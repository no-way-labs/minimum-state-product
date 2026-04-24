"""SMT cycle-existence prober.

For a multiset `ms` and a target cycle length L, encode the existence
of a good cycle (in the sense of the paper's Dijkstra-convention
candidate good cycle) as a z3 query. If SAT, extract cycle / movers /
det; if UNSAT, that length is ruled out; UNKNOWN is also possible.

Encoding.
  Variables:
    state[t, p] ∈ [0, m_p)         for t ∈ [0, L], p ∈ [0, n)
    mover[t]    ∈ [0, n)           for t ∈ [0, L)

  Constraints:
    (T)   single-processor step:
            state[t+1, p] = state[t, p]        for p ≠ mover[t]
            state[t+1, mover[t]] ≠ state[t, mover[t]]
    (C)   cycle closure:
            state[L, *] = state[0, *]
    (F)   fairness: every p appears at least once in mover[0..L)
    (D)   det consistency (the hard one):
            For all (t, t') and q ∈ [0, n):
              if (state[t, q-1], state[t, q], state[t, q+1]) =
                 (state[t', q-1], state[t', q], state[t', q+1]):
                if mover[t] = q or mover[t'] = q:
                  then mover[t] = q AND mover[t'] = q AND
                       state[t+1, q] = state[t'+1, q]
      This captures: if a context for processor q appears twice in
      the cycle, both occurrences must agree (both move with same
      output, or both silent). Mixing "mover q here" with "silent q
      there" would assign det(q, ctx) both non-stay and stay.

  Symmetry breaking:
    (SB)  mover[0] = 0 (rotate time index so processor 0 starts).

Complexity. Constraint count is O(L² · n) for (D); for L = 60, n = 10
that is ~36,000 clauses. Variables total (L+1)·n + L integers — about
700 for the same sizes.

Usage:
    python3 probe_cycle_smt.py --ms 2,2,2,2,2,2,2,2,2,2 --L-max 30
    python3 probe_cycle_smt.py --ms 2,2,2,2,2,2,2,2,2,20 --L 58 --timeout 60
"""
from __future__ import annotations
import argparse, json, os, sys, time
from itertools import product as iproduct

import z3


def build_cycle_smt(ms: tuple[int, ...], L: int, break_sym: bool = True,
                     timeout_s: float = 60.0, verbose: bool = True) -> dict:
    """Solve: ∃ good cycle on ms of length exactly L?"""
    n = len(ms)
    if L < n:
        return {"result": "unsat", "reason": f"L={L} < n={n}", "elapsed_s": 0.0}

    s = z3.Solver()
    s.set("timeout", int(timeout_s * 1000))

    # state[t, p] and mover[t]
    state = [[z3.Int(f"s_{t}_{p}") for p in range(n)] for t in range(L + 1)]
    mover = [z3.Int(f"m_{t}") for t in range(L)]

    # domain
    for t in range(L + 1):
        for p in range(n):
            s.add(state[t][p] >= 0, state[t][p] < ms[p])
    for t in range(L):
        s.add(mover[t] >= 0, mover[t] < n)

    # (T) transition
    for t in range(L):
        for p in range(n):
            # if mover[t] == p: state[t+1, p] != state[t, p]
            # else:              state[t+1, p] == state[t, p]
            s.add(z3.If(mover[t] == p,
                        state[t + 1][p] != state[t][p],
                        state[t + 1][p] == state[t][p]))

    # (C) cycle closure
    for p in range(n):
        s.add(state[L][p] == state[0][p])

    # (F) fairness
    for p in range(n):
        s.add(z3.Or([mover[t] == p for t in range(L)]))

    # (D) det consistency
    # For t < t' and every q: if ctxs match at q, enforce shared mover/output.
    for t in range(L):
        for tp in range(t + 1, L):
            for q in range(n):
                qm = (q - 1) % n
                qp = (q + 1) % n
                ctx_match = z3.And(
                    state[t][qm] == state[tp][qm],
                    state[t][q]  == state[tp][q],
                    state[t][qp] == state[tp][qp],
                )
                either_mover = z3.Or(mover[t] == q, mover[tp] == q)
                # If ctx matches and at least one is mover=q, both must be
                # mover=q with same output.
                s.add(z3.Implies(
                    z3.And(ctx_match, either_mover),
                    z3.And(mover[t] == q, mover[tp] == q,
                            state[t + 1][q] == state[tp + 1][q]),
                ))

    # (SB) symmetry break: mover[0] = 0
    if break_sym:
        s.add(mover[0] == 0)

    # Stats
    if verbose:
        print(f"  SMT: n={n} ms={list(ms)} L={L} "
              f"|vars|≈{(L+1)*n + L} timeout={timeout_s}s", flush=True)

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    out = {
        "ms": list(ms), "L": L, "result": str(result),
        "elapsed_s": round(elapsed, 2), "timeout_s": timeout_s,
    }
    if result == z3.sat:
        mdl = s.model()
        cycle = []
        movers = []
        for t in range(L):
            cfg = tuple(int(str(mdl.eval(state[t][p]))) for p in range(n))
            cycle.append(list(cfg))
            movers.append(int(str(mdl.eval(mover[t]))))
        # Build det from cycle + movers
        det = {}
        for t in range(L):
            p = movers[t]
            c = cycle[t]
            nxt_p_val = cycle[(t + 1) % L][p]
            key_mover = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            det[key_mover] = nxt_p_val
            # stay entries for non-movers
            for q in range(n):
                if q == p: continue
                key_q = (q, c[(q - 1) % n], c[q], c[(q + 1) % n])
                if key_q in det and det[key_q] != c[q]:
                    # shouldn't happen if constraints were right
                    return {**out, "error": "det inconsistency post-extract",
                            "key": list(key_q), "existing": det[key_q],
                            "new_stay": c[q]}
                det[key_q] = c[q]
        out["cycle"] = cycle
        out["movers"] = movers
        out["det_size"] = len(det)
        out["det"] = {str(k): v for k, v in det.items()}
    if verbose:
        print(f"  -> {result} ({elapsed:.2f}s)", flush=True)
    return out


def sweep_L(ms, L_min, L_max, timeout_s, verbose=True):
    """Try L from L_min to L_max until SAT or all UNSAT."""
    n = len(ms)
    records = []
    for L in range(max(L_min, n), L_max + 1):
        out = build_cycle_smt(ms, L, timeout_s=timeout_s, verbose=verbose)
        records.append(out)
        if out["result"] == "sat":
            return {"status": "found", "L": L, "records": records, **out}
        if out["result"] == "unknown":
            return {"status": "unknown_at_L", "L": L, "records": records,
                    "last": out}
    return {"status": "unsat_all", "records": records}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--ms", required=True, help="comma-separated multiset")
    p.add_argument("--L", type=int, default=0,
                   help="target cycle length (if 0, sweep L_min..L_max)")
    p.add_argument("--L-min", type=int, default=0,
                   help="min L (defaults to n)")
    p.add_argument("--L-max", type=int, default=0,
                   help="max L (defaults to 3n-2)")
    p.add_argument("--timeout", type=float, default=60.0,
                   help="per-L z3 timeout, seconds (default 60)")
    p.add_argument("--no-sym", action="store_true",
                   help="disable mover[0]=0 symmetry break")
    p.add_argument("--quiet", action="store_true")
    p.add_argument("--out", default="",
                   help="write result JSON to this path")
    args = p.parse_args()

    ms = tuple(int(x) for x in args.ms.split(","))
    n = len(ms)
    L_min = args.L_min or n
    L_max = args.L_max or (3 * n - 2)

    print("=" * 72)
    print(f"SMT cycle search: n={n} ms={list(ms)} prod={int(__import__('math').prod(ms))} "
          f"L_min={L_min} L_max={L_max}")
    print("=" * 72, flush=True)

    verbose = not args.quiet
    t0 = time.time()
    if args.L > 0:
        out = build_cycle_smt(ms, args.L, break_sym=not args.no_sym,
                               timeout_s=args.timeout, verbose=verbose)
        result = out
    else:
        result = sweep_L(ms, L_min, L_max, args.timeout, verbose=verbose)
    dt = time.time() - t0

    print()
    print(f"Total: {dt:.2f}s   status: {result.get('status', result.get('result'))}")
    if result.get("status") == "found":
        print(f"  Found cycle at L={result['L']}, "
              f"|det|={result.get('det_size')}")
        if verbose and result.get("L") <= 10:
            print("  cycle:")
            for t, cfg in enumerate(result["cycle"]):
                print(f"    t={t}: {cfg}  mover={result['movers'][t]}")

    if args.out:
        with open(args.out, "w") as f:
            json.dump(result, f, indent=2, default=str)
        print(f"  wrote {args.out}")


if __name__ == "__main__":
    main()
