"""§1.8 SMT exhaustive relaxed-convention search at n = 5 (and n = 6
for small ms).

Encodes the five relaxed-convention validity properties (liveness, mutex
on good, closure, convergence, fairness — connectedness dropped) as
first-order z3 constraints over:

  f[p, l, s, r]       — rule-table entry for processor p with local
                          context (l, s, r). Domain: Fin(m_p).
  good[c]             — whether config c is in the designer's good set.
  rank[c]             — integer rank for the convergence well-ordering
                          on bad configs; ∈ [0, |configs|).
  rank_p[c]           — per-processor rank for fairness (one copy per p).

Target per call: one specific ms at one specific n. Result: z3 SAT/UNSAT.
UNSAT at sub-threshold ⇒ M_n^rel > product(ms) on this ms (no relaxed-
valid completion of any rule table exists).

Invocation:
    python3 smt_relaxed_n5_n6.py --ms 2,2,2,2,2
    python3 smt_relaxed_n5_n6.py --ms 2,2,2,2,3

Scaling note: z3 search time grows fast with |ms|. n=5 all-binary has
~170 decision vars + ~500 constraints; n=6 all-binary has more. n=5
with one m=3 should also be tractable. n=6 may need a tighter encoding.
"""
from __future__ import annotations
import argparse
import sys
import time
from itertools import product as iproduct
from typing import List, Tuple

import z3


def build_and_solve(ms: Tuple[int, ...], time_limit_s: float = 300.0,
                     verbose: bool = True, sym_break: bool = False) -> dict:
    n = len(ms)
    configs = list(iproduct(*[range(m) for m in ms]))
    N = len(configs)
    cfg_idx = {c: i for i, c in enumerate(configs)}

    # -- Decision variables --
    # f[p, l, s, r] ∈ Fin(m_p)
    f = {}
    for p in range(n):
        for l in range(ms[(p - 1) % n]):
            for s in range(ms[p]):
                for r in range(ms[(p + 1) % n]):
                    f[p, l, s, r] = z3.Int(f"f_{p}_{l}_{s}_{r}")

    good = [z3.Bool(f"good_{i}") for i in range(N)]
    rank = [z3.Int(f"rank_{i}") for i in range(N)]
    # Per-processor fairness rank
    rankp = {p: [z3.Int(f"rankp_{p}_{i}") for i in range(N)] for p in range(n)}

    s = z3.Solver()
    s.set("timeout", int(time_limit_s * 1000))

    # f[...] ∈ [0, m_p)
    for (p, l, sv, r), var in f.items():
        s.add(var >= 0, var < ms[p])

    # rank[i] ∈ [0, N)
    for i in range(N):
        s.add(rank[i] >= 0, rank[i] < N)
        for p in range(n):
            s.add(rankp[p][i] >= 0, rankp[p][i] < N)

    # -- Helpers: priv_p(c), move_p(c) (symbolic in f) --
    def priv_p(c, p):
        """z3 bool: 'processor p is privileged at config c'."""
        l, sv, r = c[(p - 1) % n], c[p], c[(p + 1) % n]
        return f[p, l, sv, r] != sv

    def fired_p(c, p, v):
        """z3 bool: 'processor p's move at c produces value v' (v ≠ c[p])."""
        l, sv, r = c[(p - 1) % n], c[p], c[(p + 1) % n]
        return f[p, l, sv, r] == v

    def move_p_v(c, p, v):
        """Return the config that results from processor p writing value v at c."""
        return tuple(v if i == p else c[i] for i in range(n))

    # -- Property 1: Liveness (∀ c: ∃ p: priv_p(c)) --
    for c in configs:
        s.add(z3.Or([priv_p(c, p) for p in range(n)]))

    # -- Property 2: Mutual exclusion on good (∀ good c: |priv set| = 1) --
    # at most one priv, given at least one by liveness
    for c in configs:
        i = cfg_idx[c]
        # No two distinct processors both privileged
        for p in range(n):
            for q in range(p + 1, n):
                s.add(z3.Implies(
                    good[i],
                    z3.Not(z3.And(priv_p(c, p), priv_p(c, q))),
                ))

    # -- At least one good config exists --
    if sym_break:
        # WLOG under per-processor value-swap action: the origin config
        # (0, ..., 0) is good. This collapses the value-swap group orbit
        # of the good set to a canonical representative.
        zero_idx = cfg_idx[tuple(0 for _ in range(n))]
        s.add(good[zero_idx])
        # WLOG under cyclic rotation of processor indices: the unique
        # mover at origin (exists by liveness + mutex-on-good + good[0])
        # is processor 0. Encode by: every p > 0 stays at origin.
        for p in range(1, n):
            s.add(f[p, 0, 0, 0] == 0)
        # WLOG under value-swap at position 0: the move at origin sends
        # processor 0 to value 1 (not 2, 3, ...). For binary m_0 = 2
        # this is forced anyway; for larger m_0 this is a real break.
        s.add(f[0, 0, 0, 0] == 1)
    else:
        s.add(z3.Or(good))

    # -- Property 3: Closure --
    # good[c] AND priv_p(c) AND f[p,...] = v (for v ≠ c[p]) ⇒ good[move_p_v(c)]
    for c in configs:
        i = cfg_idx[c]
        for p in range(n):
            l, sv, r = c[(p - 1) % n], c[p], c[(p + 1) % n]
            for v in range(ms[p]):
                if v == sv:  # stay — no move
                    continue
                c_next = move_p_v(c, p, v)
                j = cfg_idx[c_next]
                s.add(z3.Implies(
                    z3.And(good[i], f[p, l, sv, r] == v),
                    good[j],
                ))

    # -- Property 4: Convergence --
    # ∀ c: NOT good[c] AND priv_p(c) ⇒ if move destination is bad, rank strictly decreases
    # (This forces the functional graph on bad to be acyclic.)
    for c in configs:
        i = cfg_idx[c]
        for p in range(n):
            l, sv, r = c[(p - 1) % n], c[p], c[(p + 1) % n]
            for v in range(ms[p]):
                if v == sv:
                    continue
                c_next = move_p_v(c, p, v)
                j = cfg_idx[c_next]
                # If c is bad, p fires at c, and successor c_next is also bad, rank must decrease
                s.add(z3.Implies(
                    z3.And(z3.Not(good[i]),
                           f[p, l, sv, r] == v,
                           z3.Not(good[j])),
                    rank[j] < rank[i],
                ))

    # -- Property 5: Fairness (per-processor rank on good) --
    # For each processor q: every good c reaches a config with mover = q along succ.
    # Encoding: for each c ∈ good, let mover(c) be the unique i with priv_i(c).
    # If mover(c) = q, rankp_q[c] = 0 (fine).
    # If mover(c) ≠ q, rankp_q[c] > 0, and rankp_q[succ(c)] < rankp_q[c].
    for c in configs:
        i = cfg_idx[c]
        for q in range(n):
            # Case A: some p ≠ q fires at c; follow succ, rank strictly decreases
            for p in range(n):
                if p == q:
                    continue
                l, sv, r = c[(p - 1) % n], c[p], c[(p + 1) % n]
                for v in range(ms[p]):
                    if v == sv:
                        continue
                    c_next = move_p_v(c, p, v)
                    j = cfg_idx[c_next]
                    s.add(z3.Implies(
                        z3.And(good[i], f[p, l, sv, r] == v),
                        rankp[q][j] < rankp[q][i],
                    ))
            # Case B: if mover(c) = q, rankp_q[c] may be 0
            # (no constraint forced; rankp_q[c] still lives in [0, N))

    # -- Solve --
    if verbose:
        print(f"SMT setup: n={n} ms={list(ms)} N={N} "
              f"|f|={len(f)} total_vars={len(f) + N + N + n*N}", flush=True)
        print(f"  attempting solve with time limit {time_limit_s}s ...",
              flush=True)
    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    if verbose:
        print(f"  result: {result} ({elapsed:.1f}s)", flush=True)
    out = {
        "n": n, "ms": list(ms), "product": int(1),
        "N_configs": N,
        "n_f_vars": len(f),
        "n_total_vars": len(f) + 2 * N + n * N,
        "result": str(result),
        "elapsed_s": round(elapsed, 2),
        "timeout_s": time_limit_s,
    }
    prod = 1
    for m in ms:
        prod *= m
    out["product"] = prod
    if result == z3.sat:
        mdl = s.model()
        # Extract f as a rule table
        f_table = {}
        for (p, l, sv, r), var in f.items():
            val = mdl.eval(var)
            f_table[(p, l, sv, r)] = val.as_long() if hasattr(val, "as_long") else int(str(val))
        good_set = [i for i in range(N) if z3.is_true(mdl.eval(good[i]))]
        out["f_table"] = {f"{k}": v for k, v in f_table.items()}
        out["good_indices"] = good_set
        out["good_configs"] = [list(configs[i]) for i in good_set]
    return out


def verify_with_relaxed_verifier(ms, f_table):
    """Post-hoc check: hand f_table to relaxed_verifier.verify_relaxed."""
    import os, sys
    HERE = os.path.dirname(os.path.abspath(__file__))
    REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
    for p in (HERE, os.path.join(REPO, "probes")):
        if p not in sys.path:
            sys.path.insert(0, p)
    from relaxed_verifier import verify_relaxed

    n = len(ms)
    def make_f(p):
        def f(L, S, R, pp=p):
            return f_table.get((pp, L, S, R), S)
        return f
    fs = [make_f(p) for p in range(n)]
    return verify_relaxed(ms, fs, verbose=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ms", default="2,2,2,2,2",
                        help="comma-separated ms (default 2,2,2,2,2)")
    parser.add_argument("--timeout", type=float, default=300.0,
                        help="z3 timeout in seconds (default 300)")
    parser.add_argument("--verify", action="store_true",
                        help="if SAT, run relaxed_verifier on the returned f_table")
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--sym-break", action="store_true",
                        help="WLOG symmetry break: origin is good, mover "
                             "at origin is proc 0, output is value 1")
    args = parser.parse_args()

    ms = tuple(int(x) for x in args.ms.split(","))
    prod = 1
    for m in ms:
        prod *= m
    n = len(ms)
    M_n_connected = {3: 8, 4: 24, 5: 96, 6: 288, 7: 864, 8: 2592, 9: 8748}
    M_n = M_n_connected.get(n, None)

    print("=" * 72)
    print(f"SMT relaxed-convention search at n = {n}  ms = {list(ms)}  "
          f"product = {prod}")
    if M_n is not None:
        print(f"  connected-model M_n = {M_n};  "
              f"sub-threshold? {prod < M_n}")
    print("=" * 72, flush=True)

    out = build_and_solve(ms, time_limit_s=args.timeout,
                           verbose=not args.quiet,
                           sym_break=args.sym_break)
    print(f"\nVerdict: {out['result']}  ({out['elapsed_s']}s)")
    if out["result"] == "unsat":
        print(f"  → No relaxed-valid completion of any rule table at "
              f"ms={list(ms)}. M_{n}^rel > {prod} on this multiset.")
    elif out["result"] == "sat":
        print(f"  → SAT: z3 found a candidate. {len(out.get('good_configs', []))} "
              "good configs.")
        if args.verify:
            print(f"  running relaxed_verifier.verify_relaxed post-hoc ...")
            # reconstruct f_table with tuple keys
            f_table = {eval(k) if isinstance(k, str) and k.startswith("(") else k: v
                       for k, v in out["f_table"].items()}
            v = verify_with_relaxed_verifier(ms, f_table)
            print(f"  relaxed_verifier: valid={v.get('valid')} "
                  f"reason={v.get('reason', '-')}")
            out["relaxed_verifier"] = v
    else:
        print(f"  → z3 unknown within timeout. Raise --timeout or tighten encoding.")

    # Suppress large fields if --quiet
    if args.quiet and "f_table" in out:
        out["f_table"] = f"<suppressed, {len(out['f_table'])} entries>"
        out["good_configs"] = f"<suppressed, {len(out['good_configs'])} configs>"
        out["good_indices"] = f"<suppressed, {len(out['good_indices'])} indices>"


if __name__ == "__main__":
    main()
