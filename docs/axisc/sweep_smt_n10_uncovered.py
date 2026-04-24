"""SMT sweep: run probe_cycle_smt on every n=10 multiset that the DFS
enumerator could not find a cycle for (the 214 budget-limited records
in axc_n10_sweep_results.json).

For each multiset:
  1. Pick one canonical dihedral ordering (sorted).
  2. Sweep L from n..L_max, accept first SAT.
  3. If SAT, run Axis-C on the extracted cycle + det.

Checkpoints incrementally to axc_n10_smt_sweep_results.json.
"""
from __future__ import annotations
import argparse, json, os, sys, time
from itertools import product as iproduct

HERE = "docs/lean_docs/paper_upgrade_3"
sys.path.insert(0, HERE)
sys.path.insert(0, "docs/lean_docs/paper_upgrade_1")
sys.path.insert(0, "docs")
sys.path.insert(0, "claude")

from probe_cycle_smt import build_cycle_smt
from probe_axis_c_forced_ng import analyze_record


def _fmt(s):
    s = int(s); h, s = divmod(s, 3600); m, s = divmod(s, 60)
    return f"{h:02d}:{m:02d}:{s:02d}"


def run_one(ms, L_min, L_max, timeout_s, verbose=True):
    """SMT-sweep one multiset; returns verdict dict."""
    n = len(ms)
    t0 = time.time()
    per_L = []
    found = None
    for L in range(max(L_min, n), L_max + 1):
        out = build_cycle_smt(ms, L, break_sym=True,
                               timeout_s=timeout_s, verbose=False)
        per_L.append({"L": L, "result": out["result"],
                      "elapsed_s": out["elapsed_s"]})
        if out["result"] == "sat":
            found = out
            break
        if out["result"] == "unknown":
            # record but continue — we want SAT if reachable at larger L
            continue
    dt = time.time() - t0
    rec = {"ms": list(ms), "product": 1, "per_L": per_L,
            "dt_total_s": round(dt, 2)}
    for m in ms: rec["product"] *= m
    if found is None:
        status = "no_cycle_all_L"
        if any(r["result"] == "unknown" for r in per_L):
            status = "unknown_some_L"
        rec["status"] = status
        return rec
    # SAT: extract + run Axis-C
    rec["status"] = "found"
    rec["L"] = found["L"]
    cycle = found["cycle"]; movers = found["movers"]
    # Parse det (same trick as probe_cycle_smt produces)
    det = {}
    for t, p in enumerate(movers):
        c = cycle[t]
        c_next = cycle[(t + 1) % len(cycle)]
        key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        det[key] = c_next[p]
        for q in range(n):
            if q == p: continue
            det[(q, c[(q - 1) % n], c[q], c[(q + 1) % n])] = c[q]
    axc_rec = {"ms": list(ms), "cycle": cycle, "movers": movers,
               "det": det, "n": n, "L": len(cycle), "id": "smt"}
    axc = analyze_record(axc_rec)
    rec["axc"] = {
        "n_ng": axc.get("n_ng"), "n_edges": axc.get("n_edges"),
        "sk_size": axc.get("sk_size"),
        "sk_nonempty": axc.get("sk_nonempty"),
        "sk_frac": axc.get("sk_frac"),
        "scc": axc.get("scc"),
    }
    rec["cycle_L"] = len(cycle)
    rec["det_size"] = len(det)
    return rec


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--in", dest="inp", default=os.path.join(
        HERE, "axc_n10_sweep_results.json"),
        help="prior sweep JSON to select uncovered multisets from")
    p.add_argument("--out", default=os.path.join(
        HERE, "axc_n10_smt_sweep_results.json"))
    p.add_argument("--L-max", type=int, default=30)
    p.add_argument("--timeout", type=float, default=90.0,
                   help="per-L z3 timeout seconds (default 90)")
    p.add_argument("--max-ms", type=int, default=0,
                   help="cap on multisets processed (0 = all uncovered)")
    p.add_argument("--resume", action="store_true",
                   help="skip multisets already in --out")
    p.add_argument("--checkpoint-every", type=int, default=3)
    args = p.parse_args()

    prior = json.load(open(args.inp))
    uncovered = [tuple(r["sorted_ms"]) for r in prior["results"]
                 if r.get("n_cycles_found", 0) == 0]
    print(f"Uncovered multisets from prior sweep: {len(uncovered)}")

    done = set()
    prior_out = {"parameters": vars(args), "results": []}
    if args.resume and os.path.exists(args.out):
        prior_out = json.load(open(args.out))
        done = {tuple(r["ms"]) for r in prior_out["results"]}
        print(f"  resuming: {len(done)} already processed")

    todo = [ms for ms in uncovered if ms not in done]
    if args.max_ms:
        todo = todo[:args.max_ms]
    print(f"  running SMT on {len(todo)} multisets, L_max={args.L_max}, "
          f"timeout={args.timeout}s")

    n = len(todo[0]) if todo else 10
    L_min = n

    totals = {"found": 0, "no_cycle_all_L": 0, "unknown_some_L": 0}
    for r in prior_out["results"]:
        totals[r.get("status", "unknown_some_L")] = \
            totals.get(r.get("status", "unknown_some_L"), 0) + 1

    t_start = time.time()
    results = list(prior_out["results"])
    for idx, ms in enumerate(todo, start=1):
        dt = time.time() - t_start
        if idx > 1:
            per_ms = dt / (idx - 1)
            eta = per_ms * (len(todo) - idx + 1)
        else:
            eta = 0
        print(f"[{idx:>3d}/{len(todo)} {100*idx/len(todo):5.1f}% "
              f"elapsed={_fmt(dt)} eta={_fmt(eta)}] "
              f"ms={list(ms)} prod={int(__import__('math').prod(ms))}",
              flush=True)
        rec = run_one(ms, L_min, args.L_max, args.timeout, verbose=False)
        totals[rec["status"]] = totals.get(rec["status"], 0) + 1
        if rec["status"] == "found":
            print(f"  FOUND L={rec['L']} sk={rec['axc']['sk_size']}/"
                  f"{rec['axc']['n_ng']} "
                  f"({rec['axc']['sk_frac']:.3f})  "
                  f"tot {rec['dt_total_s']:.1f}s", flush=True)
        else:
            print(f"  {rec['status']}  tot {rec['dt_total_s']:.1f}s",
                  flush=True)
        results.append(rec)
        if idx % args.checkpoint_every == 0 or idx == len(todo):
            prior_out["results"] = results
            prior_out["totals"] = totals
            prior_out["runtime_s"] = round(time.time() - t_start, 2)
            prior_out["in_progress"] = (idx < len(todo))
            tmp = args.out + ".tmp"
            with open(tmp, "w") as f:
                json.dump(prior_out, f, default=str)
            os.replace(tmp, args.out)
            print(f"  [checkpoint] totals={totals} written to {args.out}",
                  flush=True)

    print()
    print(f"DONE: {totals}")


if __name__ == "__main__":
    main()
