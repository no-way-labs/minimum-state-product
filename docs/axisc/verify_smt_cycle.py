"""Verify that an SMT-produced cycle + movers + det is a genuine good cycle
and run Axis-C on it.

Takes the probe_cycle_smt.py result JSON, reconstructs the record, and
runs probe_axis_c_forced_ng.analyze_record to produce SK size / verdict.
"""
from __future__ import annotations
import argparse, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
for p in (HERE, os.path.join(REPO, "probes"), os.path.join(REPO, "docs")):
    if p not in sys.path:
        sys.path.insert(0, p)

from probe_axis_c_forced_ng import analyze_record


def parse_det_key(s):
    s = s.strip().lstrip("(").rstrip(")")
    return tuple(int(x.strip()) for x in s.split(","))


def verify(smt_json_path: str) -> dict:
    d = json.load(open(smt_json_path))
    ms = d["ms"]; cycle = d["cycle"]; movers = d["movers"]
    det = {parse_det_key(k): v for k, v in d["det"].items()}
    rec = {"ms": ms, "cycle": cycle, "movers": movers, "det": det,
           "id": "smt_cycle", "n": len(ms), "L": len(cycle)}
    # Sanity: cycle closure under movers + det
    n = len(ms)
    ok = True
    for t in range(len(cycle)):
        c = cycle[t]; c_next = cycle[(t + 1) % len(cycle)]
        p = movers[t]
        # one-step
        if any(c[i] != c_next[i] for i in range(n) if i != p):
            ok = False; break
        # mover changes
        if c[p] == c_next[p]:
            ok = False; break
        # det agrees
        key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        if det.get(key) != c_next[p]:
            ok = False; break
    print(f"cycle closure+det check: {'PASS' if ok else 'FAIL'}")
    print(f"n={n} L={len(cycle)} |det|={len(det)} ms={ms}")

    out = analyze_record(rec)
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--in", dest="inp", required=True,
                   help="SMT output JSON (from probe_cycle_smt.py --out)")
    args = p.parse_args()
    v = verify(args.inp)
    axc = v.get("axis_c_forced_ng") or v.get("axc") or v
    print()
    print("Axis-C verdict:")
    for k in ("axc_sk_size", "axc_sk_frac", "axc_sk_nonempty", "axc_n_ng",
              "axc_n_edges", "axc_scc"):
        if k in axc or k in v:
            val = axc.get(k, v.get(k))
            print(f"  {k}: {val}")


if __name__ == "__main__":
    main()
