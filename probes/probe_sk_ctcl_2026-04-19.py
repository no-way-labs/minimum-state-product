"""
CTCL (twist-conservation law) probe (2026-04-19 late).

After FRL-CSP was refuted, the residual analysis revealed a candidate
single invariant that subsumes DTNF's balance law in the dominant
regime and quantifies the deviation in the fusion regime:

    Σ_twists (Δi + 2·Δq)  ≟  ℓ_total   (ℓ_total = 6 in all data)

This probe computes, per record,

    S(record) := Σ_twists (signed_mod(Δi, L) + 2·signed_mod(Δq, n))
    gap       := 6 − S(record)

and reports the gap distribution, broken down by regime (dominant /
fusion / fold). The decisive data point is the fold regime: does
gap stay in a small integer set there as well?

Input : probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_ctcl_2026-04-19.json
"""
import json
from collections import Counter
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_ctcl_2026-04-19.json")


def signed_mod(x, m):
    r = x % m
    return r - m if r > m // 2 else r


def classify(dq, di):
    if dq == -1 and di >= 3:
        return ('R', di - 3)
    if dq == 2 and di <= -3:
        return ('L', (-di) - 3)
    if dq == -2 and di < 0:
        return ('F', (-di) - 3)     # fold primitive F_k
    return ('E', (dq, di))


def regime(classes):
    if all(c[0] in ('R', 'L') for c in classes):
        return 'dominant'
    if any(c[0] == 'F' for c in classes):
        return 'fold'
    # exceptions but no folds: fusion
    return 'fusion'


def main():
    data = json.loads(IN_PATH.read_text())
    records = [r for r in data['records']
               if r['min_case_C'] == 6 and len(r['c_forensics']) == 6]

    print("=" * 72)
    print("CTCL (twist-conservation law) probe")
    print("=" * 72)
    print(f"\nRecords: {len(records)}")

    by_regime = Counter()
    gap_dist = {'dominant': Counter(), 'fusion': Counter(), 'fold': Counter()}
    per_record = []

    for r in records:
        n = r['n']
        L = r['L']
        tw = sorted(r['c_forensics'], key=lambda f: f['t'])
        classes = []
        S_val = 0
        ell = 0
        for f in tw:
            dq = signed_mod(f['dq_mod_n'], n)
            di = signed_mod(f['di_mod_L'], L)
            classes.append(classify(dq, di))
            S_val += di + 2 * dq
            ell += 1    # one letter per twist edge
        reg = regime(classes)
        gap = ell - S_val
        by_regime[reg] += 1
        gap_dist[reg][gap] += 1
        per_record.append({
            'n': n, 'ms': r['ms'], 'L': L,
            'regime': reg, 'S': S_val, 'ell': ell, 'gap': gap,
            'classes': [(c[0], c[1] if not isinstance(c[1], tuple) else list(c[1])) for c in classes],
        })

    print("\nRegime counts:", dict(by_regime))

    for reg in ('dominant', 'fusion', 'fold'):
        print(f"\n--- {reg} ({by_regime[reg]} records) — gap distribution ---")
        for gap, c in sorted(gap_dist[reg].items()):
            pct = 100 * c / by_regime[reg]
            print(f"  gap = {gap:+d}:  {c:5d}  ({pct:5.1f}%)")

    # Decisive check: is fold gap set bounded?
    fold_gaps = set(gap_dist['fold'])
    fusion_gaps = set(gap_dist['fusion'])
    dominant_gaps = set(gap_dist['dominant'])
    print("\n--- Summary ---")
    print(f"  dominant gap set: {sorted(dominant_gaps)}")
    print(f"  fusion   gap set: {sorted(fusion_gaps)}")
    print(f"  fold     gap set: {sorted(fold_gaps)}")

    if dominant_gaps == {0}:
        print("  -> DTNF's balance law verified as CTCL in the dominant regime.")
    else:
        print("  -> WARNING: dominant gap ≠ {0}; CTCL formulation may be off.")

    all_gaps = dominant_gaps | fusion_gaps | fold_gaps
    if 0 in all_gaps and max(all_gaps) - min(all_gaps) <= 10:
        print(f"  -> CTCL empirically bounded: gap ∈ [{min(all_gaps)}, {max(all_gaps)}]")

    # Per-n fold gaps specifically
    fold_per_n = {}
    for rec in per_record:
        if rec['regime'] != 'fold':
            continue
        fold_per_n.setdefault(rec['n'], Counter())[rec['gap']] += 1
    print("\n--- Fold gap by n ---")
    for n in sorted(fold_per_n):
        print(f"  n={n}: {dict(fold_per_n[n])}")

    def to_j(obj):
        if isinstance(obj, dict):
            return {str(k): to_j(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [to_j(x) for x in obj]
        return obj

    out = {
        'records': len(records),
        'by_regime': dict(by_regime),
        'gap_dist': {reg: dict(gap_dist[reg]) for reg in gap_dist},
        'dominant_gap_set': sorted(dominant_gaps),
        'fusion_gap_set': sorted(fusion_gaps),
        'fold_gap_set': sorted(fold_gaps),
        'fold_gap_by_n': {n: dict(d) for n, d in fold_per_n.items()},
        'per_record': to_j(per_record),
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(out, indent=2, default=str))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
