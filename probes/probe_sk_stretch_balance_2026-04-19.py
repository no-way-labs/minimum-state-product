"""
Stretch-balance audit (2026-04-19).

Classify twists under the sign-law normal form:
  R_k = (Δq = -1, Δi = +(3+k))  with k ≥ 0  ("stretched retreat")
  L_k = (Δq = +2, Δi = -(3+k))  with k ≥ 0  ("stretched leap")
  others = {Δq ∈ {-2, +1, +3}, ...}  ("exceptional")

For each record with min_case_C = 6, compute:
  - (#R, #L, #excep)
  - Σ k_R, Σ k_L, stretch difference Σ k_R - Σ k_L
  - stretch total Σ k_R + Σ k_L
  - Σ Δi_twist
  - strict segment A-edge count (derived: #A = (spacing-1) - #B per segment,
    with #B reconstructed from i_before / i_after across segments)
  - closure test: does #A + 6 - 2·#L = 0 match? (see below)

Closure arithmetic (for 4R + 2L records):
  Σ Δi_twist = 4·3 + 2·(-3) + (Σ k_R - Σ k_L)
             = 6 + (Σ k_R - Σ k_L)
  #B_total (strict) = L - 6 - #A_total
  Σ Δi_twist + #B_total ≡ 0 mod L
  → #A_total = Σ k_R - Σ k_L (if m=1 branch; test empirically)

Input : probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_stretch_balance_2026-04-19.json
"""
import json
from collections import Counter, defaultdict
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_stretch_balance_2026-04-19.json")


def signed_mod(x, m):
    r = x % m
    return r - m if r > m // 2 else r


def classify(dq, di):
    """Return ('R', k), ('L', k), or ('E', (dq, di)) where k = |di|-3."""
    if dq == -1 and di > 0:
        return ('R', di - 3)
    if dq == +2 and di < 0:
        return ('L', (-di) - 3)
    return ('E', (dq, di))


def main():
    data = json.loads(IN_PATH.read_text())
    records = [r for r in data['records']
               if r['min_case_C'] == 6 and len(r['c_forensics']) == 6]

    print("=" * 72)
    print("Stretch-balance audit — do Σ k_R, Σ k_L satisfy a fixed law?")
    print("=" * 72)
    print(f"\nRecords: {len(records)}")

    counts = defaultdict(Counter)              # n → Counter of (#R, #L, #E)
    stretch_pairs_4R2L = defaultdict(Counter)  # n → Counter of (Σk_R, Σk_L)
    stretch_diff_4R2L = defaultdict(Counter)   # n → Counter of Σk_R - Σk_L
    stretch_sum_4R2L = defaultdict(Counter)    # n → Counter of Σk_R + Σk_L
    A_vs_diff = defaultdict(Counter)           # n → Counter of (#A, Σk_R - Σk_L)
    closure_match = defaultdict(lambda: Counter({'match': 0, 'miss': 0}))
    mismatch_samples = []

    excep_dq_counts = Counter()

    for r in records:
        n = r['n']
        L = r['L']
        tw = sorted(r['c_forensics'], key=lambda f: f['t'])
        classes = [classify(signed_mod(f['dq_mod_n'], n),
                            signed_mod(f['di_mod_L'], L)) for f in tw]
        nR = sum(1 for c in classes if c[0] == 'R')
        nL = sum(1 for c in classes if c[0] == 'L')
        nE = sum(1 for c in classes if c[0] == 'E')
        counts[n][(nR, nL, nE)] += 1

        for c in classes:
            if c[0] == 'E':
                excep_dq_counts[c[1]] += 1

        # Reconstruct strict-segment #B from i_before / i_after
        positions = [f['t'] for f in tw]
        i_after = [f['i_after'] for f in tw]
        i_before = [f['i_before'] for f in tw]
        spacings = [(positions[(j + 1) % 6] - positions[j]) % L for j in range(6)]
        # strict segment j runs from edge after twist j (exclusive) to twist j+1 (exclusive)
        # length = spacings[j] - 1
        # #B in segment j ≡ i_before[(j+1)%6] - i_after[j]  (mod L)
        B_segs = []
        for j in range(6):
            gap_edges = spacings[j] - 1
            delta = (i_before[(j + 1) % 6] - i_after[j]) % L
            # delta should be in [0, gap_edges]
            if delta > gap_edges:
                # wrap past L; represent as gap_edges - (L - delta) ?  (unlikely)
                # guard: if actually inconsistent, mark and skip
                B_segs.append(None)
            else:
                B_segs.append(delta)
        if None in B_segs:
            closure_match[n]['miss'] += 1
            if len(mismatch_samples) < 10:
                mismatch_samples.append({'n': n, 'L': L, 'classes': classes, 'B_segs': B_segs})
            continue

        total_B = sum(B_segs)
        total_A = (L - 6) - total_B

        # Stretch accounting on R/L classes
        if nR == 4 and nL == 2 and nE == 0:
            kR = sum(c[1] for c in classes if c[0] == 'R')
            kL = sum(c[1] for c in classes if c[0] == 'L')
            stretch_pairs_4R2L[n][(kR, kL)] += 1
            stretch_diff_4R2L[n][kR - kL] += 1
            stretch_sum_4R2L[n][kR + kL] += 1
            A_vs_diff[n][(total_A, kR - kL)] += 1

            # Predicted identity: #A = kR - kL
            if total_A == kR - kL:
                closure_match[n]['match'] += 1
            else:
                closure_match[n]['miss'] += 1

    # Report
    print("\n--- (#R, #L, #E) counts by n ---")
    for n in sorted(counts.keys()):
        total = sum(counts[n].values())
        print(f"  n={n}  ({total} records):")
        for (nR, nL, nE), c in counts[n].most_common():
            print(f"    [{c:4d}  {100*c/total:5.1f}%]  R={nR}  L={nL}  E={nE}")

    print("\n--- Exceptional Δq distribution ---")
    for (dq, di), c in excep_dq_counts.most_common(15):
        print(f"  {c:4d}  (Δq={dq:+d}, Δi={di:+d})")

    print("\n--- Closure identity test (#A ?= Σk_R - Σk_L) for 4R+2L records ---")
    for n in sorted(closure_match.keys()):
        m = closure_match[n]
        tot = m['match'] + m['miss']
        if tot == 0:
            continue
        print(f"  n={n}:  match {m['match']}/{tot}  ({100*m['match']/tot:.1f}%)   miss {m['miss']}")

    print("\n--- Stretch difference Σk_R - Σk_L distribution (4R+2L records) ---")
    for n in sorted(stretch_diff_4R2L.keys()):
        ctr = stretch_diff_4R2L[n]
        total = sum(ctr.values())
        print(f"  n={n}  ({total} records): " +
              ", ".join(f"diff={k}:{v}({100*v/total:.1f}%)" for k, v in sorted(ctr.items())))

    print("\n--- Stretch sum Σk_R + Σk_L distribution (4R+2L records) ---")
    for n in sorted(stretch_sum_4R2L.keys()):
        ctr = stretch_sum_4R2L[n]
        total = sum(ctr.values())
        print(f"  n={n}  ({total} records): " +
              ", ".join(f"sum={k}:{v}({100*v/total:.1f}%)" for k, v in sorted(ctr.items())))

    print("\n--- (Σk_R, Σk_L) joint distribution (top per n) ---")
    for n in sorted(stretch_pairs_4R2L.keys()):
        ctr = stretch_pairs_4R2L[n]
        total = sum(ctr.values())
        print(f"  n={n}  ({total} records):")
        for (kR, kL), c in ctr.most_common(10):
            print(f"    [{c:4d}  {100*c/total:5.1f}%]  (Σk_R={kR}, Σk_L={kL})  diff={kR-kL}  sum={kR+kL}")

    print("\n--- (#A_strict, Σk_R - Σk_L) cross-tab ---")
    for n in sorted(A_vs_diff.keys()):
        ctr = A_vs_diff[n]
        total = sum(ctr.values())
        print(f"  n={n}  ({total} records):")
        for (aA, diff), c in ctr.most_common(10):
            match = "✓" if aA == diff else "✗"
            print(f"    [{c:4d}  {100*c/total:5.1f}%]  #A={aA}  diff={diff}  {match}")

    def to_j(obj):
        if isinstance(obj, dict):
            return {str(k): to_j(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [to_j(x) for x in obj]
        return obj

    out = {
        'records': len(records),
        'RLE_counts': to_j({n: dict(counts[n]) for n in counts}),
        'stretch_pairs_4R2L': to_j({n: dict(stretch_pairs_4R2L[n]) for n in stretch_pairs_4R2L}),
        'stretch_diff_4R2L': to_j({n: dict(stretch_diff_4R2L[n]) for n in stretch_diff_4R2L}),
        'stretch_sum_4R2L': to_j({n: dict(stretch_sum_4R2L[n]) for n in stretch_sum_4R2L}),
        'A_vs_diff': to_j({n: dict(A_vs_diff[n]) for n in A_vs_diff}),
        'closure_match': to_j({n: dict(closure_match[n]) for n in closure_match}),
        'mismatch_samples': mismatch_samples,
        'excep_dq_counts': to_j(dict(excep_dq_counts)),
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(out, indent=2, default=str))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
