"""
Twist-gap probe (2026-04-19).

Post-processes r4b_twist_geometry JSON to characterize the gap pattern
between the 6 twists of a min closed threading. Two flavors:

  G_t : cyclic t-gaps in base-cycle traversal order
        = lengths of strict segments between consecutive twists,
          summing to L.
  G_i : cyclic i-gaps with twists sorted by i_before,
        cyclic differences in i_before mod L (the anchor index at
        the moment of twist).

Each flavor is canonicalized by lex-min cyclic rotation.

Separately, we also emit combined "schedule words":
  S_t = (gap, Δq_sign) per twist in t-order
  S_i = (gap, Δq_sign) per twist in i-order

If the gap pattern also collapses to a tiny family, the "closed threading
exists" target shrinks to finite dispatch.

Input : probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_twist_gaps_2026-04-19.json
"""
import json
from collections import Counter
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_twist_gaps_2026-04-19.json")


def signed_dq(dq_mod_n, n):
    d = dq_mod_n % n
    return d - n if d > n // 2 else d


def sign(x):
    return 0 if x == 0 else (1 if x > 0 else -1)


def canon_rotation(word):
    L = len(word)
    return min(tuple(word[i:] + word[:i]) for i in range(L))


def t_order_gaps(forensics, L_base):
    tw = sorted(forensics, key=lambda f: f['t'])
    k = len(tw)
    pos = [f['t'] for f in tw]
    gaps = [(pos[(j + 1) % k] - pos[j]) % L_base for j in range(k)]
    return tw, gaps


def i_order_gaps(forensics, L_base):
    tw = sorted(forensics, key=lambda f: f['i_before'])
    k = len(tw)
    ivals = [f['i_before'] for f in tw]
    gaps = [(ivals[(j + 1) % k] - ivals[j]) % L_base for j in range(k)]
    return tw, gaps


def summarize(counter, label, top_k=10):
    total = sum(counter.values())
    print(f"  {label}: {len(counter)} distinct, {total} records")
    for w, c in counter.most_common(top_k):
        pct = 100.0 * c / total
        print(f"    [{c:4d}  {pct:5.1f}%]  {w}")


def main():
    data = json.loads(IN_PATH.read_text())
    records = data['records']

    out = {'by_n': {}}
    print("=" * 72)
    print("Twist-gap probe — does the gap pattern between twists collapse?")
    print("=" * 72)

    by_n = {}
    for r in records:
        if r['min_case_C'] != 6 or len(r['c_forensics']) != 6:
            continue
        by_n.setdefault(r['n'], []).append(r)

    for n in sorted(by_n.keys()):
        recs = by_n[n]
        print(f"\n=== n={n}  ({len(recs)} records) ===")

        Gt = Counter()
        Gi = Counter()
        St = Counter()
        Si = Counter()
        TwGap_t = Counter()  # (i-jump at twist, strict-segment after) in t-order
        Ls_by_record = Counter()

        for r in recs:
            L_base = r['L']
            Ls_by_record[L_base] += 1
            tw_t, gaps_t = t_order_gaps(r['c_forensics'], L_base)
            tw_i, gaps_i = i_order_gaps(r['c_forensics'], L_base)

            Gt[canon_rotation(tuple(gaps_t))] += 1
            Gi[canon_rotation(tuple(gaps_i))] += 1

            # schedule words
            sched_t = tuple(
                (gaps_t[j], sign(signed_dq(tw_t[j]['dq_mod_n'], n)))
                for j in range(6)
            )
            sched_i = tuple(
                (gaps_i[j], sign(signed_dq(tw_i[j]['dq_mod_n'], n)))
                for j in range(6)
            )
            St[canon_rotation(sched_t)] += 1
            Si[canon_rotation(sched_i)] += 1

            # (Δi at twist, strict segment to next) pairs in t-order
            twg = tuple(
                (tw_t[j]['di_mod_L'], gaps_t[j]) for j in range(6)
            )
            TwGap_t[canon_rotation(twg)] += 1

        print(f"\n  L distribution among records: {dict(Ls_by_record)}")

        print("\n  --- Gap patterns ---")
        summarize(Gt, "G_t  (strict-segment lengths, t-order cyclic)")
        summarize(Gi, "G_i  (i_before gaps, i-order cyclic)")

        print("\n  --- Schedule words (gap, Δq sign) ---")
        summarize(St, "S_t  (gap, Δq sign) t-order")
        summarize(Si, "S_i  (gap, Δq sign) i-order")

        print("\n  --- Twist Δi × strict-segment in t-order ---")
        summarize(TwGap_t, "(Δi_twist, strict-gap) t-order", top_k=6)

        # Are S_i words partitioned by Δq-word class?
        # Count per (Δq-sign-class, gap-word)
        cross = Counter()
        for r in recs:
            L_base = r['L']
            tw_i, gaps_i = i_order_gaps(r['c_forensics'], L_base)
            sig_word = canon_rotation(tuple(
                sign(signed_dq(f['dq_mod_n'], n)) for f in tw_i
            ))
            gap_word = canon_rotation(tuple(gaps_i))
            cross[(sig_word, gap_word)] += 1

        print("\n  --- Cross: (i-order sign-word × i-order gap-word) ---")
        summarize(cross, "(sign,gap) i-ordered", top_k=10)

        out['by_n'][n] = {
            'records': len(recs),
            'G_t_distinct': len(Gt),
            'G_t_top5': Gt.most_common(5),
            'G_i_distinct': len(Gi),
            'G_i_top5': Gi.most_common(5),
            'S_i_distinct': len(Si),
            'S_i_top5': Si.most_common(5),
            'cross_distinct': len(cross),
            'cross_top10': cross.most_common(10),
        }

    def to_jsonable(obj):
        if isinstance(obj, dict):
            return {str(k): to_jsonable(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [to_jsonable(x) for x in obj]
        return obj
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(to_jsonable(out), indent=2))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
