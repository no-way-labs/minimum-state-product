"""
Twist-word probe (2026-04-19).

Post-processes the twist-geometry JSON to build canonical cyclic words
over the 6 twist edges per record, in both t-order (base cycle
traversal) and i-order (anchor cycle-index). Asks whether the resulting
words collapse to a small finite family.

Word flavors:
  W_sign       : 6-tuple of Δq signs in {-, 0, +}
  W_signed_dq  : 6-tuple of signed Δq values (mod n → nearest representative)
  W_spacing_sign : 6-tuple of (cyclic spacing to next twist, Δq sign)
  W_full       : 6-tuple of (spacing, Δq sign, arity, sig_mult_before)

All words are canonicalized by cyclic lex-min rotation (and for i-order,
by i-sorting then applying the same canonicalization).

Input:  probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_twist_words_2026-04-19.json
"""
import json
from collections import Counter
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_twist_words_2026-04-19.json")


def signed_dq(dq_mod_n, n):
    d = dq_mod_n % n
    return d - n if d > n // 2 else d


def sign(x):
    return 0 if x == 0 else (1 if x > 0 else -1)


def canon_rotation(word):
    """Return the lex-min cyclic rotation of the tuple `word`."""
    L = len(word)
    rotations = [tuple(word[i:] + word[:i]) for i in range(L)]
    return min(rotations)


def build_words_t_order(forensics, L_base, n):
    """Build words in t-order (base-cycle traversal)."""
    twists = sorted(forensics, key=lambda f: f['t'])
    positions = [f['t'] for f in twists]
    k = len(twists)
    spacings = [(positions[(i + 1) % k] - positions[i]) % L_base for i in range(k)]

    w_sign = tuple(sign(signed_dq(f['dq_mod_n'], n)) for f in twists)
    w_signed_dq = tuple(signed_dq(f['dq_mod_n'], n) for f in twists)
    w_spacing_sign = tuple((spacings[i], w_sign[i]) for i in range(k))
    w_full = tuple(
        (spacings[i], w_sign[i], twists[i]['p_arity'], twists[i]['sig_mult_before'])
        for i in range(k)
    )
    return (
        canon_rotation(w_sign),
        canon_rotation(w_signed_dq),
        canon_rotation(w_spacing_sign),
        canon_rotation(w_full),
    )


def build_words_i_order(forensics, n):
    """Order twists by i_before (anchor index before twist)."""
    twists = sorted(forensics, key=lambda f: f['i_before'])
    k = len(twists)
    # i-ordered spacings: cyclic differences in i_before modulo L (use L from twists)
    # We use a straight sort (not cyclic) then measure gap to next.
    # The cyclic "anchor length" used for i is L_base again (cycle length).
    i_vals = [f['i_before'] for f in twists]
    # Need L_base — look up max i_before + 1 as an approximation; actually use di_mod_L.
    # Better: infer L_base from any record entry — but it's shared. Compute outside.
    w_sign = tuple(sign(signed_dq(f['dq_mod_n'], n)) for f in twists)
    w_signed_dq = tuple(signed_dq(f['dq_mod_n'], n) for f in twists)
    return (
        canon_rotation(w_sign),
        canon_rotation(w_signed_dq),
        i_vals,
    )


def summarize(counter, label, top_k=10, total=None):
    if total is None:
        total = sum(counter.values())
    print(f"  {label}: {len(counter)} distinct words, {total} records")
    for w, c in counter.most_common(top_k):
        pct = 100.0 * c / total
        print(f"    [{c:4d}  {pct:5.1f}%]  {w}")


def main():
    data = json.loads(IN_PATH.read_text())
    records = data['records']

    out = {'records_processed': len(records), 'by_n': {}}
    print("=" * 72)
    print("Twist-word probe — is the word drawn from a small template family?")
    print("=" * 72)

    by_n = {}
    for r in records:
        if r['min_case_C'] != 6:
            continue
        if len(r['c_forensics']) != 6:
            continue
        by_n.setdefault(r['n'], []).append(r)

    for n in sorted(by_n.keys()):
        recs = by_n[n]
        print(f"\n=== n = {n}  ({len(recs)} records with min_case_C = 6) ===")

        t_sign_ctr = Counter()
        t_signed_dq_ctr = Counter()
        t_spacing_sign_ctr = Counter()
        t_full_ctr = Counter()
        i_sign_ctr = Counter()
        i_signed_dq_ctr = Counter()

        for r in recs:
            ws, wsd, wss, wf = build_words_t_order(r['c_forensics'], r['L'], n)
            t_sign_ctr[ws] += 1
            t_signed_dq_ctr[wsd] += 1
            t_spacing_sign_ctr[wss] += 1
            t_full_ctr[wf] += 1

            is_w, is_sd, _ = build_words_i_order(r['c_forensics'], n)
            i_sign_ctr[is_w] += 1
            i_signed_dq_ctr[is_sd] += 1

        print("\n  --- t-order (base-cycle traversal) ---")
        summarize(t_sign_ctr, "W_sign          (just Δq signs)")
        summarize(t_signed_dq_ctr, "W_signed_dq     (signed Δq magnitudes)")
        summarize(t_spacing_sign_ctr, "W_spacing_sign  (spacing, Δq sign)")
        summarize(t_full_ctr, "W_full          (spacing, Δq sign, arity, |Σ|)")

        print("\n  --- i-order (anchor index order) ---")
        summarize(i_sign_ctr, "W_sign_i        (Δq signs, i-ordered)")
        summarize(i_signed_dq_ctr, "W_signed_dq_i   (signed Δq, i-ordered)")

        out['by_n'][n] = {
            'records': len(recs),
            't_sign_distinct': len(t_sign_ctr),
            't_sign_top5': t_sign_ctr.most_common(5),
            't_signed_dq_distinct': len(t_signed_dq_ctr),
            't_signed_dq_top5': t_signed_dq_ctr.most_common(5),
            't_spacing_sign_distinct': len(t_spacing_sign_ctr),
            't_spacing_sign_top5': t_spacing_sign_ctr.most_common(5),
            't_full_distinct': len(t_full_ctr),
            'i_sign_distinct': len(i_sign_ctr),
            'i_sign_top5': i_sign_ctr.most_common(5),
            'i_signed_dq_distinct': len(i_signed_dq_ctr),
            'i_signed_dq_top5': i_signed_dq_ctr.most_common(5),
        }

    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    # counters aren't json serializable directly — convert
    def to_jsonable(obj):
        if isinstance(obj, dict):
            return {str(k): to_jsonable(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [to_jsonable(x) for x in obj]
        return obj
    OUT_PATH.write_text(json.dumps(to_jsonable(out), indent=2))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
