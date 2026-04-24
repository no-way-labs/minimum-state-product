"""
Twist jump-size audit (2026-04-19).

Falsifier: is |Δi_twist| = 3 universally across ALL records and ALL
twists, including the minor templates?

Also: build the local twist-type alphabet (Δq_signed, Δi_signed) and
check whether Δi_sign is determined by Δq_type.

Input : probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_twist_jumpsize_2026-04-19.json
"""
import json
from collections import Counter, defaultdict
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_twist_jumpsize_2026-04-19.json")


def signed_mod(x, m):
    r = x % m
    return r - m if r > m // 2 else r


def sign(x):
    return 0 if x == 0 else (1 if x > 0 else -1)


def canon_rotation(word):
    L = len(word)
    return min(tuple(word[i:] + word[:i]) for i in range(L))


def main():
    data = json.loads(IN_PATH.read_text())
    records = [r for r in data['records']
               if r['min_case_C'] == 6 and len(r['c_forensics']) == 6]

    print("=" * 72)
    print("Twist jump-size audit — is |Δi_twist| = 3 universal?")
    print("=" * 72)
    print(f"\nRecords: {len(records)}  (all min_case_C=6, 6-twist cycles)")

    by_n_abs_di = defaultdict(Counter)
    by_n_signed_di = defaultdict(Counter)
    by_template_abs_di = defaultdict(Counter)
    alphabet = Counter()                     # (Δq_signed, Δi_signed) global
    alphabet_by_n = defaultdict(Counter)
    dq_to_di_sign = defaultdict(Counter)     # conditional: given Δq_signed, Δi_signed?
    violators = []                            # records/twists with |Δi| ≠ 3
    violator_templates = Counter()
    total_twists = 0

    for r in records:
        n = r['n']
        L = r['L']
        # build signed Δq word (t-ordered)
        tw = sorted(r['c_forensics'], key=lambda f: f['t'])
        sign_word = tuple(sign(signed_mod(f['dq_mod_n'], n)) for f in tw)
        sign_word_canon = canon_rotation(sign_word)

        for f in tw:
            di_signed = signed_mod(f['di_mod_L'], L)
            abs_di = abs(di_signed)
            dq_signed = signed_mod(f['dq_mod_n'], n)

            by_n_abs_di[n][abs_di] += 1
            by_n_signed_di[n][di_signed] += 1
            by_template_abs_di[sign_word_canon][abs_di] += 1
            alphabet[(dq_signed, di_signed)] += 1
            alphabet_by_n[n][(dq_signed, di_signed)] += 1
            dq_to_di_sign[dq_signed][sign(di_signed)] += 1

            total_twists += 1
            if abs_di != 3:
                violators.append({
                    'n': n, 'L': L, 'template': sign_word_canon,
                    'dq_signed': dq_signed, 'di_signed': di_signed,
                    'p_arity': f['p_arity'],
                })
                violator_templates[sign_word_canon] += 1

    print(f"\nTotal twist events audited: {total_twists}")
    print(f"|Δi_twist| = 3 violations: {len(violators)}  ({100*len(violators)/total_twists:.2f}%)")

    print("\n--- |Δi_twist| distribution by n ---")
    for n in sorted(by_n_abs_di.keys()):
        ctr = by_n_abs_di[n]
        total = sum(ctr.values())
        dist = sorted(ctr.items())
        print(f"  n={n}  ({total} twists):  " + ", ".join(f"|Δi|={k}: {v} ({100*v/total:.1f}%)" for k, v in dist))

    print("\n--- Signed Δi_twist distribution by n ---")
    for n in sorted(by_n_signed_di.keys()):
        ctr = by_n_signed_di[n]
        total = sum(ctr.values())
        dist = sorted(ctr.items())
        print(f"  n={n}  ({total} twists):  " + ", ".join(f"Δi={k}: {v} ({100*v/total:.1f}%)" for k, v in dist))

    print("\n--- |Δi| distribution by template class ---")
    for tmpl, ctr in sorted(by_template_abs_di.items(), key=lambda kv: -sum(kv[1].values())):
        total = sum(ctr.values())
        dist = sorted(ctr.items())
        print(f"  template {tmpl}  ({total} twists): " +
              ", ".join(f"|Δi|={k}:{v}" for k, v in dist))

    print("\n--- Violator templates (|Δi| ≠ 3) ---")
    for tmpl, c in violator_templates.most_common():
        print(f"  {c:4d}  {tmpl}")

    print("\n--- Local twist alphabet: (Δq_signed, Δi_signed) global ---")
    print(f"  {len(alphabet)} distinct twist types")
    total_tw = sum(alphabet.values())
    for (dq, di), c in alphabet.most_common(20):
        print(f"    [{c:5d}  {100*c/total_tw:5.1f}%]  (Δq={dq:+d}, Δi={di:+d})")

    print("\n--- Conditional: P(Δi_sign | Δq_signed) ---")
    for dq in sorted(dq_to_di_sign.keys()):
        ctr = dq_to_di_sign[dq]
        tot = sum(ctr.values())
        dist = sorted(ctr.items())
        print(f"  Δq={dq:+d}  ({tot} twists):  " +
              ", ".join(f"sign(Δi)={s:+d}: {v} ({100*v/tot:.1f}%)" for s, v in dist))

    out = {
        'total_twists': total_twists,
        'violators_count': len(violators),
        'violator_fraction': len(violators) / total_twists,
        'abs_di_by_n': {str(n): dict(by_n_abs_di[n]) for n in by_n_abs_di},
        'signed_di_by_n': {str(n): {str(k): v for k, v in by_n_signed_di[n].items()} for n in by_n_signed_di},
        'alphabet': [
            {'dq_signed': dq, 'di_signed': di, 'count': c}
            for (dq, di), c in alphabet.most_common()
        ],
        'alphabet_size': len(alphabet),
        'conditional_di_sign_given_dq': {
            str(dq): {str(s): v for s, v in ctr.items()}
            for dq, ctr in dq_to_di_sign.items()
        },
        'violators_sample': violators[:50],
        'violator_templates': [
            {'template': list(t), 'count': c} for t, c in violator_templates.most_common()
        ],
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(out, indent=2, default=str))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
