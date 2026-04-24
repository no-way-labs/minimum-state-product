"""
Exception-decomposition audit (2026-04-19).

Falsifier: do exceptional twist events decompose as short words in the
canonical generators R_k = (-1, +(3+k)) and L_k = (+2, -(3+k))?

For each distinct exceptional (Δq, Δi), enumerate all decompositions up
to length ≤ 3 with stretches k_i ∈ [0, K_MAX]. Report:
  - the minimum decomposition length (∞ if none found),
  - the set of decompositions at minimum length,
  - a cross-tab of exception type vs. simplest decomposition.

Additionally, per record with exceptional events, try to expand the
exceptional events into canonical words and test whether the expanded
record satisfies 4R + 2L (or another small multiple) with global
stretch balance Σ k_R = Σ k_L.

Input : probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_exception_decomp_2026-04-19.json
"""
import json
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_exception_decomp_2026-04-19.json")

K_MAX = 6


def signed_mod(x, m):
    r = x % m
    return r - m if r > m // 2 else r


def classify(dq, di):
    if dq == -1 and di >= 3:
        return ('R', di - 3)
    if dq == 2 and di <= -3:
        return ('L', (-di) - 3)
    return ('E', (dq, di))


def enumerate_decompositions(target_dq, target_di, max_len=3, k_max=K_MAX):
    """Return all (length, word) with word summing to (target_dq, target_di)."""
    results = []
    # length 1 — should never succeed if target is exceptional, but include for completeness
    for kind in ('R', 'L'):
        for k in range(k_max + 1):
            if kind == 'R':
                dq, di = -1, 3 + k
            else:
                dq, di = 2, -(3 + k)
            if dq == target_dq and di == target_di:
                results.append((1, ((kind, k),)))
    # length 2..max_len
    for L in range(2, max_len + 1):
        for kinds in product(['R', 'L'], repeat=L):
            for ks in product(range(k_max + 1), repeat=L):
                dq = sum(-1 if k == 'R' else 2 for k in kinds)
                di = sum((3 + ks[j]) if kinds[j] == 'R' else -(3 + ks[j])
                         for j in range(L))
                if dq == target_dq and di == target_di:
                    word = tuple((kinds[j], ks[j]) for j in range(L))
                    results.append((L, word))
    return results


def min_length_decomps(results):
    if not results:
        return (float('inf'), [])
    min_len = min(r[0] for r in results)
    return (min_len, [r[1] for r in results if r[0] == min_len])


def main():
    data = json.loads(IN_PATH.read_text())
    records = [r for r in data['records']
               if r['min_case_C'] == 6 and len(r['c_forensics']) == 6]

    print("=" * 72)
    print("Exception-decomposition audit")
    print("=" * 72)
    print(f"\nRecords: {len(records)}")

    excep_event_counts = Counter()   # (Δq, Δi) → count across all records
    records_with_excep = 0
    per_event_decomps = {}

    for r in records:
        n = r['n']
        L = r['L']
        tw = sorted(r['c_forensics'], key=lambda f: f['t'])
        has_excep = False
        for f in tw:
            dq = signed_mod(f['dq_mod_n'], n)
            di = signed_mod(f['di_mod_L'], L)
            cls = classify(dq, di)
            if cls[0] == 'E':
                excep_event_counts[(dq, di)] += 1
                has_excep = True
        if has_excep:
            records_with_excep += 1

    print(f"\nRecords with ≥1 exceptional event: {records_with_excep}")
    print(f"Total distinct exceptional event types: {len(excep_event_counts)}")

    print("\n--- Exception decomposition table ---")
    print(f"{'(Δq, Δi)':>15}  {'count':>6}  {'min_len':>8}  {'#decomps':>9}   examples")
    for (dq, di), c in excep_event_counts.most_common():
        decomps = enumerate_decompositions(dq, di, max_len=3, k_max=K_MAX)
        min_len, min_decomps = min_length_decomps(decomps)
        per_event_decomps[(dq, di)] = {
            'count': c,
            'min_len': min_len,
            'min_decomps': min_decomps,
        }
        if min_len == float('inf'):
            print(f"  ({dq:+d}, {di:+d}) {'':>5} {c:>5}  {'∞':>8}  {0:>9}   no decomposition up to length 3")
        else:
            ex = min_decomps[:3]
            ex_str = " | ".join(str(w) for w in ex)
            print(f"  ({dq:+d}, {di:+d}) {'':>5} {c:>5}  {min_len:>8}  {len(min_decomps):>9}   {ex_str}")

    # Per-record global expansion test
    print("\n--- Global expansion test ---")
    print("For each record with ≥1 exceptional event, replace each exceptional")
    print("twist by its shortest canonical decomposition (if unique), then check")
    print("whether the expanded word has form m·R + p·L with Σk_R = Σk_L and")
    print("Σ Δq = 0 overall.")
    print()

    expansion_outcomes = Counter()
    per_record_expansion = []

    for r in records:
        n = r['n']
        L = r['L']
        tw = sorted(r['c_forensics'], key=lambda f: f['t'])
        classes = []
        has_excep = False
        for f in tw:
            dq = signed_mod(f['dq_mod_n'], n)
            di = signed_mod(f['di_mod_L'], L)
            classes.append(classify(dq, di))
            if classes[-1][0] == 'E':
                has_excep = True
        if not has_excep:
            continue

        expanded = []
        unique = True
        unresolvable = False
        for c in classes:
            if c[0] in ('R', 'L'):
                expanded.append(c)
            else:
                dq, di = c[1]
                decomps = enumerate_decompositions(dq, di, max_len=3, k_max=K_MAX)
                min_len, min_decomps = min_length_decomps(decomps)
                if min_len == float('inf'):
                    unresolvable = True
                    break
                if len(min_decomps) > 1:
                    unique = False
                expanded.extend(min_decomps[0])

        if unresolvable:
            expansion_outcomes['unresolvable'] += 1
            continue

        nR = sum(1 for x in expanded if x[0] == 'R')
        nL = sum(1 for x in expanded if x[0] == 'L')
        kR = sum(x[1] for x in expanded if x[0] == 'R')
        kL = sum(x[1] for x in expanded if x[0] == 'L')
        net_dq = sum(-1 if x[0] == 'R' else 2 for x in expanded)
        balance_ok = (kR == kL)
        mR_2L_shape = (nL > 0 and nR == 2 * nL)   # m R + (m/2) L... more generally m=2p?

        tag = []
        tag.append(f"len{len(expanded)}")
        tag.append(f"R{nR}L{nL}")
        tag.append("balanced" if balance_ok else "unbalanced")
        tag.append("4R2L" if (nR, nL) == (4, 2) else ("8R4L" if (nR, nL) == (8, 4) else f"other({nR},{nL})"))
        key = tuple(tag)
        expansion_outcomes[key] += 1
        per_record_expansion.append({
            'n': n, 'L': L, 'nR': nR, 'nL': nL, 'kR': kR, 'kL': kL,
            'net_dq': net_dq, 'balance_ok': balance_ok, 'unique': unique,
        })

    for key, c in expansion_outcomes.most_common():
        print(f"  {c:5d}   {key}")

    # Balance check in expansion
    if per_record_expansion:
        balanced = sum(1 for r in per_record_expansion if r['balance_ok'])
        four_two = sum(1 for r in per_record_expansion if (r['nR'], r['nL']) == (4, 2))
        print(f"\n  Balanced (Σk_R = Σk_L): {balanced}/{len(per_record_expansion)} ({100*balanced/len(per_record_expansion):.1f}%)")
        print(f"  4R+2L after expansion:  {four_two}/{len(per_record_expansion)} ({100*four_two/len(per_record_expansion):.1f}%)")

    def to_j(obj):
        if isinstance(obj, dict):
            return {str(k): to_j(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [to_j(x) for x in obj]
        return obj

    out = {
        'records': len(records),
        'records_with_excep': records_with_excep,
        'excep_event_counts': to_j({str(k): v for k, v in excep_event_counts.items()}),
        'per_event_decomps': to_j({
            str(k): {
                'count': v['count'],
                'min_len': v['min_len'] if v['min_len'] != float('inf') else 'inf',
                'min_decomps': v['min_decomps'],
            }
            for k, v in per_event_decomps.items()
        }),
        'expansion_outcomes': to_j({str(k): v for k, v in expansion_outcomes.items()}),
        'expansion_balanced': sum(1 for r in per_record_expansion if r['balance_ok']),
        'expansion_total': len(per_record_expansion),
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(out, indent=2, default=str))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
