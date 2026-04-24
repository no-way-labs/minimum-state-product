"""
CSP(FRL-balance) feasibility search (2026-04-19).

For each fusion-regime record (one with ≥1 exceptional twist, all exceptions
decomposable in R_k / L_k words of length ≤ 3), test whether there exists a
*choice* of decomposition per exceptional twist such that the expanded
threading satisfies the stretch-balance law

    Σ k_R  =  Σ k_L .

This is the decisive probe for FRL-CSP: DTNF holds forward only in the pure
regime. If every fusion record admits a balance-consistent expansion, the
fusion regime is reducible to DTNF via a finite CSP and Theorem B is on
firm empirical footing. If even one record has no balanced expansion, FRL-CSP
is already refuted and Theorem B must be reformulated.

Input : probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_frl_csp_2026-04-19.json
"""
import json
from collections import Counter
from itertools import product
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_frl_csp_2026-04-19.json")

K_MAX = 6           # per-letter stretch range [0..K_MAX]
MAX_WORD_LEN = 6    # length of decomposition words considered


def signed_mod(x, m):
    r = x % m
    return r - m if r > m // 2 else r


def classify(dq, di):
    """Classify a single twist event as R_k, L_k, or E(xceptional)."""
    if dq == -1 and di >= 3:
        return ('R', di - 3)
    if dq == 2 and di <= -3:
        return ('L', (-di) - 3)
    return ('E', (dq, di))


def enumerate_decompositions(target_dq, target_di, max_len=MAX_WORD_LEN, k_max=K_MAX):
    """Enumerate all R/L words of length ≤ max_len summing to (target_dq, target_di).

    Each word is a tuple of (kind, k) pairs. Empty word = length 0 (not used).
    """
    results = []
    for L in range(1, max_len + 1):
        for kinds in product(['R', 'L'], repeat=L):
            dq_fixed = sum(-1 if k == 'R' else 2 for k in kinds)
            if dq_fixed != target_dq:
                continue
            # di = sum( (3+ks[j]) * (+1 if R else -1) )
            # di - sum(±3) = sum(±ks[j])
            base_di = sum((3 if kinds[j] == 'R' else -3) for j in range(L))
            residual = target_di - base_di
            # residual = sum( ks[j] * (+1 if R else -1) ), ks[j] ∈ [0..k_max]
            for ks in product(range(k_max + 1), repeat=L):
                s = sum(ks[j] * (1 if kinds[j] == 'R' else -1) for j in range(L))
                if s == residual:
                    word = tuple((kinds[j], ks[j]) for j in range(L))
                    results.append(word)
    return results


def word_totals(word):
    """Return (nR, nL, kR, kL, dq, di) for a word of (kind, k) pairs."""
    nR = sum(1 for x in word if x[0] == 'R')
    nL = sum(1 for x in word if x[0] == 'L')
    kR = sum(x[1] for x in word if x[0] == 'R')
    kL = sum(x[1] for x in word if x[0] == 'L')
    dq = sum(-1 if x[0] == 'R' else 2 for x in word)
    di = sum((3 + x[1]) if x[0] == 'R' else -(3 + x[1]) for x in word)
    return nR, nL, kR, kL, dq, di


def record_expansions(record):
    """
    For a single record, classify its 6 twist events and enumerate the
    choice set per exceptional event. Returns:

        native_kR, native_kL : stretch totals of native R/L events
        excep_choices        : list[ list[word] ], one choice list per excep
        native_nR, native_nL, excep_types : diagnostics
        unresolvable         : True if any exception has no length-≤3 decomposition
                               (→ fold regime, not fusion; excluded from CSP)
    """
    n = record['n']
    L = record['L']
    tw = sorted(record['c_forensics'], key=lambda f: f['t'])
    native_nR = native_nL = 0
    native_kR = native_kL = 0
    excep_choices = []
    excep_types = []
    unresolvable = False
    for f in tw:
        dq = signed_mod(f['dq_mod_n'], n)
        di = signed_mod(f['di_mod_L'], L)
        cls = classify(dq, di)
        if cls[0] == 'R':
            native_nR += 1
            native_kR += cls[1]
        elif cls[0] == 'L':
            native_nL += 1
            native_kL += cls[1]
        else:
            decomps = enumerate_decompositions(dq, di)
            if not decomps:
                unresolvable = True
                break
            excep_choices.append(decomps)
            excep_types.append((dq, di))
    return {
        'native_nR': native_nR,
        'native_nL': native_nL,
        'native_kR': native_kR,
        'native_kL': native_kL,
        'excep_choices': excep_choices,
        'excep_types': excep_types,
        'unresolvable': unresolvable,
    }


def csp_feasible(data):
    """
    Check whether any combination of decomposition choices produces
    Σ k_R = Σ k_L globally.

    Prune per choice list: for each exceptional event build the residual
    (kR_choice - kL_choice) set, then ask whether sums from all events
    can hit the target residual -(native_kR - native_kL).
    """
    target_residual = data['native_kL'] - data['native_kR']   # we want Σ(kR-kL) total = 0
    choice_residuals = []   # per exception, set of (kR - kL, kR+kL, nR+nL)
    choice_best = []        # one witness per residual
    for choices in data['excep_choices']:
        per_choice = {}
        for word in choices:
            nR, nL, kR, kL, dq, di = word_totals(word)
            resid = kR - kL
            # keep the shortest witness per residual
            if resid not in per_choice or len(word) < len(per_choice[resid]):
                per_choice[resid] = word
        choice_residuals.append(sorted(per_choice.keys()))
        choice_best.append(per_choice)

    # Subset-sum search: Σ resid_i = target_residual
    # (native terms contribute kR - kL = native_kR - native_kL;
    #  we want total = 0, so excep sum = target_residual)
    # excep event residuals can be negative — use dict-based DP
    reachable = {0: []}    # residual -> list of chosen words (one per excep so far)
    for i, resids in enumerate(choice_residuals):
        new_reach = {}
        for r_prev, witnesses in reachable.items():
            for r_add in resids:
                r_new = r_prev + r_add
                if r_new not in new_reach:
                    new_reach[r_new] = witnesses + [choice_best[i][r_add]]
        reachable = new_reach
    feasible = target_residual in reachable
    witness = reachable.get(target_residual)
    return feasible, witness, choice_residuals


def main():
    data = json.loads(IN_PATH.read_text())
    records = [r for r in data['records']
               if r['min_case_C'] == 6 and len(r['c_forensics']) == 6]

    print("=" * 72)
    print("CSP(FRL-balance) feasibility search")
    print("=" * 72)
    print(f"\nTotal (min_case_C=6) records: {len(records)}")

    # Classify records into three regimes first
    by_regime = Counter()
    n_by_regime = {'dominant': Counter(), 'fusion': Counter(), 'fold': Counter()}
    fusion_records = []
    fold_records = []
    dominant_records = []

    for r in records:
        expn = record_expansions(r)
        n = r['n']
        if expn['unresolvable']:
            by_regime['fold'] += 1
            n_by_regime['fold'][n] += 1
            fold_records.append(r)
        elif not expn['excep_choices']:
            by_regime['dominant'] += 1
            n_by_regime['dominant'][n] += 1
            dominant_records.append((r, expn))
        else:
            by_regime['fusion'] += 1
            n_by_regime['fusion'][n] += 1
            fusion_records.append((r, expn))

    total = sum(by_regime.values())
    print("\nRegime distribution:")
    for regime in ('dominant', 'fusion', 'fold'):
        c = by_regime[regime]
        pct = 100 * c / total if total else 0
        print(f"  {regime:>8}: {c:4d} ({pct:5.1f}%)  by n: {dict(n_by_regime[regime])}")

    # Sanity: dominant records should trivially satisfy Σk_R = Σk_L
    dom_balanced = sum(1 for _, e in dominant_records if e['native_kR'] == e['native_kL'])
    print(f"\nDominant balance check: {dom_balanced}/{len(dominant_records)} "
          f"({100*dom_balanced/max(1,len(dominant_records)):.1f}%)")

    # CSP on fusion records
    print("\n--- CSP feasibility on fusion records ---")
    feasible_count = 0
    infeasible_count = 0
    per_record = []
    for r, expn in fusion_records:
        feasible, witness, resids = csp_feasible(expn)
        if feasible:
            feasible_count += 1
        else:
            infeasible_count += 1
        per_record.append({
            'n': r['n'],
            'ms': r['ms'],
            'L': r['L'],
            'native_nR': expn['native_nR'],
            'native_nL': expn['native_nL'],
            'native_kR': expn['native_kR'],
            'native_kL': expn['native_kL'],
            'excep_types': expn['excep_types'],
            'choice_residuals': resids,
            'feasible': feasible,
            'witness_lens': [len(w) for w in witness] if witness else None,
        })

    print(f"\nFusion records: {len(fusion_records)}")
    print(f"  Feasible    (∃ choice, Σk_R=Σk_L): {feasible_count}")
    print(f"  Infeasible  (∄ choice, Σk_R=Σk_L): {infeasible_count}")

    # Per-n breakdown
    per_n = {}
    for rec in per_record:
        n = rec['n']
        per_n.setdefault(n, {'feas': 0, 'infeas': 0})
        if rec['feasible']:
            per_n[n]['feas'] += 1
        else:
            per_n[n]['infeas'] += 1
    print("\nPer-n breakdown:")
    for n in sorted(per_n):
        print(f"  n={n}: feasible={per_n[n]['feas']}, infeasible={per_n[n]['infeas']}")

    # Show infeasible records if any
    if infeasible_count > 0:
        print("\nInfeasible records (first 10):")
        shown = 0
        for rec in per_record:
            if rec['feasible']:
                continue
            print(f"  n={rec['n']}, ms={rec['ms']}, L={rec['L']}, "
                  f"native R{rec['native_nR']}L{rec['native_nL']} "
                  f"kR={rec['native_kR']} kL={rec['native_kL']}, "
                  f"excep={rec['excep_types']}, residuals={rec['choice_residuals']}")
            shown += 1
            if shown >= 10:
                break
    else:
        print("\n*** FRL-CSP empirically corroborated: all fusion records feasible. ***")

    # Witness stats
    # Structural residual analysis: per event type, what arithmetic
    # progression do the achievable residuals form as word length grows?
    excep_residual_sets = {}
    for rec in per_record:
        for et, resids in zip(rec['excep_types'], rec['choice_residuals']):
            key = tuple(et)
            s = excep_residual_sets.setdefault(key, set())
            s.update(resids)
    print("\n--- Structural residual sets per exception type ---")
    for et, rs in sorted(excep_residual_sets.items()):
        rs_sorted = sorted(rs)
        mn, mx = min(rs), max(rs)
        mod3 = {r % 3 for r in rs}
        print(f"  {et}: residuals={rs_sorted}   min={mn}  max={mx}  mod3={mod3}")

    if feasible_count > 0:
        wit_lens = [tuple(rec['witness_lens']) for rec in per_record
                    if rec['feasible'] and rec['witness_lens'] is not None]
        wit_counter = Counter(wit_lens)
        print("\nWitness-length patterns (top 10):")
        for pat, c in wit_counter.most_common(10):
            print(f"  {pat}: {c}")

    def to_j(obj):
        if isinstance(obj, dict):
            return {str(k): to_j(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [to_j(x) for x in obj]
        return obj

    out = {
        'total_records': len(records),
        'regime_counts': dict(by_regime),
        'regime_by_n': {k: dict(v) for k, v in n_by_regime.items()},
        'dominant_balanced': dom_balanced,
        'dominant_total': len(dominant_records),
        'fusion_feasible': feasible_count,
        'fusion_infeasible': infeasible_count,
        'fusion_total': len(fusion_records),
        'fold_total': len(fold_records),
        'per_fusion_record': to_j(per_record),
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(out, indent=2, default=str))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
