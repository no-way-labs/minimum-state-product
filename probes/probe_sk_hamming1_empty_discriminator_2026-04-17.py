#!/usr/bin/env python3
"""Probe A — Hamming-1 empty-vs-nonempty discriminator for SK.

The main theorem needs (SK gc).Nonempty (≥1), NOT the floor |SK| ≥ 2^(n-1).
We have prior data (Exploration 6, probe_sk_hamming_radius_2026-04-17.py)
showing the ratio |peel(N_1 ∩ VC_NG)|/2^(n-1) falls to 0.44 at n=9 —
never tabulated as zero/nonzero.

This probe:
  1. Enumerates good cycles at n ∈ {5,6,7,8,9,10} across multiple sub-sharp ms.
  2. For each cycle C: computes peel(N_1(C) ∩ VC_NG) and tests empty-vs-nonempty.
  3. If nonempty, captures the lex-first survivor config and reports its
     structural signature (position, value, valueSet status, forced move shape).
  4. Aggregates structural signatures across all cycles.

Lifts infrastructure from:
  - probe_sk_hamming_radius_2026-04-17.py (cycle DFS, peel, build_structures)
  - probe_sk_peel_n1_structure_2026-04-16.py (N_1 ∩ VC_NG construction)

Outputs:
  - Aggregate report to stdout.
  - JSON dump of raw records to ./sk_hamming1_discriminator_out/records.json
  - CSV summary to ./sk_hamming1_discriminator_out/summary.csv
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import json, csv, os, sys, time
sys.setrecursionlimit(100000)


# --------- M_n sharp / sub-sharp ---------

def m_n_sharp(n):
    # Sub-sharp M_n value (all ms below are strictly sub-sharp).
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


# --------- Cycle enumeration (lifted from hamming_radius probe) ---------

def enumerate_cycles_from(ms, n, L_min, L_max, time_budget, max_cycles, start_config):
    found = []
    seen = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            if L < L_min:
                return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]
            Sp = config[p]
            Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced is not None and forced != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]
                    Si = config[i]
                    Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False
                        break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config)
                nc[p] = new_val
                nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    dfs(start_config, start_config, {}, [start_config], [])
    return found


def enumerate_cycles_multistart(ms, n, L_min, L_max, time_budget, max_cycles):
    """Try several starts (including all-zeros and diagonal) to find up to max_cycles."""
    starts = [tuple([0] * n)]
    # Add a diagonal start: alternate 0s and max of each
    starts.append(tuple(((i % 2) and (ms[i] - 1)) or 0 for i in range(n)))
    # Add low-value starts varying position
    for p in range(n):
        s = [0] * n
        s[p] = 1 if ms[p] >= 2 else 0
        starts.append(tuple(s))
    found = []
    seen_norm = set()
    t0 = time.time()
    per_start_budget = max(1.0, time_budget / max(1, len(starts)))
    for s in starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        budget = min(per_start_budget, time_budget - (time.time() - t0))
        cs = enumerate_cycles_from(ms, n, L_min, L_max, budget,
                                    max_cycles - len(found), s)
        for cycle, movers, det in cs:
            L = len(movers)
            norm = min(tuple(cycle[i:L] + cycle[:i]) for i in range(L))
            if norm in seen_norm:
                continue
            seen_norm.add(norm)
            found.append((cycle, movers, det))
            if len(found) >= max_cycles:
                break
    return found


# --------- Peel / VC_NG construction (lifted) ---------

def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def build_N1_and_peel(ms, n, cycle, det):
    """Return N1 ∩ VC_NG, adjacency (within N1), peel set, first-survivor provenance map."""
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # N_1(C) ∩ VC_NG via single-flip within valueSet(q)
    N1 = set()
    provenance = defaultdict(list)  # c -> list of (q, v, i) representations
    for i, c in enumerate(cycle):
        for q in range(n):
            for v in sorted(V[q]):
                if v == c[q]:
                    continue
                nc = list(c)
                nc[q] = v
                nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
                    provenance[nc].append((q, v, i))

    # Adjacency in N1 via forced-moves (det)
    adj = defaultdict(list)
    for c in N1:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c)
                nc[p] = val
                nc = tuple(nc)
                if nc in N1:
                    adj[c].append(nc)

    # Peel: iteratively remove sinks (configs with no out-neighbor in the set)
    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove:
            break
        cur -= to_remove
    peel_set = cur

    return N1, adj, peel_set, provenance, V, move_entries, cycle_set


def classify_survivor(c, provenance_entries, V, move_entries, adj, cycle_set, n, ms):
    """For a survivor c, pick its canonical (q, v, i) representation and classify.

    Returns a dict with: q, v, i, ms_q, is_binary, is_ternary, is_plus_q (non-binary),
    value_in_valueSet (always True here since we restricted to V[q]),
    num_forced_out, forced_fires_at (the position p that fires in N1-succ adj[c][0]).
    """
    # pick lex-first (q, v, i) — deterministic
    q, v, i = sorted(provenance_entries)[0]
    out_adj = adj.get(c, [])
    # inspect forced-out position
    succ_p = None
    if out_adj:
        s = out_adj[0]
        succ_p = next(idx for idx in range(n) if s[idx] != c[idx])
    return {
        'q': q,
        'v': v,
        'i_cycle_pos': i,
        'ms_q': ms[q],
        'is_binary_q': ms[q] == 2,
        'is_ternary_q': ms[q] == 3,
        'num_adj_in_N1': len(out_adj),
        'succ_fire_pos': succ_p,
        'succ_fire_at_q': succ_p == q if succ_p is not None else None,
        'succ_fire_in_q_nbhd':
            succ_p in {(q - 1) % n, q, (q + 1) % n} if succ_p is not None else None,
    }


# --------- Multiset enumeration ---------

def enumerate_multisets_subsharp(n, max_product, cap=8):
    """Enumerate tuples ms with strictly increasing values at length n, non-decreasing,
    product < max_product, each m_i ≥ 2. Returns a short prioritized list."""
    out = []

    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        lo = prefix[-1] if prefix else 2
        for m in range(lo, max_product + 1):
            new_prod = prod * m
            min_rem = 2 ** (n - i - 1)
            if new_prod * min_rem >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()

    rec(0, [], 1)
    # Prefer lower-product, more binary. Non-decreasing ms is canonical.
    out.sort(key=lambda t: (sum(1 for m in t if m == 2) * -1,
                             -1 * sum(1 for m in t if m == 3),
                             sum(t)))
    return out[:cap]


# --------- Main ---------

def run_one(n, ms, L_min, L_max, time_budget, max_cycles):
    cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                          time_budget=time_budget,
                                          max_cycles=max_cycles)
    records = []
    for cycle, movers, det in cycles:
        L = len(movers)
        N1, adj, peel_set, provenance, V, move_entries, cycle_set = build_N1_and_peel(
            ms, n, cycle, det)
        rec = {
            'n': n,
            'ms': list(ms),
            'L': L,
            'N1_size': len(N1),
            'peel_size': len(peel_set),
            'peel_empty': len(peel_set) == 0,
            'pow_bound': 2 ** (n - 1),
            'ratio_peel_over_pow': (len(peel_set) / (2 ** (n - 1)))
                                    if 2 ** (n - 1) > 0 else 0.0,
            'survivor': None,
        }
        if peel_set:
            # Pick lex-first survivor
            first = sorted(peel_set)[0]
            sig = classify_survivor(first, provenance[first], V, move_entries,
                                     adj, cycle_set, n, ms)
            sig['config'] = list(first)
            rec['survivor'] = sig
        records.append(rec)
    return records


def main():
    out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           'sk_hamming1_discriminator_out')
    os.makedirs(out_dir, exist_ok=True)

    # Plan: (n, time_budget per ms, max_cycles per ms, L_max, ms list)
    # ms picked from validated sub-sharp families in probe_sk_hamming_radius_2026-04-17.py,
    # extended with 1-2 additional sub-sharp variants per n. L_min = 2n+2 to stay above
    # the Lemma A minimum (where peel(N_1) saturates trivially).
    plans = [
        (5, 15.0, 8, 13, [(2,2,2,3,3), (2,2,3,3,3), (2,2,2,3,4)]),
        (6, 20.0, 8, 15, [(2,2,2,3,3,3), (2,2,3,2,3,3), (2,2,2,2,3,3)]),
        (7, 30.0, 6, 17, [(2,2,2,3,3,3,3), (2,2,3,2,3,3,3), (2,2,2,2,3,3,3)]),
        (8, 45.0, 5, 19, [(2,2,2,3,3,3,3,3), (2,2,3,2,3,3,3,3), (2,2,2,2,3,3,3,3)]),
        (9, 60.0, 4, 22, [(2,2,2,3,3,3,3,3,3), (2,2,3,2,3,3,3,3,3), (2,2,2,2,3,3,3,3,3)]),
        (10, 300.0, 3, 24, [(2,2,3,2,3,3,3,3,3,3), (2,3,2,3,2,3,3,3,3,3), (2,2,2,3,3,3,3,3,3,3)]),
    ]

    all_records = []
    t_start = time.time()
    for n, tb, mc, L_max, picked in plans:
        Mn = m_n_sharp(n)
        # filter any ms that is not actually sub-sharp
        picked = [ms for ms in picked if (
            __import__('math').prod(ms) < Mn
        )]
        print(f"\n=== n={n}  M_n={Mn}  picked={picked}", flush=True)
        for ms in picked:
            # n=10 hard cap: if wall since t_start > 90*60, bail
            if time.time() - t_start > 90 * 60:
                print("  [hard wall-time cap reached; stopping enumeration]", flush=True)
                break
            t0 = time.time()
            recs = run_one(n, ms, L_min=2 * n + 2, L_max=L_max,
                           time_budget=tb, max_cycles=mc)
            dt = time.time() - t0
            if not recs:
                print(f"  ms={ms}  no cycles found in {dt:.1f}s", flush=True)
                continue
            n_empty = sum(1 for r in recs if r['peel_empty'])
            print(f"  ms={ms}  {len(recs)} cycles  empty={n_empty}  "
                  f"peel sizes={[r['peel_size'] for r in recs]}  dt={dt:.1f}s",
                  flush=True)
            all_records.extend(recs)

    # --- Save raw JSON + summary CSV ---
    json_path = os.path.join(out_dir, 'records.json')
    with open(json_path, 'w') as f:
        json.dump(all_records, f, indent=2)

    csv_path = os.path.join(out_dir, 'summary.csv')
    with open(csv_path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['n', 'ms', 'L', 'N1_size', 'peel_size', 'peel_empty',
                    'pow_bound', 'ratio',
                    'surv_q', 'surv_v', 'surv_i', 'surv_ms_q', 'surv_is_binary',
                    'surv_num_adj', 'surv_succ_fire_pos', 'surv_succ_at_q',
                    'surv_succ_in_q_nbhd', 'surv_config'])
        for r in all_records:
            s = r['survivor'] or {}
            w.writerow([r['n'], r['ms'], r['L'], r['N1_size'], r['peel_size'],
                        r['peel_empty'], r['pow_bound'],
                        f"{r['ratio_peel_over_pow']:.3f}",
                        s.get('q'), s.get('v'), s.get('i_cycle_pos'),
                        s.get('ms_q'), s.get('is_binary_q'),
                        s.get('num_adj_in_N1'), s.get('succ_fire_pos'),
                        s.get('succ_fire_at_q'), s.get('succ_fire_in_q_nbhd'),
                        s.get('config')])

    # --- Aggregate report ---
    print("\n" + "=" * 80)
    print("SUMMARY — empty vs nonempty")
    print("=" * 80)
    by_n = defaultdict(list)
    for r in all_records:
        by_n[r['n']].append(r)
    total = 0
    total_empty = 0
    for n in sorted(by_n):
        recs = by_n[n]
        n_empty = sum(1 for r in recs if r['peel_empty'])
        total += len(recs)
        total_empty += n_empty
        print(f"  n={n:2d}  {len(recs):4d} cycles  empty_peel={n_empty:4d}")
        # breakdown per ms
        per_ms = defaultdict(list)
        for r in recs:
            per_ms[tuple(r['ms'])].append(r)
        for ms, rs in per_ms.items():
            e = sum(1 for r in rs if r['peel_empty'])
            sizes = [r['peel_size'] for r in rs]
            print(f"    ms={ms}  {len(rs)} cycles  empty={e}  sizes={sizes}")
    print(f"\n  TOTAL {total} cycles, {total_empty} with empty peel(N_1 ∩ VC_NG).")

    # --- Survivor signature aggregation (only for non-empty) ---
    sigs = [r['survivor'] for r in all_records if r['survivor']]
    if sigs:
        print("\n" + "=" * 80)
        print("SURVIVOR STRUCTURAL SIGNATURE (lex-first survivor)")
        print("=" * 80)
        nb = sum(1 for s in sigs if s['is_binary_q'])
        nt = sum(1 for s in sigs if s['is_ternary_q'])
        nother = len(sigs) - nb - nt
        print(f"  q-type: binary={nb}/{len(sigs)}  ternary={nt}/{len(sigs)}  "
              f"other={nother}/{len(sigs)}")

        # q-position distribution by n (fraction at q=0 or q=n-1)
        by_n_sigs = defaultdict(list)
        for r in all_records:
            if r['survivor']:
                by_n_sigs[r['n']].append(r['survivor'])
        for n in sorted(by_n_sigs):
            qs = Counter(s['q'] for s in by_n_sigs[n])
            print(f"  n={n}  q distribution: {dict(sorted(qs.items()))}")

        # succ fire pos distribution
        scnt = Counter()
        for s in sigs:
            sp = s.get('succ_fire_pos')
            q = s.get('q')
            if sp is None:
                scnt['no_succ'] += 1
            elif sp == q:
                scnt['fires_at_q'] += 1
            elif sp in {(q - 1) % 20, (q + 1) % 20}:  # approx; real computed per record
                scnt['fires_adj_q'] += 1
            else:
                scnt['fires_far'] += 1
        # Accurate neighbor count (using recorded flag):
        at_q = sum(1 for s in sigs if s.get('succ_fire_at_q'))
        in_nbhd = sum(1 for s in sigs if s.get('succ_fire_in_q_nbhd'))
        no_succ = sum(1 for s in sigs if s.get('num_adj_in_N1') == 0)
        print(f"  succ-fire relative to q: at_q={at_q}/{len(sigs)}  "
              f"in_q_nbhd={in_nbhd}/{len(sigs)}  no_succ={no_succ}/{len(sigs)}")

        # Number of adj-in-N1 distribution
        nadj = Counter(s['num_adj_in_N1'] for s in sigs)
        print(f"  |N1-out-adj| distribution: {dict(sorted(nadj.items()))}")

        # v vs c_i[q] delta: flip-value's position in valueSet (min / max?)
        # Can't reconstruct without V — skip aggregate; per-record in CSV.

    print(f"\n  raw JSON: {json_path}")
    print(f"  summary CSV: {csv_path}")


if __name__ == "__main__":
    main()
