#!/usr/bin/env python3
"""Deep-wide probe of `|SK| ≥ 2^(n-1)` (Lemma C's load-bearing inequality).

Three goals:
 (i)   At n=5..8, pin down the MIN |SK| and the record that achieves it.
       Is min |SK| ≥ 2^(n-1) at every n, or does some record violate?
 (ii)  Distribution of slack `|SK| - 2^(n-1)` at each n. Tight? Growing?
       Shrinking? Sign-flipping?
 (iii) n=9 sparse: first look across the phase transition.

Only records with cycle length L ≥ 2n+2 count (Lemma C's hypothesis).

Outputs per-n:
 - records total, min/avg/max |SK|, count below 2^(n-1), witness at min
 - slack histogram in buckets: [<0, 0, 1..3, 4..10, 11..30, 31..100, 100+]
 - top-3 tightest records (ms + L + |SK|)
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import sys, time, json

# Minimal inlined copies of compute_sk / enumerate_all_cycles /
# enumerate_multisets / value_sets (copied verbatim from
# probe_sk_abc_combined_2026-04-16.py; dashes in filename prevent direct
# import).

def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in current:
                        has_forced = True
                        break
            if not has_forced:
                victims.add(c)
        if not victims:
            break
        current -= victims
    return current


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


# ---- measurement -------------------------------------------------------

def measure(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    # Projection sizes: for each coord p, measure |π_p(SK)| =
    # # of distinct (n-1)-tuples when you drop coord p. Lemma C's
    # actual target is max_p |π_p(SK)| ≥ 2^(n-1).
    proj_sizes = []
    for p in range(n):
        proj_sizes.append(len({tuple(c[:p] + c[p+1:]) for c in SK}))
    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'VC_NG_size': len(VC_NG),
        'V_sizes': [len(v) for v in V],
        'proj_max': max(proj_sizes) if proj_sizes else 0,
        'proj_min': min(proj_sizes) if proj_sizes else 0,
    }


def bucket(slack):
    if slack < 0: return '<0_VIOLATION'
    if slack == 0: return '0_tight'
    if slack <= 3: return '1-3'
    if slack <= 10: return '4-10'
    if slack <= 30: return '11-30'
    if slack <= 100: return '31-100'
    return '100+'


def print_summary(n, recs):
    if not recs:
        print(f"\n  n={n}: NO RECORDS"); return
    bound = 2 ** (n - 1)
    sks = sorted(r['SK_size'] for r in recs)
    slack = [s - bound for s in sks]
    viol = [r for r in recs if r['SK_size'] < bound]
    tight = [r for r in recs if r['SK_size'] == bound]
    buckets = Counter(bucket(s) for s in slack)
    pmax_list = sorted(r['proj_max'] for r in recs)
    pmin_list = sorted(r['proj_min'] for r in recs)
    proj_ge = sum(1 for r in recs if r['proj_max'] >= bound)
    proj_tight = sum(1 for r in recs if r['proj_max'] == bound)
    proj_viol = [r for r in recs if r['proj_max'] < bound]
    recs_sorted = sorted(recs, key=lambda r: r['SK_size'])
    top = recs_sorted[:5]

    print(f"\n  n={n}  records={len(recs)}  bound 2^(n-1)={bound}")
    print(f"    |SK| min/avg/max:         {sks[0]} / {sum(sks)/len(sks):.1f} / {sks[-1]}")
    print(f"    slack min/avg/max:        {slack[0]} / {sum(slack)/len(slack):.1f} / {slack[-1]}")
    print(f"    |SK| < 2^(n-1):           {len(viol)}  {'<-- Lemma C VIOLATED' if viol else '(ok)'}")
    print(f"    |SK| = 2^(n-1):           {len(tight)} (tight)")
    print(f"    proj_max min/avg/max:     {pmax_list[0]} / {sum(pmax_list)/len(pmax_list):.1f} / {pmax_list[-1]}")
    print(f"    proj_min min/avg/max:     {pmin_list[0]} / {sum(pmin_list)/len(pmin_list):.1f} / {pmin_list[-1]}")
    print(f"    proj_max ≥ 2^(n-1):       {proj_ge}/{len(recs)} ({100*proj_ge/len(recs):.1f}%)")
    print(f"    proj_max = 2^(n-1):       {proj_tight}  {'<-- tight projection!' if proj_tight else ''}")
    print(f"    proj_max < 2^(n-1):       {len(proj_viol)}  {'<-- PROJECTION VIOLATED' if proj_viol else ''}")
    print(f"    slack bucket: {dict(buckets)}")
    print(f"    top-5 tightest |SK| records:")
    for r in top:
        print(f"       ms={r['ms']}  L={r['L']}  |SK|={r['SK_size']}  proj={r['proj_max']}  slack={r['SK_size']-bound}  V_sizes={r['V_sizes']}")
    if viol:
        print(f"    !! VIOLATION DETAIL (first 3):")
        for r in viol[:3]:
            print(f"       ms={r['ms']}  L={r['L']}  |SK|={r['SK_size']}  short by {bound - r['SK_size']}")


def main():
    # (n, stride, max_cycles_per_ms, time_budget, L_max)
    # Focus on n=8 full + n=9 first look. abc already covered n=5..7
    # with |SK| ≥ 2^(n-1) at 100%. New axis this run: projection sizes,
    # and n=9 (the phase transition).
    plan = [
        (8, 200, 4, 12.0, 22),   # n=8 stride-200 (~22 multisets), L up to 22
        (9, 1000, 2, 15.0, 24),  # n=9 sparse first look (~36 multisets)
    ]
    results = {}
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  Mn={Mn}  multisets total={len(multisets)}  sampled={len(sampled)}  L_max={L_max} ===", flush=True)
        t0 = time.time()
        recs = []
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                r = measure(ms, n, cycle, movers, det)
                recs.append(r)
            if (idx + 1) % max(1, len(sampled) // 8) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={len(recs)}", flush=True)
        results[n] = recs
        # Print per-n summary immediately
        print_summary(n, recs)
        # Save raw records for later analysis
        import json
        with open(f'/tmp/probes/floor_breadth_n{n}.json', 'w') as f:
            json.dump([{k: (list(v) if isinstance(v, tuple) else v)
                        for k, v in r.items()} for r in recs], f)

    # --- analysis ---
    print(f"\n{'='*78}\nSummary table\n{'='*78}")
    print(f"  {'n':>3} {'records':>8} {'bound':>6} {'min|SK|':>8} {'slack':>8} {'viol':>5} {'tight':>6}")
    for n in sorted(results):
        recs = results[n]
        if not recs: continue
        bound = 2 ** (n - 1)
        sks = sorted(r['SK_size'] for r in recs)
        viol = sum(1 for r in recs if r['SK_size'] < bound)
        tight = sum(1 for r in recs if r['SK_size'] == bound)
        print(f"  {n:>3} {len(recs):>8} {bound:>6} "
              f"{sks[0]:>8} {sks[0]-bound:>+8} {viol:>5} {tight:>6}")


if __name__ == "__main__":
    main()
