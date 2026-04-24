#!/usr/bin/env python3
"""SK projection floor probe for Lemma C-weak (P1 route).

Hypothesis (P1-proj): For every fair simple closed cycle C with L >= 2n+2
on a sub-M_n multiset, there exists a coordinate p* in [n] such that the
"drop-p*" projection of SK has image size >= 2^(n-1).

If true, this gives a clean Lemma C-weak proof:
  |SK| >= |pi_{p*}(SK)| >= 2^(n-1).

Secondary hypotheses tested in the same pass:
  (H1) max_p |pi_p(SK)| >= 2^(n-1)
  (H2) |SK ∩ V-subcube| + spillover decomposition
  (H3) For every p and every v in V_p, |{c in SK : c_p = v}| >= ?
  (H4) For the "best" p, every fiber has >= 2^(n-2) — gives the stronger
       bound via summing fibers.
  (H5) |projection onto the n-1 best coords| >= 2^(n-1)

Also records the fire-count signature of each cycle, so we can see whether
projection behavior correlates with fire pattern.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys

sys.setrecursionlimit(20000)


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


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


def compute_sk(ms, n, cycle, det):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    remaining = set(non_good)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    return remaining


def fire_vector(movers, n):
    fv = [0] * n
    for p in movers:
        fv[p] += 1
    return tuple(sorted(fv, reverse=True))


def analyze_cycle(ms, n, cycle, movers, det):
    """Compute the projection-floor statistics for one cycle."""
    sk = compute_sk(ms, n, cycle, det)
    sk_size = len(sk)
    fv_list = [0] * n
    for p in movers:
        fv_list[p] += 1
    fv = tuple(sorted(fv_list, reverse=True))

    # Project SK by dropping coordinate p.
    proj_sizes = []
    for p in range(n):
        proj = set()
        for c in sk:
            proj.add(tuple(c[i] for i in range(n) if i != p))
        proj_sizes.append(len(proj))
    max_proj = max(proj_sizes) if proj_sizes else 0
    argmax_p = proj_sizes.index(max_proj) if proj_sizes else -1

    # Best 2-coord drop: project onto n-2 coords
    best_drop2 = 0
    if n >= 2:
        for p1 in range(n):
            for p2 in range(p1 + 1, n):
                proj = set()
                for c in sk:
                    proj.add(tuple(c[i] for i in range(n) if i != p1 and i != p2))
                if len(proj) > best_drop2:
                    best_drop2 = len(proj)

    # Fiber analysis: for each coordinate p and each value v, count SK configs with c[p] = v.
    # Record the min fiber size for each p.
    min_fiber_by_p = []
    max_fiber_by_p = []
    for p in range(n):
        fibers = defaultdict(int)
        for c in sk:
            fibers[c[p]] += 1
        if fibers:
            min_fiber_by_p.append(min(fibers.values()))
            max_fiber_by_p.append(max(fibers.values()))
        else:
            min_fiber_by_p.append(0)
            max_fiber_by_p.append(0)
    best_min_fiber = max(min_fiber_by_p) if min_fiber_by_p else 0
    best_min_fiber_p = min_fiber_by_p.index(best_min_fiber) if min_fiber_by_p else -1

    # Categorize: does the best-projection p have the highest fireCount, or the lowest?
    argmax_fc = fv_list[argmax_p] if argmax_p >= 0 else 0
    argmax_mf_fc = fv_list[best_min_fiber_p] if best_min_fiber_p >= 0 else 0
    max_fc = max(fv_list)
    min_fc = min(fv_list)

    return {
        'sk_size': sk_size,
        'fv': fv,
        'fv_list': tuple(fv_list),
        'max_proj': max_proj,
        'argmax_p': argmax_p,
        'argmax_fc': argmax_fc,
        'best_drop2': best_drop2,
        'best_min_fiber': best_min_fiber,
        'best_min_fiber_p': best_min_fiber_p,
        'argmax_mf_fc': argmax_mf_fc,
        'max_fc': max_fc,
        'min_fc': min_fc,
        'proj_sizes': proj_sizes,
    }


def main():
    print("=" * 80, flush=True)
    print("SK projection floor probe (Lemma C P1 route)", flush=True)
    print("  Hypothesis: max_p |proj_p(SK)| >= 2^(n-1)", flush=True)
    print("=" * 80, flush=True)

    plan = [
        (5, 1, 1500, 4.0, 15),
        (6, 8,  400, 3.0, 16),
        (7, 40, 100, 2.5, 17),
    ]

    # Collect: for each (n, L), the worst (smallest) max_proj across all cycles.
    # Also: a few histograms.
    worst_by_nL = {}  # (n, L) -> (max_proj, sk_size, fv, ms)
    records = []      # list of dicts with full stats
    # Categorization: does best-p* have max or min fire count?
    p_fc_category = Counter()

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets  L range [{2*n+2}, {L_max}] ===",
              flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                stats = analyze_cycle(ms, n, cycle, movers, det)
                sk_size = stats['sk_size']
                max_proj = stats['max_proj']
                stats['n'] = n; stats['L'] = L; stats['ms'] = ms
                records.append(stats)
                # Categorize: is argmax_p a high-fc or low-fc processor?
                if stats['argmax_fc'] == stats['max_fc']:
                    p_fc_category['argmax_proj is HIGHEST fc'] += 1
                elif stats['argmax_fc'] == stats['min_fc']:
                    p_fc_category['argmax_proj is LOWEST fc'] += 1
                else:
                    p_fc_category['argmax_proj is MIDDLE fc'] += 1
                key = (n, L)
                if key not in worst_by_nL or max_proj < worst_by_nL[key][0]:
                    worst_by_nL[key] = (max_proj, sk_size, stats['fv'], ms)
            if (idx + 1) % 20 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s  records={len(records)}",
                      flush=True)

    print(f"\n=== Projection floor analysis ===", flush=True)
    print(f"  records collected: {len(records)}", flush=True)
    print(f"\n  n  L   count  min_max_proj  2^(n-1)  slack  fv_worst", flush=True)
    violations = 0
    for (n, L) in sorted(worst_by_nL.keys()):
        mp, sk, fv, ms = worst_by_nL[(n, L)]
        target = 2 ** (n - 1)
        slack = mp - target
        cnt = sum(1 for r in records if r['n'] == n and r['L'] == L)
        flag = " !" if mp < target else ""
        print(f"  {n}  {L:2d}  {cnt:5d}  {mp:11d}  {target:6d}  {slack:+5d}  {fv}{flag}",
              flush=True)
        if mp < target:
            violations += 1

    print(f"\n  P1-proj hypothesis: {'HOLDS' if violations == 0 else f'VIOLATED ({violations} buckets)'}",
          flush=True)

    # Fiber analysis: what's the smallest "best min fiber" by (n,L)?
    print(f"\n=== Min-fiber analysis (largest min over p, v) ===", flush=True)
    print(f"  n  L   count  worst_best_mf  2^(n-2)  slack", flush=True)
    worst_mf = {}
    for r in records:
        key = (r['n'], r['L'])
        if key not in worst_mf or r['best_min_fiber'] < worst_mf[key]:
            worst_mf[key] = r['best_min_fiber']
    for (n, L) in sorted(worst_mf.keys()):
        mf = worst_mf[(n, L)]
        target = 2 ** (n - 2)
        slack = mf - target
        cnt = sum(1 for r in records if r['n'] == n and r['L'] == L)
        flag = " !" if mf < target else ""
        print(f"  {n}  {L:2d}  {cnt:5d}  {mf:13d}  {target:6d}  {slack:+5d}{flag}",
              flush=True)

    # Which p achieves argmax projection? Test fireCount correlation.
    print(f"\n=== Which p* achieves max projection? ===", flush=True)
    for cat, cnt in sorted(p_fc_category.items(), key=lambda x: -x[1]):
        pct = cnt / len(records) * 100 if records else 0
        print(f"  {cat}: {cnt} ({pct:.1f}%)", flush=True)


if __name__ == "__main__":
    main()
