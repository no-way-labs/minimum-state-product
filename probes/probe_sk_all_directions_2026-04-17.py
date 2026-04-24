#!/usr/bin/env python3
"""All three remaining attack directions for the peel-induction inductive step.

(β) weighted potential: Φ_p(S) = |π_p(S)| + cascade term. Want monotone under peel.
(δ) recursive chain-to-C: from each sink x, follow forced edges. Measure chain length,
    terminal location (C or dead-end). If chains always end in C with bounded length,
    we can charge σ_p via chain-endpoints.
(ε) layer-size / cascade-density: relate σ_p(k) to |X_k| and peel depth K.

Tested at n=7,8,9.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time, sys
sys.setrecursionlimit(100000)


def enumerate_cycles_from(ms, n, L_min, L_max, time_budget, max_cycles, start_config):
    found = []; seen = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    dfs(start_config, start_config, {}, [start_config], [])
    return found


def build_peel(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    all_targets = defaultdict(list)
    adj_ng = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                all_targets[c].append(nc)
                if nc in ng_set: adj_ng[c].append(nc)

    remaining = set(non_good)
    peel_layer = {}; layers = []
    step = 0
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj_ng.get(c, []))}
        if not sinks: break
        for s in sinks: peel_layer[s] = step
        layers.append(sinks)
        remaining -= sinks
        step += 1
    return {
        'ng_set': ng_set, 'cycle_set': cycle_set, 'V_sorted': V_sorted,
        'all_targets': all_targets, 'adj_ng': adj_ng,
        'peel_layer': peel_layer, 'layers': layers, 'SK': remaining,
    }


def direction_delta_recursive_chain(data, n):
    """(δ) Recursive charging: follow forced edges until reach C or dead-end.

    Record: max chain length, fraction terminating in C, fraction dead-end.
    For each layer k, pick canonical target: first forced edge, follow through layers.
    """
    layers = data['layers']; peel_layer = data['peel_layer']
    all_targets = data['all_targets']; cycle_set = data['cycle_set']

    chain_stats = []  # (from_layer, chain_len, terminal_type)
    for k, X_k in enumerate(layers):
        for x in X_k:
            # follow forced-target chain (greedy: first target)
            cur = x; chain_len = 0
            seen = {cur}
            terminal = None
            for _ in range(2 * len(peel_layer) + 10):
                targets = all_targets.get(cur, [])
                if not targets:
                    terminal = 'dead'; break
                # prefer target in C, else lowest-layer target
                in_C = [t for t in targets if t in cycle_set]
                if in_C:
                    terminal = 'C'; chain_len += 1; break
                next_t = min(targets, key=lambda t: peel_layer.get(t, -1))
                if next_t in seen:
                    terminal = 'loop'; break
                seen.add(next_t); cur = next_t; chain_len += 1
            else:
                terminal = 'timeout'
            chain_stats.append((k, chain_len, terminal))

    by_terminal = Counter(t for _,_,t in chain_stats)
    if chain_stats:
        max_len = max(c for _,c,_ in chain_stats)
        avg_len = sum(c for _,c,_ in chain_stats) / len(chain_stats)
    else:
        max_len = 0; avg_len = 0.0
    return {'by_terminal': by_terminal, 'max_chain': max_len, 'avg_chain': avg_len,
            'total': len(chain_stats)}


def direction_epsilon_layer_sizes(data, n):
    """(ε) Layer sizes: |X_k|, K=# layers, σ_p per layer for each p."""
    layers = data['layers']
    K = len(layers)
    layer_sizes = [len(X) for X in layers]
    ng_set = data['ng_set']
    # σ_p(k) per position per layer
    sigma = [[0]*K for _ in range(n)]
    S_k = set(ng_set)
    for k, X_k in enumerate(layers):
        for p in range(n):
            fiber = defaultdict(int)
            for c in S_k:
                b = tuple(c[i] for i in range(n) if i != p)
                fiber[b] += 1
            for x in X_k:
                b = tuple(x[i] for i in range(n) if i != p)
                if fiber[b] == 1: sigma[p][k] += 1
        S_k -= X_k
    return {'K': K, 'layer_sizes': layer_sizes, 'sigma_per_p': sigma}


def direction_beta_potential(data, n, bound):
    """(β) Weighted potential Φ_p(S) = |π_p(S)| + small-fiber-count.

    Try: Φ_p(S) = |π_p(S)| + #(b : |fiber(b)| ≥ 2 in S).
    Check if Φ_p is monotonic under peel.

    Actually try several candidates.
    """
    layers = data['layers']; ng_set = data['ng_set']
    S_k = set(ng_set)
    traj = []
    for k in range(len(layers) + 1):
        row = {'|S|': len(S_k)}
        for p in range(n):
            fiber = defaultdict(int)
            for c in S_k:
                b = tuple(c[i] for i in range(n) if i != p)
                fiber[b] += 1
            pi = len(fiber)
            multi = sum(1 for v in fiber.values() if v >= 2)
            heavy = sum(1 for v in fiber.values() if v >= 3)
            row[f'p{p}_pi'] = pi
            row[f'p{p}_multi'] = multi
            row[f'p{p}_heavy'] = heavy
        traj.append(row)
        if k < len(layers): S_k -= layers[k]

    # Check several candidate Φ for monotonicity
    candidates = ['pi', 'multi', 'heavy', 'pi+multi', 'pi+heavy', 'pi-multi', 'pi-heavy']
    results = {}
    for p in range(n):
        for cand in candidates:
            series = []
            for row in traj:
                pi = row[f'p{p}_pi']; mu = row[f'p{p}_multi']; he = row[f'p{p}_heavy']
                if cand == 'pi': v = pi
                elif cand == 'multi': v = mu
                elif cand == 'heavy': v = he
                elif cand == 'pi+multi': v = pi + mu
                elif cand == 'pi+heavy': v = pi + he
                elif cand == 'pi-multi': v = pi - mu
                elif cand == 'pi-heavy': v = pi - he
                series.append(v)
            # monotone non-increasing?
            monotone = all(series[i] >= series[i+1] for i in range(len(series)-1))
            # stays above bound?
            above = all(v >= bound for v in series)
            results[(p, cand)] = {'series': series, 'monotone': monotone, 'above_bound': above,
                                  'final': series[-1]}
    return results


def main():
    print("=" * 100)
    print("ALL DIRECTIONS (β, δ, ε) for peel-induction inductive step")
    print("=" * 100)
    cases = [
        (7, (2,2,2,3,3,3,3), 17, 35.0),
        (8, (2,2,2,3,3,3,3,3), 19, 50.0),
        (9, (2,2,3,2,3,3,3,3,3), 22, 60.0),
    ]
    for n, ms, L_max, tb in cases:
        bound = 2**(n-1)
        print(f"\n{'='*80}")
        print(f"n={n} ms={ms} bound={bound}")
        print(f"{'='*80}")
        cycles = enumerate_cycles_from(ms, n, L_min=2*n+2, L_max=L_max,
                                       time_budget=tb, max_cycles=1,
                                       start_config=tuple([0]*n))
        if not cycles: print("  no cycles"); continue
        cycle, movers, det = cycles[0]
        print(f"  L={len(cycle)}")
        data = build_peel(ms, n, cycle, det)
        print(f"  |VC_NG|={len(data['ng_set'])} |SK|={len(data['SK'])} K={len(data['layers'])}")

        # (δ) recursive chain
        print("\n  (δ) RECURSIVE CHAIN:")
        dres = direction_delta_recursive_chain(data, n)
        print(f"    total chains = {dres['total']}")
        print(f"    terminals: {dict(dres['by_terminal'])}")
        print(f"    chain length: max={dres['max_chain']}, avg={dres['avg_chain']:.2f}")

        # (ε) layer sizes
        print("\n  (ε) LAYER SIZES:")
        eres = direction_epsilon_layer_sizes(data, n)
        print(f"    K={eres['K']} layer_sizes={eres['layer_sizes']}")
        # Check σ_p(k) ≤ |X_k| (trivially true) and σ_p(k) vs layer-decay
        for p in range(n):
            sp = eres['sigma_per_p'][p]
            tot = sum(sp)
            print(f"    p={p}: σ_p per layer = {sp}, total={tot}")

        # (β) potential
        print("\n  (β) POTENTIAL:")
        bres = direction_beta_potential(data, n, bound)
        # Find candidates that are (monotone AND above_bound) for at least one p
        found_any = False
        for p in range(n):
            winners = [cand for cand in ['pi','multi','heavy','pi+multi','pi+heavy','pi-multi','pi-heavy']
                       if bres[(p,cand)]['monotone'] and bres[(p,cand)]['above_bound']]
            if winners:
                found_any = True
                print(f"    p={p} monotone&above: {winners}")
                for w in winners[:3]:
                    s = bres[(p,w)]['series']
                    print(f"      Φ({w}): start={s[0]} end={s[-1]}")
        if not found_any:
            # show pi-series and pi-multi for p=0
            for p in [0, n//2, n-1]:
                pi_s = bres[(p,'pi')]['series']
                pm_s = bres[(p,'pi-multi')]['series']
                print(f"    p={p} π series: {pi_s[:5]}...{pi_s[-3:]}")
                print(f"    p={p} π-multi: {pm_s[:5]}...{pm_s[-3:]}")


if __name__ == "__main__":
    main()
