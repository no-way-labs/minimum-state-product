#!/usr/bin/env python3
"""n=8 3CB failure analysis with exhaustive construction search."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'docs'))

from itertools import product as cartesian
from collections import defaultdict, Counter
from verifier import all_configs as gen_configs, apply_move, privileged_set

from ra_3cb_transition import (
    make_fs_from_tables, good_targeting_completion,
    build_bounce_cycle, build_mixed_sweep_cycle, cyclic_orders,
)
from clb_inherent_cycles import find_sccs

ms = [2, 2, 2, 3, 3, 3, 3, 4]
n = 8
mid = 1
product = 2592
configs = list(gen_configs(ms))
print(f'n=8, ms={ms}, product={product}, total={len(configs)}')
print(f'Threshold: 4*3^6 = {4*3**6}, sub-threshold: {product < 4*3**6}')

best_info = None
best_bad_scc = float('inf')
n_tried = 0
n_valid = 0

# Try bounce cycles with all starting points and directions
for start in range(n):
    for direction in [1, -1]:
        base = []
        for i in range(n):
            base.append((start + direction * i) % n)
        for i in range(n-2, 0, -1):
            base.append((start + direction * i) % n)
        cycle, movers = build_bounce_cycle(ms, base)
        if cycle is None:
            continue
        n_tried += 1
        result = good_targeting_completion(ms, cycle)
        if result is None:
            continue
        vr = result['verify']
        if vr['valid']:
            n_valid += 1
            print(f'VALID via bounce! start={start}, dir={direction}')
            continue

        tables = result['tables']
        fs = make_fs_from_tables(tables)
        priv_map = {}
        for c in configs:
            priv_map[c] = privileged_set(c, fs, ms)

        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        succ = {}
        for c in single_priv:
            i = priv_map[c][0]
            s = apply_move(c, i, fs, ms)
            succ[c] = (s, i)

        good_cands = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_remove = {c for c in good_cands if succ[c][0] not in good_cands}
            if to_remove:
                good_cands -= to_remove
                changed = True

        visited = set()
        all_procs = set(range(n))
        for c0 in good_cands:
            if c0 in visited:
                continue
            path = []
            path_set = set()
            node = c0
            while node not in visited and node not in path_set:
                path.append(node)
                path_set.add(node)
                node = succ[node][0]
            if node in path_set:
                cy = path[path.index(node):]
                cy_movers = {succ[c][1] for c in cy}
                if cy_movers == all_procs:
                    good_set = set(cy)
                    bad_local = set(configs) - good_set
                    bad_adj = defaultdict(list)
                    for c in bad_local:
                        for i in priv_map[c]:
                            s = apply_move(c, i, fs, ms)
                            if s in bad_local:
                                bad_adj[c].append(s)
                    sccs = find_sccs(dict(bad_adj))
                    scc_total = sum(len(s) for s in sccs)
                    if scc_total < best_bad_scc:
                        best_bad_scc = scc_total
                        best_info = {
                            'cycle_len': len(cy), 'bad': len(bad_local),
                            'n_sccs': len(sccs), 'recurrent_bad': scc_total,
                            'cycle': cy, 'succ': succ, 'priv_map': priv_map,
                            'fs': fs, 'source': f'bounce start={start} dir={direction}'
                        }
            visited.update(path)

# Also try sweep orders
for order in list(cyclic_orders(n))[:16]:
    for t3 in [1, 2]:
        for t4 in [1, 2, 3]:
            targets = {}
            for p in range(n):
                if ms[p] == 2:
                    targets[p] = 1
                elif ms[p] == 3:
                    targets[p] = t3
                else:
                    targets[p] = t4
            for rs in [True, False]:
                cycle = build_mixed_sweep_cycle(ms, order, targets, rs)
                if cycle is None:
                    continue
                n_tried += 1
                result = good_targeting_completion(ms, cycle)
                if result is None:
                    continue
                vr = result['verify']
                if vr['valid']:
                    n_valid += 1
                    print(f'VALID sweep! order={order}')
                    continue

                tables = result['tables']
                fs = make_fs_from_tables(tables)
                priv_map = {}
                for c in configs:
                    priv_map[c] = privileged_set(c, fs, ms)

                single_priv = {c for c in configs if len(priv_map[c]) == 1}
                succ = {}
                for c in single_priv:
                    i = priv_map[c][0]
                    s = apply_move(c, i, fs, ms)
                    succ[c] = (s, i)

                good_cands = set(single_priv)
                ch = True
                while ch:
                    ch = False
                    to_remove = {c for c in good_cands if succ[c][0] not in good_cands}
                    if to_remove:
                        good_cands -= to_remove
                        ch = True

                visited = set()
                all_procs = set(range(n))
                for c0 in good_cands:
                    if c0 in visited:
                        continue
                    path = []
                    path_set = set()
                    node = c0
                    while node not in visited and node not in path_set:
                        path.append(node)
                        path_set.add(node)
                        node = succ[node][0]
                    if node in path_set:
                        cy = path[path.index(node):]
                        cy_movers = {succ[c][1] for c in cy}
                        if cy_movers == all_procs:
                            good_set = set(cy)
                            bad_local = set(configs) - good_set
                            bad_adj = defaultdict(list)
                            for c in bad_local:
                                for i in priv_map[c]:
                                    s = apply_move(c, i, fs, ms)
                                    if s in bad_local:
                                        bad_adj[c].append(s)
                            sccs = find_sccs(dict(bad_adj))
                            scc_total = sum(len(s) for s in sccs)
                            if scc_total < best_bad_scc:
                                best_bad_scc = scc_total
                                best_info = {
                                    'cycle_len': len(cy), 'bad': len(bad_local),
                                    'n_sccs': len(sccs), 'recurrent_bad': scc_total,
                                    'cycle': cy, 'succ': succ, 'priv_map': priv_map,
                                    'fs': fs, 'source': f'sweep order={order}'
                                }
                    visited.update(path)

print(f'\nTried {n_tried} constructions, {n_valid} valid')

if best_info:
    bi = best_info
    print(f'\nBest failed attempt ({bi["source"]}):')
    print(f'  Good cycle length: {bi["cycle_len"]}')
    print(f'  Bad configs: {bi["bad"]}')
    print(f'  Bad SCCs: {bi["n_sccs"]}, recurrent bad: {bi["recurrent_bad"]}')

    cy = bi['cycle']
    succ = bi['succ']
    all_8 = [(L, S, R) for L in range(2) for S in range(2) for R in range(2)]
    mover_ctxs = set()
    nonmover_ctxs = set()
    mover_count = Counter()
    for c in cy:
        _, mover = succ[c]
        L = c[(mid-1)%n]
        S = c[mid]
        R = c[(mid+1)%n]
        ctx = (L, S, R)
        if mover == mid:
            mover_ctxs.add(ctx)
            mover_count[ctx] += 1
        else:
            nonmover_ctxs.add(ctx)

    print(f'  Mover contexts at mid: {len(mover_ctxs)}/8 = {sorted(mover_ctxs)}')
    print(f'  Non-mover contexts at mid: {len(nonmover_ctxs)}/8')
    print(f'  Overlap: {len(mover_ctxs & nonmover_ctxs)}')

    # SCC context distribution
    priv_map = bi['priv_map']
    fs = bi['fs']
    good_set = set(cy)
    bad_configs = [c for c in configs if c not in good_set]
    bad_set = set(bad_configs)
    bad_adj = defaultdict(list)
    for c in bad_configs:
        for i in priv_map[c]:
            s = apply_move(c, i, fs, ms)
            if s in bad_set:
                bad_adj[c].append(s)
    sccs = find_sccs(dict(bad_adj))
    scc_members = set()
    for s in sccs:
        scc_members.update(s)

    ctx_in_scc = Counter()
    for c in scc_members:
        ctx = (c[(mid-1)%n], c[mid], c[(mid+1)%n])
        ctx_in_scc[ctx] += 1

    other_product = product // 8
    print(f'\n  Context distribution in recurrent bad:')
    for ctx in sorted(all_8):
        cnt = ctx_in_scc[ctx]
        print(f'    {ctx}: {cnt}/{other_product} ({cnt/other_product*100:.1f}%)')

    bottleneck = bi['bad'] / (bi['cycle_len'] * len(mover_ctxs)) if mover_ctxs else float('inf')
    print(f'\n  Bottleneck ratio: {bottleneck:.2f}')

    # Also analyze: for each binary proc (0,1,2), how many contexts are used as mover?
    print(f'\n  All 3CB proc mover context counts:')
    for bp in [0, 1, 2]:
        bp_actual = bp  # for ms=(2,2,2,...)
        mc = set()
        for c in cy:
            _, mover = succ[c]
            if mover == bp_actual:
                L = c[(bp_actual-1)%n]
                S = c[bp_actual]
                R = c[(bp_actual+1)%n]
                mc.add((L, S, R))
        # How many total contexts does this proc have?
        total_ctx = ms[(bp_actual-1)%n] * ms[bp_actual] * ms[(bp_actual+1)%n]
        print(f'    Proc {bp_actual}: {len(mc)}/{total_ctx} mover contexts')
else:
    print('No fair cycle found in any construction')

# Theoretical comparison
other_product = product // 8
print(f'\n=== THEORETICAL n=8 VALUES ===')
print(f'Configs per context at middle binary: {other_product}')
print(f'Typical cycle length for 3CB at n=8 would be ~3n-2=22')
print(f'Typical mover contexts at mid = 2 (same as n=4..7)')
print(f'Theoretical bottleneck = (2592-22)/(22*2) = {(2592-22)/(22*2):.2f}')
print(f'At n=7: bottleneck was 7.59, configs/ctx=108')
print(f'At n=8: configs/ctx={other_product}, ratio={other_product/108:.2f}x more configs per ctx')
