#!/usr/bin/env python3
"""3CB Context Saturation Analysis.

Measures context usage at middle binary proc across n=4..8.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'docs'))

from itertools import product as cartesian
from collections import defaultdict, Counter
from verifier import all_configs as gen_configs, apply_move, privileged_set, verify_system

# Import witnesses
from verify_witnesses import witness_n4, witness_n5, witness_n6, witness_n7


def analyze_system(name, ms_tuple, rules_tuple):
    ms = list(ms_tuple)
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    # Find 3CB positions
    binary_pos = None
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            binary_pos = [i, (i+1)%n, (i+2)%n]
            break
    if binary_pos is None:
        print(f'{name}: NO 3CB found')
        return None

    mid = binary_pos[1]  # middle binary proc

    # Build fs
    fs = []
    for table in rules_tuple:
        def make_f(t):
            def f(L, S, R):
                return t[(L, S, R)]
            return f
        fs.append(make_f(table))

    # Verify
    result = verify_system(ms, fs, verbose=False)
    if not result['valid']:
        print(f'{name}: INVALID system')
        return None

    cycle = result['cycle']
    cycle_set = set(cycle)
    good = result['good_configs']
    configs = list(gen_configs(ms))
    bad = [c for c in configs if c not in good]
    bad_set = set(bad)

    # Mover sequence in cycle
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    cycle_movers = []
    for c in cycle:
        p = priv_map[c]
        assert len(p) == 1
        cycle_movers.append(p[0])

    # Context analysis at middle binary proc
    all_8_contexts = [(L, S, R) for L in range(2) for S in range(2) for R in range(2)]

    mover_contexts = set()
    nonmover_contexts = set()
    mover_ctx_count = Counter()
    nonmover_ctx_count = Counter()
    for idx, c in enumerate(cycle):
        L = c[(mid-1)%n]
        S = c[mid]
        R = c[(mid+1)%n]
        ctx = (L, S, R)
        if cycle_movers[idx] == mid:
            mover_contexts.add(ctx)
            mover_ctx_count[ctx] += 1
        else:
            nonmover_contexts.add(ctx)
            nonmover_ctx_count[ctx] += 1

    # Configs per context at mid
    ctx_configs = defaultdict(list)
    ctx_good = defaultdict(int)
    ctx_bad = defaultdict(int)
    for c in configs:
        L = c[(mid-1)%n]
        S = c[mid]
        R = c[(mid+1)%n]
        ctx = (L, S, R)
        ctx_configs[ctx].append(c)
        if c in good:
            ctx_good[ctx] += 1
        else:
            ctx_bad[ctx] += 1

    # Convergence depth via DAG rank
    bad_succs = defaultdict(list)
    for c in bad:
        for i in priv_map[c]:
            s = apply_move(c, i, fs, ms)
            if s in bad_set:
                bad_succs[c].append(s)

    in_degree = defaultdict(int)
    for c in bad:
        for s in bad_succs[c]:
            in_degree[s] += 1

    queue = [c for c in bad if in_degree[c] == 0]
    rank = {c: 0 for c in bad}
    q = list(queue)
    while q:
        c = q.pop(0)
        for s in bad_succs[c]:
            r = rank[c] + 1
            if r > rank[s]:
                rank[s] = r
            in_degree[s] -= 1
            if in_degree[s] == 0:
                q.append(s)

    max_depth = max(rank.values()) if rank else 0

    # Bad configs draining via middle binary proc firing
    mid_drain = 0
    for c in bad:
        if mid in priv_map[c]:
            s = apply_move(c, mid, fs, ms)
            if s in good:
                mid_drain += 1

    other_product = product // (ms[(mid-1)%n] * ms[mid] * ms[(mid+1)%n])

    overlap = mover_contexts & nonmover_contexts
    bottleneck = len(bad) / (len(cycle) * len(mover_contexts)) if mover_contexts else float('inf')

    print(f'=== {name}: n={n}, ms={ms}, product={product} ===')
    print(f'  3CB at positions: {binary_pos}, middle={mid}')
    print(f'  Total configs: {len(configs)}')
    print(f'  Good cycle length: {len(cycle)}')
    print(f'  Good configs (incl tails): {len(good)}')
    print(f'  Bad configs: {len(bad)}')
    print(f'  Max convergence depth: {max_depth}')
    print()
    print(f'  Middle binary (proc {mid}) context analysis:')
    print(f'  Configs per context triple: {other_product} (product / (m_L * m_S * m_R))')
    print(f'  Mover contexts in cycle: {len(mover_contexts)}/8 = {sorted(mover_contexts)}')
    print(f'  Non-mover contexts in cycle: {len(nonmover_contexts)}/8')
    print(f'  Overlap (both mover & non-mover): {len(overlap)} = {sorted(overlap)}')
    print()
    print(f'  Per-context breakdown:')
    for ctx in sorted(all_8_contexts):
        total = len(ctx_configs[ctx])
        g = ctx_good[ctx]
        b = ctx_bad[ctx]
        role = 'M' if ctx in mover_contexts else ' '
        role += 'N' if ctx in nonmover_contexts else ' '
        mc = mover_ctx_count[ctx]
        nc = nonmover_ctx_count[ctx]
        print(f'    {ctx}: total={total:4d}, good={g:3d}, bad={b:4d}, role={role}, in_cycle: mover={mc} nonmover={nc}')

    print()
    drain_pct = mid_drain/len(bad)*100 if len(bad) > 0 else 0
    print(f'  Bad draining via mid firing: {mid_drain}/{len(bad)} = {drain_pct:.1f}%')
    print(f'  Bottleneck ratio (bad / (cycle_len * mover_ctx)): {bottleneck:.2f}')
    print()

    return {
        'n': n, 'ms': ms, 'product': product,
        'total': len(configs), 'cycle_len': len(cycle),
        'good': len(good), 'bad': len(bad),
        'mover_ctx': len(mover_contexts), 'nonmover_ctx': len(nonmover_contexts),
        'overlap': len(overlap), 'max_depth': max_depth,
        'mid_drain': mid_drain, 'bottleneck': bottleneck,
        'other_product': other_product,
        'drain_pct': drain_pct,
    }


# ── n=8 failure analysis ──────────────────────────────────────────────
def analyze_n8_failure():
    """Analyze n=8 3CB failure: ms=(2,2,2,3,3,3,3,4), product=2592."""
    ms = [2, 2, 2, 3, 3, 3, 3, 4]
    n = 8
    product = 1
    for m in ms:
        product *= m
    binary_pos = [0, 1, 2]
    mid = 1

    print(f'=== n=8 FAILURE: ms={ms}, product={product} ===')
    print(f'  3CB at positions: {binary_pos}, middle={mid}')
    print(f'  Total configs: {product}')
    print(f'  Threshold: 4*3^6 = {4*3**6}')
    print(f'  Sub-threshold: {product < 4*3**6}')

    configs = list(gen_configs(ms))
    other_product = product // (ms[(mid-1)%n] * ms[mid] * ms[(mid+1)%n])
    print(f'  Configs per context triple: {other_product}')

    # Try all sweep orders with good-targeting
    from ra_3cb_transition import (
        make_fs_from_tables, good_targeting_completion,
        build_bounce_cycle as bounce, build_mixed_sweep_cycle, cyclic_orders
    )

    best_scc = None
    best_cycle_len = 0
    n_tried = 0

    for order in cyclic_orders(n):
        targets = {p: 1 for p in range(n)}
        for return_same in [True, False]:
            cycle = build_mixed_sweep_cycle(ms, order, targets, return_same)
            if cycle is None:
                continue
            n_tried += 1
            result = good_targeting_completion(ms, cycle)
            if result is None:
                continue
            vr = result['verify']
            if vr['valid']:
                print(f'  FOUND VALID! order={order}, return_same={return_same}')
                return
            # Check bad SCC size
            if 'cycle' in vr:
                cl = vr.get('cycle_length', 0)
                if cl > best_cycle_len:
                    best_cycle_len = cl

    # Try bounce cycles
    for base in [list(range(n)) + list(range(n-2, 0, -1)),
                 list(range(n-1, -1, -1)) + list(range(1, n))]:
        cycle, movers = bounce(ms, base)
        if cycle is None:
            continue
        n_tried += 1
        result = good_targeting_completion(ms, cycle)
        if result is None:
            continue
        vr = result['verify']
        if vr['valid']:
            print(f'  FOUND VALID via bounce!')
            return

        # Analyze the failed system
        if 'properties' in vr:
            tables = result['tables']
            fs = make_fs_from_tables(tables)
            priv_map = {}
            for c in configs:
                priv_map[c] = privileged_set(c, fs, ms)

            # Find good candidates
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

            # Find cycles
            visited = set()
            cycles_found = []
            for c in good_cands:
                if c in visited:
                    continue
                path = []
                path_set = set()
                node = c
                while node not in visited and node not in path_set:
                    path.append(node)
                    path_set.add(node)
                    node = succ[node][0]
                if node in path_set:
                    cy = path[path.index(node):]
                    cycles_found.append(cy)
                visited.update(path)

            if cycles_found:
                cy = max(cycles_found, key=len)
                good_set = set(cy)
                bad_configs = [c for c in configs if c not in good_set]

                # Context analysis at mid for the good cycle
                all_8 = [(L, S, R) for L in range(2) for S in range(2) for R in range(2)]
                mover_ctxs = set()
                nonmover_ctxs = set()
                for c in cy:
                    _, mover = succ[c]
                    L = c[(mid-1)%n]
                    S = c[mid]
                    R = c[(mid+1)%n]
                    ctx = (L, S, R)
                    if mover == mid:
                        mover_ctxs.add(ctx)
                    else:
                        nonmover_ctxs.add(ctx)

                # Bad SCC analysis
                bad_set = set(bad_configs)
                bad_adj = defaultdict(list)
                for c in bad_configs:
                    for i in priv_map[c]:
                        s = apply_move(c, i, fs, ms)
                        if s in bad_set:
                            bad_adj[c].append(s)

                # Find SCCs in bad graph
                idx_counter = [0]
                stack = []
                on_stack = set()
                index_map = {}
                lowlink = {}
                sccs = []

                def strongconnect(v):
                    work = [(v, 0)]
                    index_map[v] = lowlink[v] = idx_counter[0]
                    idx_counter[0] += 1
                    stack.append(v)
                    on_stack.add(v)
                    while work:
                        node, si = work[-1]
                        succs_list = bad_adj.get(node, [])
                        if si < len(succs_list):
                            work[-1] = (node, si + 1)
                            w = succs_list[si]
                            if w not in index_map:
                                index_map[w] = lowlink[w] = idx_counter[0]
                                idx_counter[0] += 1
                                stack.append(w)
                                on_stack.add(w)
                                work.append((w, 0))
                            elif w in on_stack:
                                lowlink[node] = min(lowlink[node], index_map[w])
                        else:
                            if lowlink[node] == index_map[node]:
                                scc = []
                                while True:
                                    w = stack.pop()
                                    on_stack.discard(w)
                                    scc.append(w)
                                    if w == node:
                                        break
                                if len(scc) > 1 or (scc[0] in bad_adj and scc[0] in bad_adj[scc[0]]):
                                    sccs.append(scc)
                            work.pop()
                            if work:
                                lowlink[work[-1][0]] = min(lowlink[work[-1][0]], lowlink[node])

                for v in bad_adj:
                    if v not in index_map:
                        strongconnect(v)

                recurrent_bad = sum(len(s) for s in sccs)
                print(f'  Tried {n_tried} constructions, none valid')
                print(f'  Best good cycle found: length {len(cy)}')
                print(f'  Good candidates: {len(good_cands)}')
                print(f'  Bad configs: {len(bad_configs)}')
                print(f'  Bad SCCs: {len(sccs)}, total recurrent bad: {recurrent_bad}')
                print(f'  Mover contexts at mid: {len(mover_ctxs)}/8 = {sorted(mover_ctxs)}')
                print(f'  Non-mover contexts at mid: {len(nonmover_ctxs)}/8')
                print(f'  Overlap: {len(mover_ctxs & nonmover_ctxs)}')
                print()

                # Context distribution in bad SCCs
                scc_set = set()
                for s in sccs:
                    scc_set.update(s)
                ctx_in_scc = Counter()
                for c in scc_set:
                    L = c[(mid-1)%n]
                    S = c[mid]
                    R = c[(mid+1)%n]
                    ctx_in_scc[(L, S, R)] += 1

                print(f'  Context distribution in recurrent bad configs:')
                for ctx in sorted(all_8):
                    cnt = ctx_in_scc[ctx]
                    total_with_ctx = sum(1 for c in configs if (c[(mid-1)%n], c[mid], c[(mid+1)%n]) == ctx)
                    print(f'    {ctx}: {cnt}/{total_with_ctx} ({cnt/total_with_ctx*100:.1f}% of context)')

                bottleneck = len(bad_configs) / (len(cy) * len(mover_ctxs)) if mover_ctxs else float('inf')
                print(f'\n  Bottleneck ratio: {bottleneck:.2f}')
                print(f'  Configs per context: {other_product}')

                return {
                    'n': 8, 'product': product, 'total': len(configs),
                    'cycle_len': len(cy), 'bad': len(bad_configs),
                    'mover_ctx': len(mover_ctxs), 'recurrent_bad': recurrent_bad,
                    'n_sccs': len(sccs), 'bottleneck': bottleneck,
                    'other_product': other_product,
                }

    print(f'  Tried {n_tried} constructions, none valid, no good cycle found')
    return None


if __name__ == '__main__':
    results = {}
    for name, wfn in [('n=4', witness_n4), ('n=5', witness_n5),
                       ('n=6', witness_n6), ('n=7', witness_n7)]:
        ms, rules = wfn()
        r = analyze_system(name, ms, rules)
        if r:
            results[r['n']] = r

    r8 = analyze_n8_failure()
    if r8:
        results[8] = r8

    print('=' * 100)
    print('SATURATION TABLE')
    print('=' * 100)
    hdr = f'{"n":>3} {"product":>8} {"total":>8} {"cfg/ctx":>8} {"cycle":>6} {"mover_ctx":>10} {"bad":>8} {"depth":>6} {"bottleneck":>10} {"drain%":>8}'
    print(hdr)
    print('-' * 100)
    for n_val in sorted(results):
        r = results[n_val]
        depth = r.get('max_depth', 'INF')
        drain = r.get('drain_pct', 0)
        if n_val == 8:
            depth = 'INF'
            drain = 'N/A'
            print(f'{r["n"]:3d} {r["product"]:8d} {r["total"]:8d} {r["other_product"]:8d} {r["cycle_len"]:6d} {r["mover_ctx"]:10d} {r["bad"]:8d} {"INF":>6} {r["bottleneck"]:10.2f} {"N/A":>8}')
        else:
            print(f'{r["n"]:3d} {r["product"]:8d} {r["total"]:8d} {r["other_product"]:8d} {r["cycle_len"]:6d} {r["mover_ctx"]:10d} {r["bad"]:8d} {depth:6d} {r["bottleneck"]:10.2f} {drain:7.1f}%')
