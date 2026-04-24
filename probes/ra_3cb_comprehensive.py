#!/usr/bin/env python3
"""Comprehensive 3CB investigation — privilege graph, response exhaustion, context saturation.

Uses ra_3cb_transition infrastructure for system construction.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
import time

from verifier import all_configs, privileged_set, apply_move, verify_system
from ra_3cb_transition import (
    build_mixed_sweep_cycle, good_targeting_completion, build_bounce_cycle,
    cyclic_orders, make_fs_from_tables, diagnose_tables, run_mixed_sweep_family,
    run_bounce_family, Config, Triple, RuleTable
)


# ─── Tarjan SCC (iterative) ─────────────────────────────────────────────

def tarjan_scc(nodes, succs_fn):
    """Iterative Tarjan's SCC."""
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []

    for start in nodes:
        if start in index:
            continue
        call_stack = [(start, iter(succs_fn(start)))]
        index[start] = lowlink[start] = index_counter[0]
        index_counter[0] += 1
        stack.append(start)
        on_stack.add(start)

        while call_stack:
            node, children = call_stack[-1]
            advanced = False
            for w in children:
                if w not in index:
                    index[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    call_stack.append((w, iter(succs_fn(w))))
                    advanced = True
                    break
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index[w])

            if not advanced:
                call_stack.pop()
                if call_stack:
                    parent = call_stack[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
                if lowlink[node] == index[node]:
                    scc = set()
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.add(w)
                        if w == node:
                            break
                    sccs.append(scc)
    return sccs


# ─── Analysis ────────────────────────────────────────────────────────────

def analyze_bad_graph(ms, fs, good_set, mid_binary):
    """Full analysis of bad-config transition graph."""
    n = len(ms)
    configs = list(all_configs(ms))
    bad = [c for c in configs if c not in good_set]
    bad_set = set(bad)

    if not bad:
        return {'total_bad': 0, 'recurrent_count': 0, 'num_recurrent_sccs': 0,
                'scc_info': [], 'max_depth': 0, 'all_bad_ctx_at_mid': {}}

    # Build bad→bad successors
    bad_succs = defaultdict(list)
    for c in bad:
        priv = privileged_set(c, fs, ms)
        for i in priv:
            s = apply_move(c, i, fs, ms)
            if s in bad_set:
                bad_succs[c].append(s)

    # Tarjan SCC
    sccs = tarjan_scc(bad, lambda v: bad_succs.get(v, []))
    recurrent = []
    for scc in sccs:
        if len(scc) > 1:
            recurrent.append(scc)
        elif len(scc) == 1:
            node = next(iter(scc))
            if node in bad_succs.get(node, []):
                recurrent.append(scc)

    scc_info = []
    for scc in recurrent:
        info = {'size': len(scc)}
        if mid_binary is not None:
            ctx_counts = Counter()
            for c in scc:
                L = c[(mid_binary-1) % n]
                S = c[mid_binary]
                R = c[(mid_binary+1) % n]
                ctx_counts[(L, S, R)] += 1
            info['mid_binary_contexts'] = dict(ctx_counts)
        priv_counts = Counter()
        for c in scc:
            for p in privileged_set(c, fs, ms):
                priv_counts[p] += 1
        info['priv_distribution'] = dict(priv_counts)
        scc_info.append(info)

    total_recurrent = sum(s['size'] for s in scc_info)

    # Context distribution across all bad configs
    all_bad_ctx = Counter()
    if mid_binary is not None:
        for c in bad:
            ctx = (c[(mid_binary-1)%n], c[mid_binary], c[(mid_binary+1)%n])
            all_bad_ctx[ctx] += 1

    # Convergence depth (only if no recurrent SCCs and not too many configs)
    max_depth = None
    if not recurrent and len(bad) <= 50000:
        depth = {c: 1 for c in bad}
        for _ in range(len(bad)):
            changed = False
            for c in bad:
                succs = bad_succs.get(c, [])
                if succs:
                    new_d = 1 + max(depth[s] for s in succs)
                    if new_d != depth[c]:
                        depth[c] = new_d
                        changed = True
            if not changed:
                break
        max_depth = max(depth.values()) if depth else 0

    return {
        'total_bad': len(bad), 'recurrent_count': total_recurrent,
        'num_recurrent_sccs': len(recurrent), 'scc_info': scc_info,
        'max_depth': max_depth, 'all_bad_ctx_at_mid': dict(all_bad_ctx),
    }


def build_best_system(ms):
    """Try all construction methods, return the best (least recurrent bad)."""
    n = len(ms)
    best_rec = float('inf')
    best_fs = None
    best_good = None
    best_label = None
    best_tables = None

    # 1. Mixed sweep family
    non_binary = [p for p, m in enumerate(ms) if m > 2]
    target_ranges = [range(1, ms[p]) for p in non_binary]
    for combo in cartesian(*target_ranges):
        targets = {p: 1 for p, m in enumerate(ms) if m == 2}
        for idx, p in enumerate(non_binary):
            targets[p] = combo[idx]
        for order in cyclic_orders(n):
            for ret_same in (True, False):
                cycle = build_mixed_sweep_cycle(ms, order, targets, ret_same)
                if cycle is None:
                    continue
                comp = good_targeting_completion(ms, cycle)
                if comp is None:
                    continue
                tables = comp['tables']
                fs = comp['fs']
                result = comp['verify']
                if result['valid']:
                    return fs, tables, set(cycle), 'mixed_sweep(VALID)', 0
                # Check recurrent bad count
                diag = diagnose_tables(ms, tables)
                rec = diag['best_scc_nodes'] if diag['best_scc_nodes'] is not None else float('inf')
                if rec < best_rec:
                    best_rec = rec
                    best_fs = fs
                    best_tables = tables
                    best_good = set(cycle)
                    best_label = f"mixed_sweep"

    # 2. Bounce family
    base_cw = list(range(n)) + list(range(n-2, 0, -1))
    base_ccw = list(range(n-1, -1, -1)) + list(range(1, n-1))
    patterns_seen = set()
    for base in (base_cw, base_ccw):
        for shift in range(len(base)):
            pattern = tuple(base[shift:] + base[:shift])
            if pattern in patterns_seen:
                continue
            patterns_seen.add(pattern)
            cycle, movers = build_bounce_cycle(ms, base_pattern=pattern)
            if cycle is None:
                continue
            comp = good_targeting_completion(ms, cycle)
            if comp is None:
                continue
            tables = comp['tables']
            fs = comp['fs']
            result = comp['verify']
            if result['valid']:
                return fs, tables, set(cycle), 'bounce(VALID)', 0
            diag = diagnose_tables(ms, tables)
            rec = diag['best_scc_nodes'] if diag['best_scc_nodes'] is not None else float('inf')
            if rec < best_rec:
                best_rec = rec
                best_fs = fs
                best_tables = tables
                best_good = set(cycle)
                best_label = "bounce"

    return best_fs, best_tables, best_good, best_label, best_rec


def investigate(ms, binary_positions, label):
    """Full investigation for a given ms + binary positions."""
    n = len(ms)
    product = 1
    for m in ms:
        product *= m
    mid = binary_positions[len(binary_positions)//2]

    print(f"\n{'='*70}")
    print(f"{label}: ms={ms}, product={product}, binary at {binary_positions}, mid={mid}")
    print(f"{'='*70}")

    t0 = time.time()
    fs, tables, good_set, method, rec_count = build_best_system(ms)
    elapsed = time.time() - t0

    if fs is None:
        print(f"  NO SYSTEM BUILT ({elapsed:.1f}s)")
        return None

    configs = list(all_configs(ms))
    bad_configs = [c for c in configs if c not in good_set]

    print(f"  Best method: {method}")
    print(f"  Good cycle: {len(good_set)} configs, Bad: {len(bad_configs)}")
    print(f"  Recurrent bad: {rec_count}")
    print(f"  Construction time: {elapsed:.1f}s")

    # Full bad-graph analysis
    analysis = analyze_bad_graph(ms, fs, good_set, mid)

    # Context analysis at middle binary
    m_L = ms[(mid-1) % n]
    m_R = ms[(mid+1) % n]

    good_mover_ctx = set()
    good_nonmover_ctx = set()
    for c in good_set:
        L = c[(mid-1) % n]; S = c[mid]; R = c[(mid+1) % n]
        if fs[mid](L, S, R) != S:
            good_mover_ctx.add((L, S, R))
        else:
            good_nonmover_ctx.add((L, S, R))

    print(f"\n  --- Context at proc {mid} (middle binary) ---")
    print(f"  Mover contexts: {len(good_mover_ctx)} — {sorted(good_mover_ctx)}")
    print(f"  Non-mover contexts: {len(good_nonmover_ctx)}")

    print(f"\n  Per-context (total/good/bad):")
    for L in range(m_L):
        for S in range(2):
            for R in range(m_R):
                ctx = (L, S, R)
                total = sum(1 for c in configs if c[(mid-1)%n]==L and c[mid]==S and c[(mid+1)%n]==R)
                good_ct = sum(1 for c in good_set if c[(mid-1)%n]==L and c[mid]==S and c[(mid+1)%n]==R)
                mflag = "M" if ctx in good_mover_ctx else " "
                print(f"    {ctx} [{mflag}]: total={total:>4}, good={good_ct:>3}, bad={total-good_ct:>4}")

    # Recurrent SCC analysis
    if analysis['scc_info']:
        print(f"\n  --- Recurrent SCCs ---")
        print(f"  {analysis['num_recurrent_sccs']} SCCs, {analysis['recurrent_count']} total recurrent")
        # Aggregate context distribution across all recurrent SCCs
        agg_ctx = Counter()
        for scc in analysis['scc_info']:
            if 'mid_binary_contexts' in scc:
                for ctx, cnt in scc['mid_binary_contexts'].items():
                    agg_ctx[ctx] += cnt
        if agg_ctx:
            print(f"  Recurrent configs by context at proc {mid}:")
            for ctx in sorted(agg_ctx.keys()):
                print(f"    {ctx}: {agg_ctx[ctx]}")

        # Show a few SCCs
        for i, scc in enumerate(analysis['scc_info'][:5]):
            print(f"    SCC {i}: size={scc['size']}, priv={scc['priv_distribution']}")

    if analysis['max_depth'] is not None:
        print(f"\n  Max convergence depth: {analysis['max_depth']}")

    # Drainage via middle binary
    drain_via_mid = 0
    for c in bad_configs:
        priv = privileged_set(c, fs, ms)
        if mid in priv:
            s = apply_move(c, mid, fs, ms)
            if s in good_set:
                drain_via_mid += 1
    drain_pct = 100*drain_via_mid/max(1,len(bad_configs))
    print(f"\n  Drain to good via proc {mid}: {drain_via_mid}/{len(bad_configs)} ({drain_pct:.1f}%)")

    return {
        'n': n, 'ms': ms, 'product': product, 'method': method,
        'good_size': len(good_set), 'bad_size': len(bad_configs),
        'recurrent': analysis['recurrent_count'],
        'recurrent_sccs': analysis['num_recurrent_sccs'],
        'max_depth': analysis['max_depth'],
        'mover_contexts': len(good_mover_ctx),
        'drain_via_mid': drain_via_mid, 'drain_pct': drain_pct,
        'valid': rec_count == 0,
    }


def response_exhaustion(ms, binary_positions):
    """Test ALL toggle-valid privilege rules at middle binary proc."""
    n = len(ms)
    mid = binary_positions[len(binary_positions)//2]
    m_L = ms[(mid-1) % n]
    m_R = ms[(mid+1) % n]

    # Enumerate toggle pairs: (L,0,R) paired with (L,1,R)
    pairs = []
    for L in range(m_L):
        for R in range(m_R):
            pairs.append(((L, 0, R), (L, 1, R)))

    # Enumerate all valid subsets (choose 0 or 1 from each pair, at least 1 total)
    rules = []
    def backtrack(idx, chosen):
        if idx == len(pairs):
            if chosen:
                rules.append(frozenset(chosen))
            return
        backtrack(idx+1, chosen)
        backtrack(idx+1, chosen + [pairs[idx][0]])
        backtrack(idx+1, chosen + [pairs[idx][1]])
    backtrack(0, [])

    print(f"\n{'='*70}")
    print(f"RESPONSE EXHAUSTION at proc {mid}: {len(rules)} toggle-valid rules")
    print(f"ms={ms}")
    print(f"{'='*70}")

    results = []
    for ri, rule in enumerate(rules):
        # For each rule, try constructions where proc mid's mover set = rule
        # We need to build cycles where proc mid fires exactly on these contexts
        # This is hard to force with mixed sweep, so instead:
        # Build the system normally, then check what proc mid's actual mover set is

        # Simpler approach: just test all 80 rules by building transition tables
        # where proc mid fires on exactly the triples in `rule`
        rule_set = set(rule)
        best_rec = float('inf')
        best_method = None

        # Try mixed sweep cycles and override proc mid's table
        non_binary = [p for p, m in enumerate(ms) if m > 2]
        target_ranges = [range(1, ms[p]) for p in non_binary]

        tried = 0
        for combo in cartesian(*target_ranges):
            targets = {p: 1 for p, m in enumerate(ms) if m == 2}
            for idx, p in enumerate(non_binary):
                targets[p] = combo[idx]
            for order in cyclic_orders(n):
                for ret_same in (True, False):
                    cycle = build_mixed_sweep_cycle(ms, order, targets, ret_same)
                    if cycle is None:
                        continue

                    # Check compatibility: does the cycle agree with the fixed rule?
                    compatible = True
                    for ci in range(len(cycle)):
                        c = cycle[ci]
                        c_next = cycle[(ci+1) % len(cycle)]
                        diffs = [p for p in range(n) if c[p] != c_next[p]]
                        if len(diffs) != 1:
                            compatible = False
                            break
                        mover = diffs[0]
                        ctx = (c[(mid-1)%n], c[mid], c[(mid+1)%n])
                        if mover == mid:
                            if ctx not in rule_set:
                                compatible = False
                                break
                        else:
                            if ctx in rule_set:
                                # mid should fire here but doesn't — might be ok
                                # (rule says ctx is mover, but mid isn't the chosen mover)
                                # This is fine for cycle construction
                                pass

                    if not compatible:
                        continue

                    comp = good_targeting_completion(ms, cycle)
                    if comp is None:
                        continue

                    # Override proc mid's table to match the rule
                    tables = list(comp['tables'])
                    mid_table = dict(tables[mid])
                    for L in range(m_L):
                        for S in range(2):
                            for R in range(m_R):
                                ctx = (L, S, R)
                                key = (L, S, R)
                                if ctx in rule_set:
                                    if mid_table[key] == S:
                                        mid_table[key] = 1 - S  # force fire
                                else:
                                    mid_table[key] = S  # force non-fire
                    tables[mid] = mid_table

                    fs = make_fs_from_tables(tables)
                    diag = diagnose_tables(ms, tables)
                    if diag['dead_count'] > 0:
                        continue
                    rec = diag['best_scc_nodes']
                    if rec is None:
                        rec = float('inf')
                    if rec < best_rec:
                        best_rec = rec
                        best_method = 'mixed_sweep'
                    tried += 1
                    if tried > 200:  # cap per rule
                        break
                if tried > 200:
                    break
            if tried > 200:
                break

        results.append({
            'rule': sorted(rule_set), 'size': len(rule_set),
            'best_recurrent': best_rec, 'method': best_method,
            'converges': best_rec == 0, 'tried': tried,
        })
        if (ri+1) % 20 == 0:
            print(f"  Tested {ri+1}/{len(rules)} rules...")

    # Summary
    print(f"\n  --- Summary ---")
    converging = [r for r in results if r['converges']]
    print(f"  Total rules: {len(results)}")
    print(f"  Converging: {len(converging)}")
    if not converging:
        print(f"  DRAINAGE FAILURE IS UNIVERSAL")

    for size in [1, 2, 3, 4]:
        subset = [r for r in results if r['size'] == size]
        if subset:
            finite = [r for r in subset if r['best_recurrent'] < float('inf')]
            if finite:
                min_r = min(r['best_recurrent'] for r in finite)
                max_r = max(r['best_recurrent'] for r in finite)
                print(f"  |M|={size}: {len(subset)} rules, {len(finite)} with finite rec, "
                      f"range [{min_r}, {max_r}]")
            else:
                no_cycle = [r for r in subset if r['tried'] == 0]
                print(f"  |M|={size}: {len(subset)} rules, {len(no_cycle)} no compatible cycle found")

    # Top 5
    finite_results = [r for r in results if r['best_recurrent'] < float('inf')]
    if finite_results:
        finite_results.sort(key=lambda r: r['best_recurrent'])
        print(f"\n  Top 5 best:")
        for r in finite_results[:5]:
            print(f"    rule={r['rule']}, |M|={r['size']}, rec={r['best_recurrent']}")

    return results


# ─── MAIN ───────────────────────────────────────────────────────────────

if __name__ == '__main__':
    t0 = time.time()

    print("=" * 70)
    print("3CB COMPREHENSIVE INVESTIGATION")
    print("=" * 70)

    # ── Part 1: Context saturation + privilege graph (RA-1 + RA-3) ──
    print("\n### PART 1: CONTEXT SATURATION + PRIVILEGE GRAPH ###\n")

    cases = [
        ((2,2,2,3), [0,1,2], "n=4"),
        ((2,2,2,3,4), [0,1,2], "n=5"),
        ((2,2,2,4,3,3), [0,1,2], "n=6"),
        ((3,2,2,2,3,4,3), [1,2,3], "n=7"),
        ((2,2,2,3,3,3,3,4), [0,1,2], "n=8 (FAILING)"),
    ]

    saturation_data = []
    for ms, bpos, label in cases:
        print(f"\n--- Starting {label} ---")
        sys.stdout.flush()
        result = investigate(ms, bpos, label)
        if result:
            saturation_data.append(result)
        sys.stdout.flush()

    # Summary table
    print(f"\n\n{'='*70}")
    print("SATURATION SUMMARY")
    print(f"{'='*70}")
    print(f"{'n':>3} {'prod':>6} {'good':>5} {'bad':>5} {'rec':>5} "
          f"{'SCCs':>5} {'mctx':>4} {'drain%':>6} {'depth':>6} {'valid':>5}")
    for d in saturation_data:
        depth = str(d['max_depth']) if d['max_depth'] is not None else '∞'
        print(f"{d['n']:>3} {d['product']:>6} {d['good_size']:>5} {d['bad_size']:>5} "
              f"{d['recurrent']:>5} {d['recurrent_sccs']:>5} {d['mover_contexts']:>4} "
              f"{d['drain_pct']:>6.1f} {depth:>6} {str(d['valid']):>5}")

    # ── Part 2: Response exhaustion (RA-2) ──
    elapsed = time.time() - t0
    print(f"\nPart 1 took {elapsed:.1f}s")

    print("\n### PART 2: RESPONSE EXHAUSTION (n=8) ###\n")
    sys.stdout.flush()
    response_exhaustion((2,2,2,3,3,3,3,4), [0,1,2])

    total = time.time() - t0
    print(f"\n\nTotal: {total:.1f}s")
