#!/usr/bin/env python3
"""shadow_scc_structure.py — Analyze the 3 bad SCCs (252, 168, 72).

Key question: what structural pattern makes these 492 configs special?
Do they relate to the shadow permutation σ? To binary state patterns?
Understanding this might reveal WHY non-uniform cycles also create them.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict


def prod(sc):
    p = 1
    for m in sc:
        p *= m
    return p


def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, f"non-single mover at step {idx}"
        mover = diffs[0]
        Li = c[(mover - 1) % n]; Si = c[mover]; Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, "conflict"
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}, "conflict"
                required[key] = Si
    return True, required, "OK"


def construct_sweep_cycle(ms, n, nb_vals):
    config = [0] * n
    cycle = [tuple(config)]
    for proc in range(n):
        config = list(cycle[-1])
        new_val = 1 if ms[proc] == 2 else nb_vals.get(proc, 1)
        if config[proc] == new_val:
            return None
        config[proc] = new_val
        cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        if config[proc] == 0:
            return None
        config[proc] = 0
        cycle.append(tuple(config))
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    return cycle


def find_sccs(forced_succs):
    """Iterative Tarjan SCC."""
    index_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []

    def strongconnect_iter(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        while work:
            node, si = work[-1]
            succs = forced_succs.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
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
                    if len(scc) > 1 or (len(scc) == 1 and node in forced_succs.get(node, [])):
                        sccs.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    for v in forced_succs:
        if v not in index_map:
            strongconnect_iter(v)

    return sccs


def main():
    n = 9
    ms = (2, 2, 3, 3, 3, 3, 3, 3, 3)

    print("=" * 70)
    print("SCC STRUCTURE ANALYSIS")
    print("=" * 70)

    nb_vals = {i: 1 for i in range(n)}
    cycle = construct_sweep_cycle(list(ms), n, nb_vals)
    ok, det, msg = check_cycle_consistency(cycle, n, list(ms))
    good_set = set(cycle)

    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Build forced successor graph
    forced_succs = {}
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[i] = det[key]
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    succs.append(new_c)
        if succs:
            forced_succs[c] = succs

    sccs = find_sccs(forced_succs)
    sccs.sort(key=len, reverse=True)

    print(f"\nSCCs found: {len(sccs)}, sizes: {[len(s) for s in sccs]}")

    # ─── Analyze each SCC ───
    for si, scc in enumerate(sccs):
        scc_set = set(scc)
        print(f"\n{'─' * 60}")
        print(f"SCC #{si+1}: {len(scc)} configs")
        print(f"{'─' * 60}")

        # Binary state distribution
        bin_dist = Counter(tuple(c[i] for i in range(n) if ms[i] == 2) for c in scc)
        print(f"\n  Binary state distribution:")
        for bs, count in sorted(bin_dist.items()):
            print(f"    bin={bs}: {count} configs")

        # Ternary state distribution
        tern_procs = [i for i in range(n) if ms[i] == 3]
        tern_sum_dist = Counter(sum(c[i] for i in tern_procs) for c in scc)
        print(f"\n  Ternary state sum distribution:")
        for ts, count in sorted(tern_sum_dist.items()):
            print(f"    sum={ts}: {count} configs")

        # Number of zeros in each config
        zero_dist = Counter(sum(1 for j in range(n) if c[j] == 0) for c in scc)
        print(f"\n  Zero-count distribution:")
        for z, count in sorted(zero_dist.items()):
            print(f"    zeros={z}: {count} configs")

        # Which processors are forced-privileged?
        priv_proc_dist = Counter()
        for c in scc:
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    new_c = list(c)
                    new_c[i] = det[key]
                    if tuple(new_c) in scc_set:
                        priv_proc_dist[i] += 1
        print(f"\n  Internal forced-privilege by processor:")
        for proc in range(n):
            count = priv_proc_dist.get(proc, 0)
            ptype = "BIN" if ms[proc] == 2 else "TER"
            print(f"    P{proc}({ptype}): {count} internal moves")

        # Show a sample cycle within the SCC
        print(f"\n  Sample forced-move path (first 30 steps):")
        start = scc[0]
        path = [start]
        c = start
        for step in range(30):
            # Pick first forced successor within SCC
            found = False
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    new_c = list(c)
                    new_c[i] = det[key]
                    new_c = tuple(new_c)
                    if new_c in scc_set:
                        mover = i
                        c = new_c
                        path.append(c)
                        found = True
                        break
            if not found:
                break

        for pidx, cfg in enumerate(path[:20]):
            if pidx < len(path) - 1:
                nxt = path[pidx + 1]
                diff = [j for j in range(n) if cfg[j] != nxt[j]]
                mstr = f"→ P{diff[0]}" if diff else "→ ?"
            else:
                mstr = ""
            print(f"    {pidx}: {cfg} {mstr}")

        # Find cycle within path
        seen = {}
        for pidx, cfg in enumerate(path):
            if cfg in seen:
                cyc_len = pidx - seen[cfg]
                print(f"\n  Cycle found at step {seen[cfg]}, length {cyc_len}")
                cyc_movers = []
                for ci in range(seen[cfg], pidx):
                    diff = [j for j in range(n) if path[ci][j] != path[ci+1][j]]
                    cyc_movers.append(diff[0])
                print(f"  Cycle movers: {cyc_movers}")
                break
            seen[cfg] = pidx

    # ─── Compare: is SCC structure same across all 4 necklaces? ───
    print(f"\n{'─' * 60}")
    print("CROSS-NECKLACE COMPARISON")
    print(f"{'─' * 60}")

    all_ms = [
        (2, 2, 3, 3, 3, 3, 3, 3, 3),
        (2, 3, 2, 3, 3, 3, 3, 3, 3),
        (2, 3, 3, 2, 3, 3, 3, 3, 3),
        (2, 3, 3, 3, 2, 3, 3, 3, 3),
    ]

    for ms_test in all_ms:
        ms_list = list(ms_test)
        bin_pos = [i for i in range(n) if ms_test[i] == 2]
        cycle = construct_sweep_cycle(ms_list, n, {i: 1 for i in range(n)})
        if not cycle:
            print(f"  ms={ms_test}: no sweep cycle")
            continue
        ok, det_t, msg = check_cycle_consistency(cycle, n, ms_list)
        good_set_t = set(cycle)
        non_good_t = [c for c in iproduct(*[range(m) for m in ms_test]) if c not in good_set_t]
        non_good_set_t = set(non_good_t)

        fs = {}
        for c in non_good_t:
            succs = []
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                key = (i, L, S, R)
                if key in det_t and det_t[key] != S:
                    new_c = list(c)
                    new_c[i] = det_t[key]
                    new_c = tuple(new_c)
                    if new_c in non_good_set_t:
                        succs.append(new_c)
            if succs:
                fs[c] = succs

        sccs_t = find_sccs(fs)
        sizes = sorted([len(s) for s in sccs_t], reverse=True)
        print(f"  ms={ms_test} bin_pos={bin_pos}: {len(sccs_t)} SCCs, sizes={sizes}")

    # ─── Key structural insight ───
    print(f"\n{'─' * 60}")
    print("STRUCTURAL INSIGHT")
    print(f"{'─' * 60}")
    print(f"""
The 3 bad SCCs ({', '.join(str(len(s)) for s in sccs)} configs) are created by
the uniform sweep's determined mover entries. These entries force specific
transitions that cycle through ternary-state variations.

The binary state distribution within each SCC reveals whether the shadow
operates in the binary or ternary dimension. If all 4 binary states appear
equally, the shadow is ternary-driven. If binary states are skewed, the
shadow exploits binary structure.

The mover processors within SCCs reveal which processors drive the shadow.
Binary processors (P0, P1) have only 2 states — their forced moves are
fully determined. Ternary processors have 3 states — their forced moves
come from the specific sweep cycle's determined entries.
""")


if __name__ == "__main__":
    main()
