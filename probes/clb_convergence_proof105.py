#!/usr/bin/env python3
"""
CONVERGENCE PROOF 105: Boundary automaton analysis
====================================================
The 36 boundary states (c[0],c[1],c[n-2],c[n-1]) have exactly 106 transition
types on constant-Φ_full edges (n-independent!). These transitions come from
firing at positions {0, 1, 2, n-2, n-1}.

Questions:
1. Is the boundary automaton a DAG? If so, boundary provides a progress measure.
2. If not, what are the SCCs? Can (Φ_level, boundary, ...) break cycles?
3. Within each boundary state, is the interior subgraph a DAG?
4. What's the KEY ingredient that makes the constant subgraph a DAG?
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)
def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)
def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def main():
    sys.stdout.reconfigure(line_buffering=True)

    # Analyze boundary automaton for multiple n to confirm n-independence
    all_bnd_transitions = set()  # (bnd_from, bnd_to, pos_type, L, S, R, out, dfc)

    for n_val in [9, 10, 11]:
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 900000:
            continue

        # Build TP edges + g_full + Φ_full
        tp_fwd = defaultdict(list)
        tp_nodes = set()
        fc_cache = {}
        tp_edge_list = []
        for c in bad_list:
            fc_cache[c] = fc(c, n)
            tp_nodes.add(c)
        for c in bad_list:
            e2c = exp2_count(c, n)
            i21c = int_21(c, n)
            ewc = exp2_weight(c, n)
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        if succ not in fc_cache:
                            fc_cache[succ] = fc(succ, n)
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            dfc = fc_cache[succ] - fc_cache[c]
                            tp_fwd[c].append((succ, dfc))
                            tp_edge_list.append((c, succ, i, dfc))
                            tp_nodes.add(succ)

        g = {c: 0 for c in tp_nodes}
        for _ in range(2 * n + 5):
            changed = False
            for c in tp_nodes:
                for s, dfc in tp_fwd.get(c, []):
                    new_g = dfc + g[s]
                    if new_g > g[c]:
                        g[c] = new_g
                        changed = True
            if not changed:
                break

        phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

        # Extract constant-Φ edges and their boundary transitions
        bnd_trans_n = set()
        const_edges = []
        for c, s, pos, dfc in tp_edge_list:
            if phi[s] != phi[c]:
                continue
            const_edges.append((c, s, pos, dfc))
            bnd_c = (c[0], c[1], c[n-2], c[n-1])
            bnd_s = (s[0], s[1], s[n-2], s[n-1])
            if bnd_c != bnd_s:
                L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
                if pos == 0: ptype = "bot"
                elif pos == 1: ptype = "low"
                elif pos == 2: ptype = "P2"
                elif pos == n-2: ptype = "high"
                elif pos == n-1: ptype = "top"
                else: ptype = "mid"
                bnd_trans_n.add((bnd_c, bnd_s, ptype, L, S, R, out, dfc))
                all_bnd_transitions.add((bnd_c, bnd_s, ptype, L, S, R, out, dfc))

        print(f"\nn={n}: {len(bnd_trans_n)} boundary transitions, {len(const_edges)} const edges")

    print(f"\n{'='*70}")
    print(f"BOUNDARY AUTOMATON: {len(all_bnd_transitions)} transition types")

    # Build boundary adjacency
    bnd_adj = defaultdict(list)  # bnd_from -> [(bnd_to, info)]
    bnd_states = set()
    for (bf, bt, ptype, L, S, R, out, dfc) in all_bnd_transitions:
        bnd_adj[bf].append((bt, ptype, L, S, R, out, dfc))
        bnd_states.add(bf)
        bnd_states.add(bt)

    print(f"Boundary states involved: {len(bnd_states)}")

    # List all transitions grouped by source
    for bf in sorted(bnd_states):
        targets = bnd_adj.get(bf, [])
        if targets:
            print(f"\n  {bf}:")
            for bt, ptype, L, S, R, out, dfc in sorted(targets):
                print(f"    → {bt}  via {ptype} ({L},{S},{R})→{out} Δfc={dfc:+d}")

    # Check for cycles in boundary automaton
    bnd_simple_adj = defaultdict(set)
    for bf in bnd_states:
        for bt, *_ in bnd_adj.get(bf, []):
            bnd_simple_adj[bf].add(bt)

    # DFS cycle detection
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {b: WHITE for b in bnd_states}
    has_cycle = False
    cycle_edges = []
    parent = {}

    for start in sorted(bnd_states):
        if color[start] != WHITE:
            continue
        stack = [(start, iter(sorted(bnd_simple_adj.get(start, set()))))]
        color[start] = GRAY
        while stack:
            node, children = stack[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    has_cycle = True
                    # Trace cycle
                    cycle = [child]
                    for n2, _ in reversed(stack):
                        cycle.append(n2)
                        if n2 == child:
                            break
                    cycle_edges = list(reversed(cycle))
                    break
                if color[child] == WHITE:
                    color[child] = GRAY
                    parent[child] = node
                    stack.append((child, iter(sorted(bnd_simple_adj.get(child, set())))))
            except StopIteration:
                color[node] = BLACK
                stack.pop()
        if has_cycle:
            break

    print(f"\n{'='*70}")
    print(f"BOUNDARY AUTOMATON DAG CHECK: {'NO — HAS CYCLE' if has_cycle else 'YES — IS A DAG'}")
    if has_cycle:
        print(f"  Cycle: {' → '.join(str(b) for b in cycle_edges)}")

    # Find SCCs using Tarjan's algorithm
    index_counter = [0]
    stack = []
    lowlinks = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlinks[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for w in bnd_simple_adj.get(v, set()):
            if w not in index:
                strongconnect(w)
                lowlinks[v] = min(lowlinks[v], lowlinks[w])
            elif on_stack.get(w, False):
                lowlinks[v] = min(lowlinks[v], index[w])

        if lowlinks[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            sccs.append(frozenset(scc))

    for v in sorted(bnd_states):
        if v not in index:
            strongconnect(v)

    nontrivial_sccs = [s for s in sccs if len(s) > 1]
    print(f"\nSCCs: {len(sccs)} total, {len(nontrivial_sccs)} non-trivial")
    for i, scc in enumerate(nontrivial_sccs):
        print(f"  SCC {i}: {sorted(scc)}")
        # Show edges within this SCC
        for bf in sorted(scc):
            for bt, ptype, L, S, R, out, dfc in sorted(bnd_adj.get(bf, [])):
                if bt in scc:
                    print(f"    {bf} → {bt} via {ptype} ({L},{S},{R})→{out} Δfc={dfc:+d}")

    # Check: with (boundary, g) or (boundary, fc), are SCCs broken?
    print(f"\n{'='*70}")
    print(f"AUGMENTED BOUNDARY: (boundary, Δfc) or (boundary, g) transitions")

    # Use n=9 data to check augmented transitions
    n_val = 9
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    n = n_val

    tp_fwd = defaultdict(list)
    tp_nodes = set()
    fc_cache = {}
    tp_edge_list = []
    for c in bad_list:
        fc_cache[c] = fc(c, n)
        tp_nodes.add(c)
    for c in bad_list:
        e2c = exp2_count(c, n)
        i21c = int_21(c, n)
        ewc = exp2_weight(c, n)
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    if succ not in fc_cache:
                        fc_cache[succ] = fc(succ, n)
                    e2s = exp2_count(succ, n)
                    i21s = int_21(succ, n)
                    ews = exp2_weight(succ, n)
                    if e2s == e2c and i21s == i21c and ews == ewc:
                        dfc = fc_cache[succ] - fc_cache[c]
                        tp_fwd[c].append((succ, dfc))
                        tp_edge_list.append((c, succ, i, dfc))
                        tp_nodes.add(succ)

    g = {c: 0 for c in tp_nodes}
    for _ in range(2 * n + 5):
        changed = False
        for c in tp_nodes:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]:
                    g[c] = new_g
                    changed = True
        if not changed:
            break

    phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

    # Build (boundary, g) transitions on constant-Φ edges
    bg_adj = defaultdict(set)
    bg_states = set()
    for c, s, pos, dfc in tp_edge_list:
        if phi[s] != phi[c]:
            continue
        bnd_c = (c[0], c[1], c[n-2], c[n-1])
        bnd_s = (s[0], s[1], s[n-2], s[n-1])
        state_c = (bnd_c, g[c])
        state_s = (bnd_s, g[s])
        if state_c != state_s:
            bg_adj[state_c].add(state_s)
            bg_states.add(state_c)
            bg_states.add(state_s)

    # Check (boundary, g) automaton for cycles
    color = {b: WHITE for b in bg_states}
    bg_has_cycle = False
    for start in bg_states:
        if color[start] != WHITE:
            continue
        stack_dfs = [(start, iter(bg_adj.get(start, set())))]
        color[start] = GRAY
        while stack_dfs:
            node, children = stack_dfs[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    bg_has_cycle = True
                    break
                if color[child] == WHITE:
                    color[child] = GRAY
                    stack_dfs.append((child, iter(bg_adj.get(child, set()))))
            except StopIteration:
                color[node] = BLACK
                stack_dfs.pop()
        if bg_has_cycle:
            break

    print(f"\n(boundary, g) automaton at n={n}: {len(bg_states)} states, "
          f"DAG: {'YES' if not bg_has_cycle else 'NO'}")

    # Build (boundary, fc) transitions
    bfc_adj = defaultdict(set)
    bfc_states = set()
    for c, s, pos, dfc in tp_edge_list:
        if phi[s] != phi[c]:
            continue
        bnd_c = (c[0], c[1], c[n-2], c[n-1])
        bnd_s = (s[0], s[1], s[n-2], s[n-1])
        state_c = (bnd_c, fc_cache[c])
        state_s = (bnd_s, fc_cache[s])
        if state_c != state_s:
            bfc_adj[state_c].add(state_s)
            bfc_states.add(state_c)
            bfc_states.add(state_s)

    # Check (boundary, fc) automaton
    color = {b: WHITE for b in bfc_states}
    bfc_has_cycle = False
    for start in bfc_states:
        if color[start] != WHITE:
            continue
        stack_dfs = [(start, iter(bfc_adj.get(start, set())))]
        color[start] = GRAY
        while stack_dfs:
            node, children = stack_dfs[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    bfc_has_cycle = True
                    break
                if color[child] == WHITE:
                    color[child] = GRAY
                    stack_dfs.append((child, iter(bfc_adj.get(child, set()))))
            except StopIteration:
                color[node] = BLACK
                stack_dfs.pop()
        if bfc_has_cycle:
            break

    print(f"(boundary, fc) automaton at n={n}: {len(bfc_states)} states, "
          f"DAG: {'YES' if not bfc_has_cycle else 'NO'}")

    # Check (boundary, g, fc) = (boundary, g, Φ-g) → equivalent to (boundary, Φ, g)
    # Since Φ is constant within constant edges within a Φ-level, and g = Φ - fc:
    # (boundary, fc) = (boundary, g) on constant-Φ edges. So both should give same result.

    # Build (boundary, c[2]) transitions — include next-to-boundary position
    b2_adj = defaultdict(set)
    b2_states = set()
    for c, s, pos, dfc in tp_edge_list:
        if phi[s] != phi[c]:
            continue
        state_c = (c[0], c[1], c[2], c[n-2], c[n-1])
        state_s = (s[0], s[1], s[2], s[n-2], s[n-1])
        if state_c != state_s:
            b2_adj[state_c].add(state_s)
            b2_states.add(state_c)
            b2_states.add(state_s)

    color = {b: WHITE for b in b2_states}
    b2_has_cycle = False
    for start in b2_states:
        if color[start] != WHITE:
            continue
        stack_dfs = [(start, iter(b2_adj.get(start, set())))]
        color[start] = GRAY
        while stack_dfs:
            node, children = stack_dfs[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    b2_has_cycle = True
                    break
                if color[child] == WHITE:
                    color[child] = GRAY
                    stack_dfs.append((child, iter(b2_adj.get(child, set()))))
            except StopIteration:
                color[node] = BLACK
                stack_dfs.pop()
        if b2_has_cycle:
            break

    print(f"(bnd, c[2]) automaton at n={n}: {len(b2_states)} states, "
          f"DAG: {'YES' if not b2_has_cycle else 'NO'}")

    # Build (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1]) transitions
    b3_adj = defaultdict(set)
    b3_states = set()
    for c, s, pos, dfc in tp_edge_list:
        if phi[s] != phi[c]:
            continue
        state_c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
        state_s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
        if state_c != state_s:
            b3_adj[state_c].add(state_s)
            b3_states.add(state_c)
            b3_states.add(state_s)

    color = {b: WHITE for b in b3_states}
    b3_has_cycle = False
    for start in b3_states:
        if color[start] != WHITE:
            continue
        stack_dfs = [(start, iter(b3_adj.get(start, set())))]
        color[start] = GRAY
        while stack_dfs:
            node, children = stack_dfs[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    b3_has_cycle = True
                    break
                if color[child] == WHITE:
                    color[child] = GRAY
                    stack_dfs.append((child, iter(b3_adj.get(child, set()))))
            except StopIteration:
                color[node] = BLACK
                stack_dfs.pop()
        if b3_has_cycle:
            break

    print(f"(c[0..2], c[n-3..n-1]) automaton at n={n}: {len(b3_states)} states, "
          f"DAG: {'YES' if not b3_has_cycle else 'NO'}")

    # Also check: within each boundary state, is the INTERIOR-ONLY subgraph a DAG?
    # Interior edges: positions 3..n-3 (boundary unchanged)
    print(f"\n{'='*70}")
    print(f"INTERIOR-ONLY subgraph analysis (within each boundary state, n={n})")
    interior_edges_by_bnd = defaultdict(list)
    for c, s, pos, dfc in tp_edge_list:
        if phi[s] != phi[c]:
            continue
        if 3 <= pos <= n-3:
            bnd = (c[0], c[1], c[n-2], c[n-1])
            interior_edges_by_bnd[bnd].append((c, s, pos, dfc))

    # Also include position 2 edges that don't change boundary
    for c, s, pos, dfc in tp_edge_list:
        if phi[s] != phi[c]:
            continue
        if pos == 2:
            bnd_c = (c[0], c[1], c[n-2], c[n-1])
            bnd_s = (s[0], s[1], s[n-2], s[n-1])
            if bnd_c == bnd_s:
                interior_edges_by_bnd[bnd_c].append((c, s, pos, dfc))

    max_int_rank = 0
    for bnd in sorted(interior_edges_by_bnd.keys()):
        edges = interior_edges_by_bnd[bnd]
        adj = defaultdict(list)
        nodes = set()
        for c, s, pos, dfc in edges:
            adj[c].append(s)
            nodes.add(c)
            nodes.add(s)

        # DAG check
        color = {c: WHITE for c in nodes}
        is_dag = True
        for start in nodes:
            if color[start] != WHITE:
                continue
            stk = [(start, iter(adj.get(start, [])))]
            color[start] = GRAY
            while stk:
                nd, ch = stk[-1]
                try:
                    child = next(ch)
                    if color[child] == GRAY:
                        is_dag = False
                        break
                    if color[child] == WHITE:
                        color[child] = GRAY
                        stk.append((child, iter(adj.get(child, []))))
                except StopIteration:
                    color[nd] = BLACK
                    stk.pop()
            if not is_dag:
                break

        # Rank
        out_deg = {c: len(adj.get(c, [])) for c in nodes}
        sinks = [c for c in nodes if out_deg[c] == 0]
        rank = {c: 0 for c in sinks}
        radj = defaultdict(list)
        for c in nodes:
            for s in adj.get(c, []):
                radj[s].append(c)
        q = deque(sinks)
        while q:
            s = q.popleft()
            for c in radj.get(s, []):
                new_r = rank[s] + 1
                if c not in rank or new_r > rank[c]:
                    rank[c] = new_r
                    q.append(c)
        mrank = max(rank.values()) if rank else 0
        max_int_rank = max(max_int_rank, mrank)

        if len(edges) >= 20:
            print(f"  bnd={bnd}: {len(edges)} edges, {len(nodes)} nodes, "
                  f"DAG: {'YES' if is_dag else 'NO'}, rank={mrank}")

    print(f"\n  MAX interior rank across all boundaries: {max_int_rank}")

    elapsed = time.time() - t0
    print(f"  Time: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
