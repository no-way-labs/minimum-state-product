#!/usr/bin/env python3
"""Check if Prod.Lex(sixStateRank, Psi) decreases on ALL privileged steps.
- Boundary fires: 6-tuple changes, need sixStateRank to decrease.
- Interior fires: 6-tuple unchanged, need Psi to decrease."""

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

# sixStateRankVals from SixTuple.lean (324 entries)
# I need to read these from the Lean file. Let me hard-code the encoding.
# SixBoundary encoding: c0 * 54 + c1 * 18 + c2 * 6 + cn3 * 2 + cn2 * ... hmm
# Actually, the encoding from check_boundary_dag.py:
# encode(c0, c1, c2, cN3, cN2, cN1) = ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1
# But SixTuple.lean might use a different encoding. Let me just compute the rank from the DAG.

def encode6(c0, c1, c2, cn3, cn2, cn1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cn3) * 3 + cn2) * 2 + cn1

def get_ms(n):
    ms = [3]*n; ms[0] = 2; ms[n-1] = 2; return ms

def get_trans(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

def frontierBitVal(a, b):
    return 0 if a == b else 1

def frontierTypeVal(a, b):
    if a == b: return 0
    return (b + 3 - a) % 3

def W1(n, j):
    if j + 1 == n: return 0
    if j + 2 == n: return 1
    return j + 1

def W2(n, j):
    if j + 1 == n: return 0
    if j == 0: return n - 1
    return n - 1 - j

def psiWeightVal(n, j, a, b):
    if a == b: return 0
    if frontierTypeVal(a, b) == 1: return W1(n, j)
    return W2(n, j)

def fc(config, n):
    return sum(frontierBitVal(config[j], config[(j+1)%n]) for j in range(n))

def psi(config, n):
    return sum(psiWeightVal(n, j, config[j], config[(j+1)%n]) for j in range(n))

def fire(config, n, i):
    ms = get_ms(n)
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    new_config = list(config); new_config[i] = new_S
    return tuple(new_config)

def get_6tuple(config, n):
    return (config[0], config[1], config[2], config[n-3], config[n-2], config[n-1])

def is_boundary_pos(n, i):
    return i <= 2 or i >= n-3

def build_6tuple_dag_rank():
    """Build DAG rank for 324-state 6-tuple automaton from check_boundary_dag.py"""
    adj = {i: set() for i in range(324)}
    for c0 in range(2):
      for c1 in range(3):
        for c2 in range(3):
          for cN3 in range(3):
            for cN2 in range(3):
              for cN1 in range(2):
                s = encode6(c0, c1, c2, cN3, cN2, cN1)
                # P0
                new_c0 = TBotVal(cN1, c0, c1)
                if new_c0 != c0 and new_c0 < 2:
                  adj[s].add(encode6(new_c0, c1, c2, cN3, cN2, cN1))
                # P1
                new_c1 = TLowVal(c0, c1, c2)
                if new_c1 != c1 and new_c1 < 3:
                  adj[s].add(encode6(c0, new_c1, c2, cN3, cN2, cN1))
                # P2 (3 extras)
                for c3 in range(3):
                  new_c2 = TMidVal(c1, c2, c3)
                  if new_c2 != c2 and new_c2 < 3:
                    adj[s].add(encode6(c0, c1, new_c2, cN3, cN2, cN1))
                # PN3 (3 extras)
                for cn4 in range(3):
                  new_cN3 = TMidVal(cn4, cN3, cN2)
                  if new_cN3 != cN3 and new_cN3 < 3:
                    adj[s].add(encode6(c0, c1, c2, new_cN3, cN2, cN1))
                # PN2
                new_cN2 = THighVal(cN3, cN2, cN1)
                if new_cN2 != cN2 and new_cN2 < 3:
                  adj[s].add(encode6(c0, c1, c2, cN3, new_cN2, cN1))
                # PN1
                new_cN1 = TTopVal(cN2, cN1, c0)
                if new_cN1 != cN1 and new_cN1 < 2:
                  adj[s].add(encode6(c0, c1, c2, cN3, cN2, new_cN1))

    # Check DAG
    # Tarjan's SCC
    import sys
    sys.setrecursionlimit(10000)
    idx_counter = [0]; stack = []; lowlink = {}; index = {}
    on_stack = set(); sccs = []
    def strongconnect(v):
        index[v] = lowlink[v] = idx_counter[0]; idx_counter[0] += 1
        stack.append(v); on_stack.add(v)
        for w in adj[v]:
            if w not in index:
                strongconnect(w); lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop(); on_stack.discard(w); scc.append(w)
                if w == v: break
            sccs.append(scc)
    for v in range(324):
        if v not in index: strongconnect(v)

    non_trivial = [s for s in sccs if len(s) > 1]
    self_loops = sum(1 for v in range(324) if v in adj[v])
    is_dag = len(non_trivial) == 0 and self_loops == 0
    print(f"6-tuple graph: DAG={is_dag}, non-trivial SCCs={len(non_trivial)}, self-loops={self_loops}")

    if not is_dag:
        print("WARNING: 6-tuple graph has cycles!")
        # Still compute rank for the DAG part
        # Use the RESTRICTED 617-edge set from SixTuple.lean
        return None, adj

    # Compute rank (longest path from each node)
    topo_order = []
    for scc in sccs:
        topo_order.extend(scc)
    topo_order.reverse()
    rank = {v: 0 for v in range(324)}
    for v in reversed(topo_order):
        for w in adj[v]:
            rank[v] = max(rank[v], rank[w] + 1)
    return rank, adj

rank, adj = build_6tuple_dag_rank()

if rank is None:
    print("Cannot check — 6-tuple graph has cycles.")
    print("Need to use the RESTRICTED 617-edge set from SixTuple.lean")
    print("Let me check the boundary TRANSITION rank instead.")

    # The 617-edge set in SixTuple.lean IS a DAG.
    # But the FULL boundary graph (all privileged boundary transitions) has cycles.
    # So sixStateRank from the 617-edge DAG doesn't decrease on ALL boundary transitions.
    # We need to handle non-617-edge boundary transitions differently.
    print("\nThe full boundary graph has cycles, so sixStateRank alone won't work.")
    print("Need a different approach for boundary fires not in the 617-edge set.")
else:
    max_rank = max(rank.values())
    print(f"Max rank: {max_rank}")

    # Now check: for each n, does Prod.Lex(sixStateRank, Psi) decrease on ALL steps?
    for n in [9, 10, 11]:
        print(f"\nn={n}:")
        ms = get_ms(n)
        from itertools import product as iproduct

        boundary_violations = 0
        interior_violations = 0
        total_boundary = 0
        total_interior = 0

        for config in iproduct(*[range(m) for m in ms]):
            old_6tuple = get_6tuple(config, n)
            old_rank = rank[encode6(*old_6tuple)]
            old_psi = psi(config, n)

            for i in range(n):
                new_config = fire(config, n, i)
                if new_config is None:
                    continue

                new_6tuple = get_6tuple(new_config, n)
                new_rank = rank[encode6(*new_6tuple)]
                new_psi = psi(new_config, n)

                if is_boundary_pos(n, i):
                    total_boundary += 1
                    if new_6tuple != old_6tuple:
                        # 6-tuple changed: need rank to decrease
                        if new_rank >= old_rank:
                            boundary_violations += 1
                            if boundary_violations <= 3:
                                print(f"  BOUNDARY RANK VIOLATION: pos {i}, {config}")
                                print(f"    6-tuple: {old_6tuple} -> {new_6tuple}, rank: {old_rank} -> {new_rank}")
                    else:
                        # Boundary fire but 6-tuple unchanged (shouldn't happen for n>=9)
                        print(f"  WARNING: boundary fire at {i} but 6-tuple unchanged!")
                else:
                    total_interior += 1
                    # Interior fire: 6-tuple preserved, need Psi to decrease
                    if new_psi >= old_psi:
                        interior_violations += 1
                        if interior_violations <= 5:
                            print(f"  INTERIOR PSI VIOLATION: pos {i}, {config}")
                            print(f"    psi: {old_psi} -> {new_psi}, fc: {fc(config,n)} -> {fc(new_config,n)}")

        print(f"  Boundary: {total_boundary} fires, {boundary_violations} rank violations")
        print(f"  Interior: {total_interior} fires, {interior_violations} Psi violations")
