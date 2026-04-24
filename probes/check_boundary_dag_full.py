#!/usr/bin/env python3
"""Check if the FULL boundary transition graph (all 1368 edges) is a DAG.
If yes, we can compute a universal rank function that bypasses FutureFc entirely.
If no, we need approach 1 (prove non-CF edges always drop FutureFc)."""

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

def encode(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1

# Build adjacency list
adj = {i: set() for i in range(324)}

for c0 in range(2):
  for c1 in range(3):
    for c2 in range(3):
      for cN3 in range(3):
        for cN2 in range(3):
          for cN1 in range(2):
            s = encode(c0, c1, c2, cN3, cN2, cN1)
            # P0
            new_c0 = TBotVal(cN1, c0, c1)
            if new_c0 != c0 and new_c0 < 2:
              adj[s].add(encode(new_c0, c1, c2, cN3, cN2, cN1))
            # P1
            new_c1 = TLowVal(c0, c1, c2)
            if new_c1 != c1 and new_c1 < 3:
              adj[s].add(encode(c0, new_c1, c2, cN3, cN2, cN1))
            # P2 (3 extras)
            for c3 in range(3):
              new_c2 = TMidVal(c1, c2, c3)
              if new_c2 != c2 and new_c2 < 3:
                adj[s].add(encode(c0, c1, new_c2, cN3, cN2, cN1))
            # PN3 (3 extras)
            for cn4 in range(3):
              new_cN3 = TMidVal(cn4, cN3, cN2)
              if new_cN3 != cN3 and new_cN3 < 3:
                adj[s].add(encode(c0, c1, c2, new_cN3, cN2, cN1))
            # PN2
            new_cN2 = THighVal(cN3, cN2, cN1)
            if new_cN2 != cN2 and new_cN2 < 3:
              adj[s].add(encode(c0, c1, c2, cN3, new_cN2, cN1))
            # PN1
            new_cN1 = TTopVal(cN2, cN1, c0)
            if new_cN1 != cN1 and new_cN1 < 2:
              adj[s].add(encode(c0, c1, c2, cN3, cN2, new_cN1))

total_edges = sum(len(v) for v in adj.values())
print(f"Total directed edges: {total_edges}")

# Tarjan's SCC to check for cycles
idx_counter = [0]
stack = []
lowlink = {}
index = {}
on_stack = set()
sccs = []

def strongconnect(v):
    index[v] = lowlink[v] = idx_counter[0]
    idx_counter[0] += 1
    stack.append(v)
    on_stack.add(v)

    for w in adj[v]:
        if w not in index:
            strongconnect(w)
            lowlink[v] = min(lowlink[v], lowlink[w])
        elif w in on_stack:
            lowlink[v] = min(lowlink[v], index[w])

    if lowlink[v] == index[v]:
        scc = []
        while True:
            w = stack.pop()
            on_stack.discard(w)
            scc.append(w)
            if w == v:
                break
        sccs.append(scc)

import sys
sys.setrecursionlimit(10000)
for v in range(324):
    if v not in index:
        strongconnect(v)

non_trivial_sccs = [scc for scc in sccs if len(scc) > 1]
self_loops = sum(1 for v in range(324) if v in adj[v])

print(f"\nSCCs with >1 node: {len(non_trivial_sccs)}")
print(f"Self-loops: {self_loops}")

if not non_trivial_sccs and self_loops == 0:
    print("\nThe full boundary transition graph IS a DAG!")

    # Compute topological rank (longest path from any source)
    # Use reverse topological order
    topo_order = []
    for scc in sccs:
        topo_order.extend(scc)
    topo_order.reverse()

    rank = {v: 0 for v in range(324)}
    for v in topo_order:
        for w in adj[v]:
            rank[w] = max(rank[w], rank[v] + 1)
    # Wait, we want rank to DECREASE. Let me use "longest path to any sink"
    # Actually, for WF we want: if edge (s, s'), then rank(s') < rank(s)
    # Since edges go from s to s' (s is source/old, s' is target/new),
    # we need rank to decrease along edges.
    # Use "longest path FROM v" as rank (longer = higher rank)

    # Reverse: compute longest path from each node
    # In topological order (reversed), compute longest path
    rank = {v: 0 for v in range(324)}
    for v in reversed(topo_order):
        for w in adj[v]:
            rank[v] = max(rank[v], rank[w] + 1)

    max_rank = max(rank.values())
    print(f"Max rank (longest path): {max_rank}")

    # Verify: every edge decreases rank
    violations = 0
    for v in range(324):
        for w in adj[v]:
            if rank[w] >= rank[v]:
                violations += 1
    print(f"Rank violations: {violations}")

    # Output the rank values for use in Lean
    print(f"\nRank values (324 entries, max {max_rank}):")
    rank_list = [rank[i] for i in range(324)]
    print(rank_list)

else:
    print("\nThe full boundary transition graph has CYCLES!")
    print(f"Largest non-trivial SCC size: {max(len(scc) for scc in non_trivial_sccs)}")
    for i, scc in enumerate(non_trivial_sccs[:5]):
        print(f"  SCC {i}: size {len(scc)}, nodes: {scc[:10]}...")

    # Check if the CF-only edges (617) are a DAG
    sixTupleEdgeVals = [(0, 6), (0, 162), (1, 0), (1, 7), (2, 164), (3, 1), (3, 9), (4, 166), (6, 8), (6, 168), (7, 6), (7, 9), (8, 170), (9, 11), (10, 16), (10, 172), (11, 17), (12, 174), (13, 12), (14, 176), (16, 4), (16, 178), (17, 5), (18, 24), (18, 180), (19, 18), (19, 25), (20, 182), (21, 19), (21, 27), (22, 184), (24, 26), (24, 186), (25, 24), (25, 27), (26, 188), (27, 29), (28, 34), (28, 190), (29, 35), (30, 192), (31, 30), (32, 194), (34, 22), (34, 196), (35, 23)]
    # (truncated for brevity - already verified as DAG in Lean)
    print("\n(CF-only 617 edges are a DAG — verified in Lean via sixStateRank)")

    # Let's find which edges cause cycles
    cycle_nodes = set()
    for scc in non_trivial_sccs:
        cycle_nodes.update(scc)

    # Decode a boundary state
    def decode(s):
        cN1 = s % 2; s //= 2
        cN2 = s % 3; s //= 3
        cN3 = s % 3; s //= 3
        c2 = s % 3; s //= 3
        c1 = s % 3; s //= 3
        c0 = s
        return (c0, c1, c2, cN3, cN2, cN1)

    print(f"\nNodes involved in cycles: {len(cycle_nodes)}")
    # Find a specific short cycle
    for scc in non_trivial_sccs:
        if len(scc) <= 5:
            print(f"\nSmall cycle SCC: {scc}")
            for v in scc:
                print(f"  {v} = {decode(v)}, successors in SCC: {[w for w in adj[v] if w in set(scc)]}")
            break
