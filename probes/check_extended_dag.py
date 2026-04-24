#!/usr/bin/env python3
"""Check if adding B4Unsafe edges to the 617-edge DAG preserves acyclicity."""

# Import the edge list from check_boundary_edges.py
from check_boundary_edges import sixTupleEdgeVals, encode, decode

# The 12 missing B4Unsafe edges
b4_unsafe_edges = []
for c1 in range(3):
    for c2 in range(3):
        for cN3 in range(3):
            src = encode(0, c1, c2, cN3, 2, 0)
            tgt = encode(0, c1, c2, cN3, 2, 1)
            if (src, tgt) not in set(sixTupleEdgeVals):
                b4_unsafe_edges.append((src, tgt))

print(f"B4Unsafe edges to add: {len(b4_unsafe_edges)}")
for s, t in b4_unsafe_edges:
    print(f"  ({s}, {t}): {decode(s)} → {decode(t)}")

# Build extended edge list
extended_edges = list(sixTupleEdgeVals) + b4_unsafe_edges
edge_set = set(extended_edges)

# Check DAG by topological sort
adj = {}
for s, t in extended_edges:
    adj.setdefault(s, []).append(t)

# DFS cycle detection
WHITE, GRAY, BLACK = 0, 1, 2
color = {}
all_nodes = set()
for s, t in extended_edges:
    all_nodes.add(s)
    all_nodes.add(t)

for n in all_nodes:
    color[n] = WHITE

is_dag = True
for start in all_nodes:
    if color[start] != WHITE:
        continue
    stack = [(start, iter(adj.get(start, [])))]
    color[start] = GRAY
    while stack:
        node, children = stack[-1]
        try:
            child = next(children)
            if color[child] == GRAY:
                print(f"CYCLE detected involving {child} ({decode(child)})")
                is_dag = False
                break
            if color[child] == WHITE:
                color[child] = GRAY
                stack.append((child, iter(adj.get(child, []))))
        except StopIteration:
            color[node] = BLACK
            stack.pop()
    if not is_dag:
        break

if is_dag:
    print(f"\nExtended DAG ({len(extended_edges)} edges) is ACYCLIC")

    # Compute rank
    rank = {}
    out_deg = {n: len(adj.get(n, [])) for n in all_nodes}
    sinks = [n for n in all_nodes if out_deg[n] == 0]
    for s in sinks:
        rank[s] = 0
    from collections import deque, defaultdict
    radj = defaultdict(list)
    for s, t in extended_edges:
        radj[t].append(s)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r
                q.append(c)
    max_rank = max(rank.values()) if rank else 0
    print(f"Max rank: {max_rank}")

    # Generate rank values for all 324 states
    rank_vals = [rank.get(i, 0) for i in range(324)]

    # Verify rank decrease on ALL extended edges
    violations = 0
    for s, t in extended_edges:
        if rank_vals[t] >= rank_vals[s]:
            violations += 1
            print(f"  VIOLATION: ({s},{t}) rank {rank_vals[s]} → {rank_vals[t]}")
    print(f"Rank violations: {violations}")

    if violations == 0:
        print("\nExtended rank values (for Lean):")
        print(f"  [{', '.join(str(r) for r in rank_vals)}]")
else:
    print("Extended DAG has CYCLES — cannot use this approach")
