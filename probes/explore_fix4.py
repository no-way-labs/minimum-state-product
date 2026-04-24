#!/usr/bin/env python3
"""
Check if the 494-edge DAG rank decreases on ALL 617 edges (including the 123 always-fc-down ones).
If so, we can just use the 494-edge rank as a drop-in replacement.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

n = 9; ms, fs = build_system(n); N = 1
for m in ms: N *= m

def idx_to_config(idx):
    c = []
    for m in reversed(ms):
        c.append(idx % m); idx //= m
    return tuple(reversed(c))
def config_to_idx(c):
    idx = 0
    for j in range(n): idx = idx * ms[j] + c[j]
    return idx
def move(c, pos):
    L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
    c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def tp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)
def boundary6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

bad_set = set(); tp_adj = {}
for i in range(N):
    if fc(idx_to_config(i)) > 0: bad_set.add(i); tp_adj[i] = []
for i in bad_set:
    c = idx_to_config(i); t = tp(c)
    for p in range(n):
        c2 = move(c, p); j = config_to_idx(c2)
        if c2 != c and j in bad_set and tp(c2) == t: tp_adj[i].append(j)

phi_full = {i: fc(idx_to_config(i)) for i in bad_set}
tp_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in tp_adj[i]: tp_rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad_set:
        for i in tp_rev[j]:
            if phi_full[j] > phi_full[i]: phi_full[i] = phi_full[j]; changed = True

future_fc = {i: fc(idx_to_config(i)) for i in bad_set}
all_adj = {i: [] for i in bad_set}
for i in bad_set:
    c = idx_to_config(i)
    for p in range(n):
        c2 = move(c, p); j = config_to_idx(c2)
        if c2 != c and j in bad_set: all_adj[i].append(j)
all_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in all_adj[i]: all_rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad_set:
        for i in all_rev[j]:
            if future_fc[j] > future_fc[i]: future_fc[i] = future_fc[j]; changed = True

# Classify 617 edges
edge_fc_class = {}  # edge -> set of fc directions
for i in bad_set:
    for j in tp_adj[i]:
        if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
            c, c2 = idx_to_config(i), idx_to_config(j)
            b1, b2 = boundary6(c), boundary6(c2)
            if b1 != b2:
                edge = (b1, b2)
                d = fc(c2) - fc(c)
                if edge not in edge_fc_class: edge_fc_class[edge] = set()
                if d > 0: edge_fc_class[edge].add("up")
                elif d == 0: edge_fc_class[edge].add("same")
                else: edge_fc_class[edge].add("down")

always_down = {e for e, d in edge_fc_class.items() if d == {"down"}}
rest_edges = set(edge_fc_class.keys()) - always_down

# Compute rank on 494-edge DAG
adj494 = defaultdict(set)
nodes494 = set()
for a, b in rest_edges:
    adj494[a].add(b); nodes494.add(a); nodes494.add(b)
# Add isolated nodes from always-down edges
for a, b in always_down:
    nodes494.add(a); nodes494.add(b)

out_deg = {c: len(adj494.get(c, set())) for c in nodes494}
sinks = [c for c in nodes494 if out_deg.get(c, 0) == 0]
rank494 = {c: 0 for c in sinks}
radj = defaultdict(list)
for c in nodes494:
    for s in adj494.get(c, set()):
        if s in nodes494: radj[s].append(c)
q = deque(sinks)
while q:
    s = q.popleft()
    for c in radj.get(s, []):
        new_r = rank494[s] + 1
        if c not in rank494 or new_r > rank494[c]:
            rank494[c] = new_r; q.append(c)

print("494-edge DAG rank check on ALL 617 edges:")
violations = 0
for edge in edge_fc_class:
    a, b = edge
    ra = rank494.get(a, 0)
    rb = rank494.get(b, 0)
    if ra <= rb:
        violations += 1
        print(f"  VIOLATION: {a} (rank {ra}) → {b} (rank {rb}), fc_class={edge_fc_class[edge]}")
        # Check if this is an always-down edge
        if edge in always_down:
            print(f"    (this is an always-fc-down edge)")

print(f"\nTotal violations: {violations}")
if violations == 0:
    print("✓ 494-edge DAG rank drops on ALL 617 edges!")
    print("  Just use this rank as a DROP-IN replacement for sixStateRank!")
    max_rank = max(rank494.get(s, 0) for s in range(324))
    print(f"  Max rank: {max_rank}")

    # Output new rank values
    new_ranks = [rank494.get(s, 0) for s in range(324)]
    print(f"\n  New rank values for Lean ({max_rank} max):")
    for i in range(0, 324, 18):
        chunk = new_ranks[i:i+18]
        print("    " + ", ".join(str(v) for v in chunk) + ",")

    # Also output new edge list
    sorted_edges = sorted(rest_edges)
    print(f"\n  New edge list ({len(sorted_edges)} edges):")
    edge_strs = [f"({a}, {b})" for a, b in sorted_edges]
    for i in range(0, len(edge_strs), 10):
        print("    " + ", ".join(edge_strs[i:i+10]) + ",")
else:
    print(f"\n✗ 494-edge DAG rank does NOT decrease on all 617 edges.")
    print("  Need a different approach for the always-fc-down edges.")

    # For the violating edges, can we show fc drops?
    print("\n  Checking: are all violating edges always-fc-down?")
    all_viol_down = True
    for edge in edge_fc_class:
        a, b = edge
        ra = rank494.get(a, 0)
        rb = rank494.get(b, 0)
        if ra <= rb:
            if edge not in always_down:
                all_viol_down = False
                print(f"    NOT always-down: {a} → {b}, class={edge_fc_class[edge]}")

    if all_viol_down:
        print("  ✓ All violations are on always-fc-down edges!")
        print("  → Can use (fc, rank494) lex: fc handles always-down, rank handles rest")
        print()
        # But wait, fc can go UP on rest edges. Check if rank494 handles those.
        print("  Double-check: rank494 drops on all non-always-down edges?")
        rest_viols = 0
        for edge in rest_edges:
            a, b = edge
            ra = rank494.get(a, 0)
            rb = rank494.get(b, 0)
            if ra <= rb:
                rest_viols += 1
                print(f"    VIOLATION: {a}→{b}, ranks {ra}→{rb}, class={edge_fc_class[edge]}")
        print(f"  Rest violations: {rest_viols}")

        # The real question: on always-down edges, does fc ALWAYS decrease at full-config level?
        # We already know this from explore_fix2.py - all instances have fc_down.
        # But in Lean, we need to PROVE this from the boundary values alone.
        # Let's check: for each always-down 6-tuple edge, what are the possible mover positions?
        print("\n  Always-down edge analysis (what proves fc drop at boundary level):")
        for edge in sorted(always_down)[:5]:
            a, b = edge
            # Find the full-config instances
            instances = []
            for i in bad_set:
                for j in tp_adj[i]:
                    if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
                        c, c2 = idx_to_config(i), idx_to_config(j)
                        if boundary6(c) == a and boundary6(c2) == b:
                            # Find mover position
                            for p in range(n):
                                c3 = move(c, p)
                                if c3 == c2:
                                    instances.append((c, c2, p, fc(c), fc(c2)))
                                    break
            movers = set(inst[2] for inst in instances)
            fc_deltas = set(inst[4]-inst[3] for inst in instances)
            print(f"    {a}→{b}: movers={movers}, fc_deltas={fc_deltas}, instances={len(instances)}")

print("\nDONE")
