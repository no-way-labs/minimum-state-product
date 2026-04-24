#!/usr/bin/env python3
"""Check if constant-FutureFc (CF) edges can be fc-decreasing."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict
import re

# Load lean edge set
path = os.path.join(os.path.dirname(__file__), '..', 'lean', 'LeanMn', 'Convergence', 'SixTuple.lean')
with open(path) as f:
    content = f.read()
m = re.search(r'def sixTupleEdgeVals.*?\[(.*?)\]', content, re.DOTALL)
pairs = re.findall(r'\((\d+),\s*(\d+)\)', m.group(1))
lean_edges = set((int(a), int(b)) for a, b in pairs)


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

for n_val in range(5, 13):
    ms, fs = build_system(n_val)
    n = n_val

    configs = list(cartesian(*[range(m) for m in ms]))
    # No good cycle filter needed - just check all bad-to-bad transitions
    fc_cache = {c: fc(c, n) for c in configs}

    tp_edges = []
    for c_tup in configs:
        c_list = list(c_tup)
        for i in range(n):
            L = c_list[(i - 1) % n]
            S = c_list[i]
            R = c_list[(i + 1) % n]
            new_val = fs[i](L, S, R)
            if new_val != S:
                s_list = list(c_list)
                s_list[i] = new_val
                s_tup = tuple(s_list)
                dfc = fc_cache[s_tup] - fc_cache[c_tup]
                tp_edges.append((c_tup, s_tup, i, dfc))

    tp_adj = defaultdict(list)
    tp_nodes = set()
    for c, s, pos, dfc in tp_edges:
        tp_adj[c].append(s)
        tp_nodes.add(c); tp_nodes.add(s)

    g = {c: 0 for c in tp_nodes}
    for _ in range(len(tp_nodes) + 1):
        changed = False
        for c in tp_nodes:
            for s in tp_adj.get(c, []):
                val = fc_cache[s] - fc_cache[c] + g[s]
                if val > g[c]:
                    g[c] = val
                    changed = True
        if not changed:
            break

    phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

    # Check: for nonneg boundary CF steps that change 6-tuple,
    # is the 6-tuple transition in the fc-nondec edge set?
    def encode6(c):
        c0, c1, c2, cN3, cN2, cN1 = c[0], c[1], c[2], c[n-3], c[n-2], c[n-1]
        return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1

    nonneg_boundary_changed = 0
    nonneg_boundary_changed_not_in_617 = 0
    for c, s, pos, dfc in tp_edges:
        if phi.get(s, 0) == phi.get(c, 0) and dfc >= 0:
            # nonneg CF step
            e_c = encode6(c)
            e_s = encode6(s)
            if e_c != e_s:
                # boundary changed
                nonneg_boundary_changed += 1
                if (e_c, e_s) not in lean_edges and (e_c, e_s) not in fc_nondec_edges:
                    nonneg_boundary_changed_not_in_617 += 1

    print(f'n={n}: nonneg+bnd_changed={nonneg_boundary_changed}, not_in_617={nonneg_boundary_changed_not_in_617}')
