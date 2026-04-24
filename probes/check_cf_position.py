#!/usr/bin/env python3
"""Check: for CF edges, is the move at boundary or interior?
Does every CF edge fall into: (a) boundary (6-tuple changes) or (b) interior + fc preserved?"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])
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

def six_tuple(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def main():
    sys.stdout.reconfigure(line_buffering=True)
    for n_val in [5, 7, 10, 12]:
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 500000:
            print(f"  n={n}: skipping")
            continue

        fc_cache = {c: fc(c, n) for c in bad_list}

        # Build TP edges and compute FutureFc
        tp_edges = []
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
                            tp_edges.append((c, succ, i, dfc))

        tp_fwd = defaultdict(list)
        tp_nodes = set()
        for c, s, pos, dfc in tp_edges:
            tp_fwd[c].append((s, dfc))
            tp_nodes.add(c)
            tp_nodes.add(s)

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

        phi = {c: fc_cache.get(c, fc(c, n)) + g.get(c, 0) for c in tp_nodes}

        cf_edges = [(c, s, pos, dfc) for c, s, pos, dfc in tp_edges
                     if phi.get(s, 0) == phi.get(c, 0)]

        # Classify CF edges
        boundary_6t_change = 0  # boundary move, 6-tuple changes
        interior_fc_zero = 0    # interior, fc preserved
        interior_fc_nonzero = 0 # interior, fc changes
        boundary_6t_same = 0    # boundary move, 6-tuple SAME (shouldn't happen for privileged)

        for c, s, pos, dfc in cf_edges:
            is_boundary = (pos <= 2 or pos >= n - 3)
            st_c = six_tuple(c, n)
            st_s = six_tuple(s, n)
            six_changed = (st_c != st_s)

            if is_boundary:
                if six_changed:
                    boundary_6t_change += 1
                else:
                    boundary_6t_same += 1
            else:
                if dfc == 0:
                    interior_fc_zero += 1
                else:
                    interior_fc_nonzero += 1

        print(f"\nn={n}: {len(cf_edges)} CF edges")
        print(f"  Boundary + 6-tuple changes: {boundary_6t_change}")
        print(f"  Boundary + 6-tuple SAME: {boundary_6t_same}")
        print(f"  Interior + fc=0: {interior_fc_zero}")
        print(f"  Interior + fc≠0: {interior_fc_nonzero}")

if __name__ == '__main__':
    main()
