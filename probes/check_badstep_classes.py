#!/usr/bin/env python3
"""
Check: for every bad step c→c', exactly one of:
1. FutureFc(c') < FutureFc(c) (Drop)
2. FutureFc(c') = FutureFc(c) AND nonneg_measure(c') < nonneg_measure(c) (CF+nonneg)
3. FutureFc(c') = FutureFc(c) AND fc(c') < fc(c) (CF+neg)

Note: FutureFc is defined within TP subgraph (TP-preserving steps only).
Bad steps that DON'T preserve TP: what happens to FutureFc?
Answer: FutureFc drops because TP quantities are monotone (they can only decrease/stay).
Any bad step preserves or decreases TP. If TP changes, reachable set shrinks, so FutureFc can only drop.

Actually, FutureFc is defined via ALL bad-reachable configs, not just TP-reachable.
But the three monotone quantities (TP) mean that the TP-subgraph captures all the structure.

Let me just verify: on EVERY bad step, either FutureFc drops OR nonneg_measure decreases.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def frontier_type(a, b):
    if a == b: return 0
    return (b + 3 - a) % 3

def w1(n, j):
    if j + 1 == n: return 0
    if j + 2 == n: return 1
    return j + 1

def w2(n, j):
    if j + 1 == n: return 0
    if j == 0: return n - 1
    return n - 1 - j

def psi_weight(n, j, a, b):
    if a == b: return 0
    ft = frontier_type(a, b)
    return w1(n, j) if ft == 1 else w2(n, j)

def psi(c, n):
    return sum(psi_weight(n, j, c[j], c[(j+1) % n]) for j in range(n))

def nonneg_measure(c, n):
    return (n - fc(c, n), psi(c, n))

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

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [5, 6, 7, 8, 9, 10]:
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 200000:
            print(f"  n={n}: skipping ({len(bad_list)} bad)")
            continue

        # Build ALL bad-step edges
        fc_cache = {}
        all_bad_edges = []
        for c in bad_list:
            fc_cache[c] = fc(c, n)
        for c in bad_list:
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        if succ not in fc_cache:
                            fc_cache[succ] = fc(succ, n)
                        all_bad_edges.append((c, succ, i))

        # Compute FutureFc via full bad-step reachability
        # BFS/DFS from each config
        bad_adj = defaultdict(list)
        for c, s, i in all_bad_edges:
            bad_adj[c].append(s)

        # Compute FutureFc = max fc reachable from c via bad steps
        # Use reverse BFS: for each config with high fc, propagate to predecessors
        # Actually, compute max reachable fc via iterative relaxation
        future_fc = {c: fc_cache[c] for c in bad_list}
        changed = True
        iters = 0
        while changed:
            changed = False
            iters += 1
            for c in bad_list:
                for s in bad_adj.get(c, []):
                    if future_fc.get(s, 0) > future_fc.get(c, 0):
                        future_fc[c] = future_fc[s]
                        changed = True
            if iters > 100:
                break

        # Check each bad step
        class1 = 0  # FutureFc drops
        class2 = 0  # CF + nonneg_measure drops
        class3 = 0  # CF + fc drops
        unclassified = 0

        for c, s, i in all_bad_edges:
            phi_c = future_fc.get(c, 0)
            phi_s = future_fc.get(s, 0)

            if phi_s < phi_c:
                class1 += 1
            elif phi_s == phi_c:
                nm_c = nonneg_measure(c, n)
                nm_s = nonneg_measure(s, n)
                if nm_s < nm_c:
                    class2 += 1
                elif fc_cache[s] < fc_cache[c]:
                    class3 += 1
                else:
                    unclassified += 1
            else:
                # phi_s > phi_c should be impossible
                unclassified += 1

        elapsed = time.time() - t0
        total = len(all_bad_edges)
        print(f"n={n}: {total} bad edges ({elapsed:.1f}s)")
        print(f"  Drop: {class1}, CF+nonneg: {class2}, CF+neg: {class3}, UNCLASSIFIED: {unclassified}")
        if unclassified:
            # Show a few examples
            count = 0
            for c, s, i in all_bad_edges:
                phi_c = future_fc.get(c, 0)
                phi_s = future_fc.get(s, 0)
                if phi_s == phi_c:
                    nm_c = nonneg_measure(c, n)
                    nm_s = nonneg_measure(s, n)
                    if nm_s >= nm_c and fc_cache[s] >= fc_cache[c]:
                        print(f"    Example: {c}->{s} pos={i}")
                        print(f"      fc: {fc_cache[c]}->{fc_cache[s]}, nm: {nm_c}->{nm_s}")
                        print(f"      phi: {phi_c}->{phi_s}")
                        count += 1
                        if count >= 3: break

if __name__ == '__main__':
    main()
