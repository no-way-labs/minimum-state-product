#!/usr/bin/env python3
"""
Check: on Drop steps (FutureFc drops), does nonneg_measure decrease?
And more importantly: on ALL bad steps, does (FutureFc, nonneg_measure) Lex-decrease?
OR does (FutureFc, fc, nonneg_measure) with some order work?
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict

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

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [5, 6, 7, 8, 9, 10]:
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 200000:
            print(f"  n={n}: skipping")
            continue

        fc_cache = {c: fc(c, n) for c in bad_list}

        bad_adj = defaultdict(list)
        all_bad_edges = []
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
                        bad_adj[c].append(succ)

        # Compute FutureFc
        future_fc = {c: fc_cache[c] for c in bad_list}
        changed = True
        while changed:
            changed = False
            for c in bad_list:
                for s in bad_adj.get(c, []):
                    if future_fc.get(s, 0) > future_fc.get(c, 0):
                        future_fc[c] = future_fc[s]
                        changed = True

        # Check (FutureFc, nonneg_measure) Lex
        phi_nm_ok = 0
        phi_nm_fail = 0
        phi_nm_fail_examples = []

        # Check (FutureFc, fc descending) — i.e., fc going DOWN is good
        # Lex: FutureFc first, then fc REVERSED (higher fc = smaller in order)
        # Actually: (FutureFc, -(fc)) or (FutureFc, max_fc - fc)

        for c, s, i in all_bad_edges:
            phi_c = future_fc.get(c, 0)
            phi_s = future_fc.get(s, 0)
            nm_c = nonneg_measure(c, n)
            nm_s = nonneg_measure(s, n)

            # (phi, nm) Lex decreasing?
            if phi_s < phi_c:
                phi_nm_ok += 1
            elif phi_s == phi_c and nm_s < nm_c:
                phi_nm_ok += 1
            else:
                phi_nm_fail += 1
                if len(phi_nm_fail_examples) < 3:
                    phi_nm_fail_examples.append((c, s, i, phi_c, phi_s, nm_c, nm_s))

        print(f"\nn={n}: {len(all_bad_edges)} bad edges")
        print(f"  (FutureFc, NonnegMeasure) Lex: {phi_nm_ok} ok, {phi_nm_fail} fail")

        if phi_nm_fail:
            # These should be CF+neg steps. Check if (phi, fc) with fc DESCENDING handles them
            # i.e., Lex (phi DESC, fc DESC)
            # Or: (phi, n-fc, psi) but n-fc goes up on neg...
            # Check: (phi, fc) with fc going DOWN = good
            phi_fc_ok = 0
            phi_fc_fail = 0
            for c, s, i in all_bad_edges:
                phi_c = future_fc.get(c, 0)
                phi_s = future_fc.get(s, 0)
                if phi_s < phi_c:
                    phi_fc_ok += 1
                elif phi_s == phi_c and fc_cache[s] < fc_cache[c]:
                    phi_fc_ok += 1
                else:
                    phi_fc_fail += 1
            print(f"  (FutureFc, fc DESC) Lex: {phi_fc_ok} ok, {phi_fc_fail} fail")

            # The fail cases for BOTH: CF steps where nonneg_measure doesn't decrease AND fc doesn't decrease
            # Those would be CF+nonneg where fc stays and psi stays... impossible since nonneg_measure strictly decreases

            for c, s, i, pc, ps, nmc, nms in phi_nm_fail_examples:
                print(f"    Fail example: {c}->{s} pos={i}")
                print(f"      phi: {pc}->{ps}, nm: {nmc}->{nms}, fc: {fc_cache[c]}->{fc_cache[s]}")

if __name__ == '__main__':
    main()
