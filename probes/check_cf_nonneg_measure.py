#!/usr/bin/env python3
"""
Check the CORRECT nonneg_measure = (n - fc, psi) using the Lean definition of psi.
On neg CF steps, n-fc increases (bad for Lex first component).
What about psi itself? Does it strictly decrease on neg CF steps?
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
    if a == b:
        return 0
    return (b + 3 - a) % 3

def w1(n, j):
    if j + 1 == n:
        return 0
    if j + 2 == n:
        return 1
    return j + 1

def w2(n, j):
    if j + 1 == n:
        return 0
    if j == 0:
        return n - 1
    return n - 1 - j

def psi_weight(n, j, a, b):
    if a == b:
        return 0
    ft = frontier_type(a, b)
    if ft == 1:
        return w1(n, j)
    return w2(n, j)

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

    for n_val in range(5, 13):
        t0 = time.time()
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

        # Build TP edges and FutureFc
        fc_cache = {}
        tp_edges = []
        for c in bad_list:
            fc_cache[c] = fc(c, n)
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

        nonneg_cf = [(c, s, pos, dfc) for c, s, pos, dfc in cf_edges if dfc >= 0]
        neg_cf = [(c, s, pos, dfc) for c, s, pos, dfc in cf_edges if dfc < 0]

        # Check nonneg_measure on nonneg CF
        nm_nonneg_ok = sum(1 for c, s, _, _ in nonneg_cf if nonneg_measure(s, n) < nonneg_measure(c, n))
        nm_nonneg_fail = len(nonneg_cf) - nm_nonneg_ok

        # Check nonneg_measure on neg CF
        nm_neg_ok = sum(1 for c, s, _, _ in neg_cf if nonneg_measure(s, n) < nonneg_measure(c, n))
        nm_neg_fail = len(neg_cf) - nm_neg_ok

        # On neg CF, check psi behavior specifically
        if neg_cf:
            psi_dec = sum(1 for c, s, _, _ in neg_cf if psi(s, n) < psi(c, n))
            psi_inc = sum(1 for c, s, _, _ in neg_cf if psi(s, n) > psi(c, n))
            psi_same = len(neg_cf) - psi_dec - psi_inc
            # Check nonneg_measure in REVERSE lex: (psi, n-fc)
            rev_ok = sum(1 for c, s, _, _ in neg_cf
                        if (psi(s,n), n-fc_cache[s]) < (psi(c,n), n-fc_cache[c]))
        else:
            psi_dec = psi_inc = psi_same = 0
            rev_ok = 0

        # On nonneg CF, check psi behavior
        nonneg_psi_dec = sum(1 for c, s, _, _ in nonneg_cf if psi(s, n) < psi(c, n))
        nonneg_psi_same = sum(1 for c, s, _, _ in nonneg_cf if psi(s, n) == psi(c, n))
        nonneg_psi_inc = sum(1 for c, s, _, _ in nonneg_cf if psi(s, n) > psi(c, n))

        elapsed = time.time() - t0
        print(f"\nn={n}: {len(cf_edges)} CF ({len(nonneg_cf)} nonneg, {len(neg_cf)} neg) [{elapsed:.1f}s]")
        print(f"  Nonneg CF: nonneg_measure Lex dec: {nm_nonneg_ok}/{len(nonneg_cf)}")
        print(f"  Nonneg CF: psi dec={nonneg_psi_dec}, same={nonneg_psi_same}, inc={nonneg_psi_inc}")
        if neg_cf:
            print(f"  Neg CF: nonneg_measure Lex dec: {nm_neg_ok}/{len(neg_cf)}")
            print(f"  Neg CF: psi dec={psi_dec}, same={psi_same}, inc={psi_inc}")
            print(f"  Neg CF: (psi, n-fc) Lex dec: {rev_ok}/{len(neg_cf)}")

if __name__ == '__main__':
    main()
