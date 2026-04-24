#!/usr/bin/env python3
"""
Check: within CF (constant FutureFc), is cup2TpInvariant Lex-non-increasing on every step?
Also check if there's ANY simple combined measure that works for ALL CF steps.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque

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

def psi(c, n):
    """Weighted frontier sum."""
    total = 0
    for j in range(n):
        if c[j] != c[(j + 1) % n]:
            total += j  # weight by position
    return total

def tp_tuple(c, n):
    return (exp2_count(c, n), int_21(c, n), exp2_weight(c, n))

def main():
    sys.stdout.reconfigure(line_buffering=True)
    print("=" * 70)
    print("CHECK: TP behavior on CF (constant-FutureFc) steps")
    print("=" * 70)

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
            print(f"  n={n}: skipping ({len(bad_list)} bad configs)")
            continue

        # Build TP-preserving edges
        fc_cache = {}
        tp_edges = []  # (c, succ, pos, dfc)
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

        # Compute FutureFc via TP graph
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

        # Extract CF edges (constant phi)
        cf_edges = [(c, s, pos, dfc) for c, s, pos, dfc in tp_edges
                     if phi.get(s, 0) == phi.get(c, 0)]

        # Check TP on CF edges
        tp_inc = 0
        tp_dec = 0
        tp_same = 0
        for c, s, pos, dfc in cf_edges:
            tp_c = tp_tuple(c, n)
            tp_s = tp_tuple(s, n)
            if tp_s < tp_c:
                tp_dec += 1
            elif tp_s > tp_c:
                tp_inc += 1
            else:
                tp_same += 1

        # Check nonneg_measure on CF edges
        nonneg_fail = 0
        nonneg_ok = 0
        for c, s, pos, dfc in cf_edges:
            nm_c = (n - fc_cache[c], psi(c, n))
            nm_s = (n - fc_cache[s], psi(s, n))
            if nm_s < nm_c:
                nonneg_ok += 1
            else:
                nonneg_fail += 1

        # Check if (TP_lex, nonneg_measure) as Lex works
        tp_then_nonneg_fail = 0
        for c, s, pos, dfc in cf_edges:
            tp_c = tp_tuple(c, n)
            tp_s = tp_tuple(s, n)
            if tp_s < tp_c:
                continue  # TP decreased, good
            elif tp_s == tp_c:
                nm_c = (n - fc_cache[c], psi(c, n))
                nm_s = (n - fc_cache[s], psi(s, n))
                if nm_s < nm_c:
                    continue  # TP same, nonneg decreased, good
            tp_then_nonneg_fail += 1

        elapsed = time.time() - t0
        print(f"\n  n={n}: {len(cf_edges)} CF edges ({elapsed:.1f}s)")
        print(f"    TP: {tp_dec} dec, {tp_same} same, {tp_inc} INC")
        print(f"    TP is constant on ALL CF edges: {tp_inc == 0 and tp_dec == 0}")
        print(f"    NonnegMeasure: {nonneg_ok} ok, {nonneg_fail} fail")
        print(f"    Lex(TP, NonnegMeasure) fail: {tp_then_nonneg_fail}")

    print("\n" + "=" * 70)
    print("DONE")

if __name__ == '__main__':
    main()
