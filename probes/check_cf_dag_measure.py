#!/usr/bin/env python3
"""
CF is a DAG. Find what measure strictly decreases on CF edges.
Check: fc*K + psi for various K? Or DAG rank directly?
Also: check nonneg-CF vs neg-CF breakdown.
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
    total = 0
    for j in range(n):
        if c[j] != c[(j + 1) % n]:
            total += j
    return total

def main():
    sys.stdout.reconfigure(line_buffering=True)
    print("=" * 70)
    print("CF DAG measure search")
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
            print(f"  n={n}: skipping")
            continue

        # Build TP-preserving edges and compute FutureFc
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

        # CF edges
        cf_edges = [(c, s, pos, dfc) for c, s, pos, dfc in tp_edges
                     if phi.get(s, 0) == phi.get(c, 0)]

        # Compute DAG rank
        cf_adj = defaultdict(list)
        cf_nodes = set()
        for c, s, pos, dfc in cf_edges:
            cf_adj[c].append(s)
            cf_nodes.add(c)
            cf_nodes.add(s)

        out_deg = {c: len(cf_adj.get(c, [])) for c in cf_nodes}
        sinks = [c for c in cf_nodes if out_deg[c] == 0]
        rank = {c: 0 for c in sinks}
        radj = defaultdict(list)
        for c in cf_nodes:
            for s in cf_adj.get(c, []):
                radj[s].append(c)
        q = deque(sinks)
        while q:
            s = q.popleft()
            for c in radj.get(s, []):
                new_r = rank[s] + 1
                if c not in rank or new_r > rank[c]:
                    rank[c] = new_r
                    q.append(c)

        # Nonneg vs neg CF breakdown
        nonneg_cf = [(c, s) for c, s, pos, dfc in cf_edges if dfc >= 0]
        neg_cf = [(c, s) for c, s, pos, dfc in cf_edges if dfc < 0]

        # Check nonneg measure on nonneg CF
        nm_ok = 0
        nm_fail = 0
        for c, s in nonneg_cf:
            nm_c = (n - fc_cache[c], psi(c, n))
            nm_s = (n - fc_cache[s], psi(s, n))
            if nm_s < nm_c:
                nm_ok += 1
            else:
                nm_fail += 1

        # Check fc on neg CF
        fc_ok = sum(1 for c, s in neg_cf if fc_cache[s] < fc_cache[c])
        fc_fail = sum(1 for c, s in neg_cf if fc_cache[s] >= fc_cache[c])

        # Check rank strictly decreasing on ALL CF edges
        rank_ok = 0
        rank_fail = 0
        for c, s, pos, dfc in cf_edges:
            rc = rank.get(c, 0)
            rs = rank.get(s, 0)
            if rs < rc:
                rank_ok += 1
            else:
                rank_fail += 1

        max_rank = max(rank.values()) if rank else 0
        elapsed = time.time() - t0
        print(f"\n  n={n}: {len(cf_edges)} CF edges, rank={max_rank} ({elapsed:.1f}s)")
        print(f"    Nonneg CF: {len(nonneg_cf)} (nonneg_measure ok: {nm_ok}, fail: {nm_fail})")
        print(f"    Neg CF: {len(neg_cf)} (fc decreasing: {fc_ok}, fail: {fc_fail})")
        print(f"    DAG rank strictly dec on ALL: {rank_ok} ok, {rank_fail} fail")

        # Check: on neg CF edges, does nonneg_measure increase or what?
        if neg_cf:
            neg_nm_dec = 0
            neg_nm_inc = 0
            neg_nm_same = 0
            neg_fc_changes = defaultdict(int)
            for c, s in neg_cf:
                nm_c = (n - fc_cache[c], psi(c, n))
                nm_s = (n - fc_cache[s], psi(s, n))
                if nm_s < nm_c:
                    neg_nm_dec += 1
                elif nm_s > nm_c:
                    neg_nm_inc += 1
                else:
                    neg_nm_same += 1
                neg_fc_changes[fc_cache[c] - fc_cache[s]] += 1
            print(f"    Neg CF nonneg_measure: dec={neg_nm_dec}, same={neg_nm_same}, inc={neg_nm_inc}")
            print(f"    Neg CF fc_drop amounts: {dict(sorted(neg_fc_changes.items()))}")

    print("\n" + "=" * 70)

if __name__ == '__main__':
    main()
