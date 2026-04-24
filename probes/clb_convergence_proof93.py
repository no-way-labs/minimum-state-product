#!/usr/bin/env python3
"""
CONVERGENCE PROOF 93: DAG rank decomposition + leftward chain theorem
=====================================================================
Key insight from proof92: interior TP entries are ALL copy_L or copy_R.
If position j>=3 fires in TP, it needs specific L=c[j-1], meaning j-1 must
change => j-1 fires too. This creates a LEFTWARD CHAIN: if j fires, then
j-1 fires, then j-2, ..., down to position 2.

Test: can the DAG rank be decomposed as a function of
  (fc, boundary state, wavefront positions, agreement count)?

Also: check whether the Δfc=0 interior subgraph alone has any cycles.
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system, T_mid
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque


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

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 11):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP edges
        tp_adj = defaultdict(list)
        tp_radj = defaultdict(list)
        tp_nodes = set()
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
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            tp_adj[c].append(succ)
                            tp_radj[succ].append(c)
                            tp_nodes.add(c)
                            tp_nodes.add(succ)
                            tp_edges.append((c, succ, i))

        for c in bad_list:
            tp_nodes.add(c)

        # Compute DAG rank
        out_deg = {c: len(tp_adj.get(c, [])) for c in tp_nodes}
        sinks = [c for c in tp_nodes if out_deg[c] == 0]
        rank = {c: 0 for c in sinks}
        q = deque(sinks)
        while q:
            c = q.popleft()
            for p in tp_radj.get(c, []):
                new_r = rank[c] + 1
                if p not in rank or new_r > rank[p]:
                    rank[p] = new_r
                    q.append(p)

        max_rank = max(rank.values()) if rank else 0
        elapsed = time.time() - t0

        print(f"\n{'='*70}")
        print(f"n={n}: max rank = {max_rank} ({elapsed:.1f}s)")

        # Test various candidate potentials
        # 1. fc alone
        viol_fc = sum(1 for c, s, _ in tp_edges if fc(s, n) >= fc(c, n))
        print(f"  fc non-increasing: {len(tp_edges) - viol_fc}/{len(tp_edges)} "
              f"({viol_fc} violations)")

        # 2. -agreement_count (want to increase)
        def agree(c):
            return sum(1 for j in range(3, n - 2) if c[j] == c[j - 1])
        viol_ag = sum(1 for c, s, _ in tp_edges if agree(s) < agree(c))
        print(f"  agree non-decreasing: {len(tp_edges) - viol_ag}/{len(tp_edges)}")

        # 3. Interior sum Σ c[j] for j in [2,n-2]
        def int_sum(c):
            return sum(c[j] for j in range(2, n - 2))
        viol_is = sum(1 for c, s, _ in tp_edges if int_sum(s) >= int_sum(c))
        print(f"  int_sum decreasing: {len(tp_edges) - viol_is}/{len(tp_edges)}")

        # 4. Count of value 2 in interior
        def cnt2(c):
            return sum(1 for j in range(2, n - 2) if c[j] == 2)
        viol_c2 = sum(1 for c, s, _ in tp_edges if cnt2(s) >= cnt2(c))
        print(f"  cnt2 decreasing: {len(tp_edges) - viol_c2}/{len(tp_edges)}")

        # 5. Count of value 0 in interior
        def cnt0(c):
            return sum(1 for j in range(2, n - 2) if c[j] == 0)
        viol_c0 = sum(1 for c, s, _ in tp_edges if cnt0(s) <= cnt0(c))
        print(f"  cnt0 non-decreasing: {len(tp_edges) - viol_c0}/{len(tp_edges)}")

        # 6. "Wavefront" = Σ j * [c[j] ≠ c[j-1]] for j in [3,n-3]
        def wavefront(c):
            return sum(j for j in range(3, n - 2) if c[j] != c[j - 1])
        viol_wf = sum(1 for c, s, _ in tp_edges if wavefront(s) >= wavefront(c))
        print(f"  wavefront decreasing: {len(tp_edges) - viol_wf}/{len(tp_edges)}")

        viol_wf2 = sum(1 for c, s, _ in tp_edges if wavefront(s) <= wavefront(c))
        print(f"  wavefront increasing: {len(tp_edges) - viol_wf2}/{len(tp_edges)}")

        # 7. Lex(-fc, wavefront) — fc decreasing, then wavefront
        viol_lex = 0
        for c, s, _ in tp_edges:
            key_c = (-fc(c, n), wavefront(c))
            key_s = (-fc(s, n), wavefront(s))
            if key_s >= key_c:
                viol_lex += 1
        print(f"  lex(fc_desc, wavefront_desc): {viol_lex} violations")

        # 8. Lex(-fc, -agree)
        viol_lex2 = 0
        for c, s, _ in tp_edges:
            key_c = (-fc(c, n), -agree(c))
            key_s = (-fc(s, n), -agree(s))
            if key_s >= key_c:
                viol_lex2 += 1
        print(f"  lex(fc_desc, agree_asc): {viol_lex2} violations")

        # 9. Weighted combo: try to find a*fc + b*agree + c*wavefront
        # Use DAG rank as target, fit coefficients
        if len(rank) > 10:
            from numpy import array, linalg
            data = []
            for c in rank:
                data.append((fc(c, n), agree(c), wavefront(c),
                             cnt2(c), int_sum(c), rank[c]))
            X = array([[d[0], d[1], d[2], d[3], d[4], 1] for d in data])
            y = array([d[5] for d in data])
            # Least squares fit
            try:
                coeffs, residuals, _, _ = linalg.lstsq(X, y, rcond=None)
                pred = X @ coeffs
                max_err = max(abs(pred - y))
                mean_err = sum(abs(pred - y)) / len(y)
                print(f"  Linear fit of rank: coeffs={[f'{c:.2f}' for c in coeffs]}")
                print(f"    (fc, agree, wavefront, cnt2, int_sum, const)")
                print(f"    max_err={max_err:.1f}, mean_err={mean_err:.2f}")
            except Exception:
                pass

        # 10. Key test: is there a "column potential" that works?
        # For each column j, define φ_j(c[j-1], c[j]) and test if
        # Φ = Σ φ_j decreases. We know this is infeasible globally, but
        # test the RESTRICTED TP subgraph by Δfc sign.

        # Δfc=0 edges only
        dfc0_edges = [(c, s, p) for c, s, p in tp_edges
                      if fc(s, n) == fc(c, n)]
        print(f"\n  Δfc=0 subgraph: {len(dfc0_edges)} edges")
        # Check wavefront on Δfc=0 edges
        viol_wf0 = sum(1 for c, s, _ in dfc0_edges if wavefront(s) >= wavefront(c))
        viol_wf0b = sum(1 for c, s, _ in dfc0_edges if wavefront(s) <= wavefront(c))
        print(f"    wavefront dec: {viol_wf0} viol, wavefront inc: {viol_wf0b} viol")

        # Within Δfc=0, test agree
        viol_ag0 = sum(1 for c, s, _ in dfc0_edges if agree(s) < agree(c))
        print(f"    agree non-dec: {viol_ag0} violations")

        # Within Δfc=0, what entries fire at each position?
        dfc0_entries = Counter()
        for c, s, p in dfc0_edges:
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]; out = s[p]
            dfc0_entries[(p, L, S, R, out)] += 1

        print(f"    Entry types:")
        for (pos, L, S, R, out), cnt in sorted(dfc0_entries.items()):
            kind = "copy_L" if out == L else ("copy_R" if out == R else "other")
            print(f"      pos={pos} ({L},{S},{R})->{out} {kind}: {cnt}")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
