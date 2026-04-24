#!/usr/bin/env python3
"""Find a tiebreaker for T_bot(1,1,2)→0 between-firing violations.

When fc stays the same between consecutive T_bot(1,1,2)→0 firings,
what quantity ALWAYS decreases?

Check: c[n-2], c[n-1], sum, interior sum, various boundary quantities,
and whether T_bot(0,0,0)→1 must fire in between.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_high, T_top
from cup2_convergence_proof import T_mid_alt, build_system, classify, delta_fc, psi
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque


def main():
    print("T_bot(1,1,2)→0 VIOLATION ANALYSIS")
    print("=" * 70)

    for nv in range(5, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build adjacency with edge types
        adj = {c: [] for c in bad_set}
        edge_info = {}
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
                        cls = classify(Li, Si, Ri, out)
                        edge_info[(c, succ)] = (cls, i)

        # Find T_bot(1,1,2)→0 sources
        def is_bd_src(c):
            return c[n-1] == 1 and c[0] == 1 and c[1] == 2

        bd_srcs = [c for c in bad_set if is_bd_src(c)]

        # For each, BFS forward to find next T_bot(1,1,2)→0 source
        # Also track: does T_bot(0,0,0)→1 fire in between?
        pairs = []  # (src, next_src, bot_up_between, path_has_anom_types)
        for src in bd_srcs:
            lst = list(src); lst[0] = 0; after = tuple(lst)
            if after not in bad_set:
                continue

            visited = {after}
            queue = deque([(after, set())])  # (config, set of anomalous types seen)
            while queue:
                cur, anom_seen = queue.popleft()
                for s in adj[cur]:
                    if s not in visited:
                        visited.add(s)
                        new_anom = set(anom_seen)
                        info = edge_info.get((cur, s))
                        if info and info[0] == "anomalous":
                            new_anom.add(info[1])  # position of anomalous
                        if is_bd_src(s):
                            lst2 = list(s); lst2[0] = 0; nxt_after = tuple(lst2)
                            if nxt_after in bad_set:
                                pairs.append((src, s, 0 in new_anom, new_anom))
                                continue
                        queue.append((s, new_anom))

        # Filter to violations: fc same, Ψ not decreasing
        violations = []
        for src, nxt, bot_up, anom_types in pairs:
            fc_s = sum(1 for j in range(n) if src[j] != src[(j+1)%n])
            fc_n = sum(1 for j in range(n) if nxt[j] != nxt[(j+1)%n])
            if fc_n == fc_s:
                psi_s = psi(src, n)
                psi_n = psi(nxt, n)
                if psi_n >= psi_s:
                    violations.append((src, nxt, fc_s, psi_s, psi_n, bot_up, anom_types))

        all_pairs_count = len(pairs)
        viol_count = len(violations)
        print(f"\n  n={nv}: {len(bd_srcs)} sources, {all_pairs_count} pairs, "
              f"{viol_count} (fc,Ψ)-violations")

        if viol_count == 0:
            continue

        # For each violation, check candidate tiebreakers
        print(f"  Checking tiebreaker quantities on {viol_count} violations:")

        # Candidate tiebreakers
        def c_nm2(c): return c[n-2]          # value at position n-2
        def c_nm1(c): return c[n-1]          # value at position n-1
        def sum_c(c): return sum(c)           # total sum
        def sum_int(c): return sum(c[2:n-2])  # interior sum (positions 2..n-3)
        def count_0(c): return sum(1 for v in c if v == 0)  # number of zeros
        def count_2(c): return sum(1 for v in c if v == 2)  # number of 2s
        def neg_sum(c): return -sum(c)
        def neg_c0_cn2(c): return -(c[0] + c[n-2])
        def sum_right(c): return c[n-3] + c[n-2] + c[n-1] if n >= 4 else 0

        candidates = [
            ("c[n-2]", c_nm2),
            ("-c[n-2]", lambda c: -c_nm2(c)),
            ("c[n-1]", c_nm1),
            ("-sum", neg_sum),
            ("sum_int", sum_int),
            ("#zeros", count_0),
            ("-#zeros", lambda c: -count_0(c)),
            ("#twos", count_2),
            ("-sum_right", lambda c: -sum_right(c)),
        ]

        for cand_name, cand_func in candidates:
            dec = same = inc = 0
            for src, nxt, fc, ps, pn, bu, at in violations:
                v_s = cand_func(src)
                v_n = cand_func(nxt)
                if v_n < v_s: dec += 1
                elif v_n == v_s: same += 1
                else: inc += 1
            status = "✓ ALWAYS DEC" if inc == 0 and same == 0 else \
                     "~ non-inc" if inc == 0 else "✗"
            if inc == 0:
                print(f"    {cand_name:>15}: {dec} dec, {same} same, {inc} inc  {status}")

        # Key question: does T_bot(0,0,0)→1 always fire between violations?
        bot_up_count = sum(1 for _, _, _, _, _, bu, _ in violations if bu)
        print(f"    T_bot(0,0,0)→1 fires between: {bot_up_count}/{viol_count}")

        # Print violation examples with all quantities
        print(f"\n  Violation examples:")
        for src, nxt, fc, ps, pn, bu, at in violations[:5]:
            print(f"    {src} → {nxt}")
            print(f"      fc={fc}, Ψ={ps}→{pn}, sum={sum(src)}→{sum(nxt)}, "
                  f"c[n-2]={src[n-2]}→{nxt[n-2]}, "
                  f"bot_up_between={bu}, anom_at={at}")


if __name__ == "__main__":
    main()
