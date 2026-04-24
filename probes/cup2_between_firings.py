#!/usr/bin/env python3
"""Check between-firing monotonicity for ALL anomalous types.

Key hypothesis: Between two consecutive firings of the SAME anomalous
entry type on any DAG path, (fc, Ψ) strictly decreases.

If true, this bounds the number of anomalous firings and proves the
full graph is a DAG analytically.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_high, T_top
from cup2_convergence_proof import T_mid_alt, build_system, classify, delta_fc, psi
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque


def check_between_firings(nv, entry_name, fire_condition, fire_pos, fire_output):
    """For a given anomalous entry type, check if (fc, Ψ) strictly decreases
    between consecutive firings on any DAG path.

    fire_condition(c, n) -> True if the entry can fire at config c
    fire_pos: the position of the mover
    fire_output: the new value at the mover position
    """
    ms, fs = build_system(nv)
    n = nv
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    # Build adjacency
    adj = {c: [] for c in bad_set}
    for c in bad_set:
        for i in range(n):
            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
            out = fs[i](Li, Si, Ri)
            if out != Si:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)

    # Find all configs where this entry fires (bad→bad)
    fire_srcs = []
    for c in bad_set:
        if fire_condition(c, n):
            lst = list(c)
            lst[fire_pos(n)] = fire_output
            succ = tuple(lst)
            if succ in bad_set:
                fire_srcs.append(c)

    # For each fire source, BFS forward to find the NEXT fire source
    pairs = []
    for src in fire_srcs:
        # Fire the entry first
        lst = list(src)
        lst[fire_pos(n)] = fire_output
        after = tuple(lst)
        if after not in bad_set:
            continue

        # BFS from after to find next fire source (avoiding further fires from after)
        visited = {after}
        queue = deque([after])
        while queue:
            cur = queue.popleft()
            for s in adj[cur]:
                if s not in visited:
                    visited.add(s)
                    if fire_condition(s, n):
                        # s is a next fire source
                        lst2 = list(s); lst2[fire_pos(n)] = fire_output
                        nxt_after = tuple(lst2)
                        if nxt_after in bad_set:
                            pairs.append((src, s))
                            # Don't BFS further from here — we found a next fire
                            continue
                    queue.append(s)

    # Check (fc, Ψ) monotonicity
    fc_dec = fc_same = fc_inc = 0
    psi_dec = psi_same = psi_inc = 0
    joint_dec = 0  # (fc, Ψ) lexicographically decreases
    joint_violation = 0
    violation_examples = []

    for src, nxt_src in pairs:
        fc_src = sum(1 for j in range(n) if src[j] != src[(j+1)%n])
        fc_nxt = sum(1 for j in range(n) if nxt_src[j] != nxt_src[(j+1)%n])
        psi_src = psi(src, n)
        psi_nxt = psi(nxt_src, n)

        if fc_nxt < fc_src:
            fc_dec += 1
        elif fc_nxt == fc_src:
            fc_same += 1
        else:
            fc_inc += 1

        if psi_nxt < psi_src:
            psi_dec += 1
        elif psi_nxt == psi_src:
            psi_same += 1
        else:
            psi_inc += 1

        if (fc_nxt, psi_nxt) < (fc_src, psi_src):
            joint_dec += 1
        else:
            joint_violation += 1
            if len(violation_examples) < 3:
                violation_examples.append((src, nxt_src, fc_src, fc_nxt, psi_src, psi_nxt))

    return {
        'name': entry_name,
        'n': nv,
        'sources': len(fire_srcs),
        'pairs': len(pairs),
        'fc': (fc_dec, fc_same, fc_inc),
        'psi': (psi_dec, psi_same, psi_inc),
        'joint_dec': joint_dec,
        'joint_violation': joint_violation,
        'violations': violation_examples,
    }


def main():
    print("BETWEEN-FIRING MONOTONICITY CHECK — ALL ANOMALOUS TYPES")
    print("=" * 70)
    print("Hypothesis: Between consecutive same-type firings, (fc, Ψ) strictly decreases")
    print()

    # Define the 4 anomalous entry types
    entries = [
        ("T_bot(0,0,0)→1",
         lambda c, n: c[n-1] == 0 and c[0] == 0 and c[1] == 0,
         lambda n: 0,
         1),
        ("T_bot(1,1,2)→0",
         lambda c, n: c[n-1] == 1 and c[0] == 1 and c[1] == 2,
         lambda n: 0,
         0),
        ("T_high(1,1,1)→2",
         lambda c, n: c[n-3] == 1 and c[n-2] == 1 and c[n-1] == 1,
         lambda n: n-2,
         2),
        ("T_top(2,0,0)→1",
         lambda c, n: c[n-2] == 2 and c[n-1] == 0 and c[0] == 0,
         lambda n: n-1,
         1),
    ]

    all_pass = True
    for name, cond, pos, out in entries:
        print(f"\n{'─'*60}")
        print(f"  {name}")
        print(f"{'─'*60}")
        for nv in range(5, 12):
            prod = 4 * 3 ** (nv - 2)
            if prod > 100000:
                break
            r = check_between_firings(nv, name, cond, pos, out)
            status = "✓" if r['joint_violation'] == 0 else "✗"
            print(f"  n={nv}: {r['sources']} sources, {r['pairs']} pairs → "
                  f"fc ({r['fc'][0]} dec, {r['fc'][1]} same, {r['fc'][2]} inc), "
                  f"joint {r['joint_dec']}/{r['pairs']} dec "
                  f"[{status}]")
            if r['joint_violation'] > 0:
                all_pass = False
                for s, ns, fc_s, fc_n, p_s, p_n in r['violations']:
                    print(f"    VIOLATION: {s} fc={fc_s},Ψ={p_s} → {ns} fc={fc_n},Ψ={p_n}")

    print("\n" + "=" * 70)
    if all_pass:
        print("ALL CHECKS PASS: Between consecutive same-type anomalous firings,")
        print("(fc, Ψ) ALWAYS strictly decreases.")
        print("\nThis implies each anomalous entry fires at most O(n²) times on any path,")
        print("bounding total anomalous firings and proving the DAG property.")
    else:
        print("SOME CHECKS FAIL — hypothesis needs refinement.")

    # ── Additional: check what happens between ANY two consecutive anomalous firings ──
    print("\n\n" + "=" * 70)
    print("BONUS: BETWEEN ANY TWO CONSECUTIVE ANOMALOUS FIRINGS")
    print("=" * 70)
    print("Check (fc, Ψ) between pairs of different anomalous types.\n")

    for nv in range(5, 10):
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        adj = {c: [] for c in bad_set}
        edge_cls = {}
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
                        edge_cls[(c, succ)] = classify(Li, Si, Ri, out)

        # Find all anomalous sources
        anom_srcs = set()
        anom_targets = {}  # src -> target after firing
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    cls = classify(Li, Si, Ri, out)
                    if cls == "anomalous":
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            anom_srcs.add(c)
                            anom_targets[c] = succ

        # For each anomalous source, BFS to find the next anomalous source
        total_pairs = 0
        fc_dec = fc_same = fc_inc = 0
        joint_dec = joint_viol = 0
        for src in anom_srcs:
            after = anom_targets[src]
            visited = {after}
            queue = deque([after])
            while queue:
                cur = queue.popleft()
                for s in adj[cur]:
                    if s not in visited:
                        visited.add(s)
                        if s in anom_srcs:
                            total_pairs += 1
                            fc_s = sum(1 for j in range(n) if src[j] != src[(j+1)%n])
                            fc_n = sum(1 for j in range(n) if s[j] != s[(j+1)%n])
                            psi_s = psi(src, n)
                            psi_n = psi(s, n)
                            if fc_n < fc_s: fc_dec += 1
                            elif fc_n == fc_s: fc_same += 1
                            else: fc_inc += 1
                            if (fc_n, psi_n) < (fc_s, psi_s):
                                joint_dec += 1
                            else:
                                joint_viol += 1
                            continue  # don't BFS further
                        queue.append(s)

        viol_pct = f"{100*joint_viol/total_pairs:.1f}%" if total_pairs > 0 else "N/A"
        print(f"  n={nv}: {total_pairs} cross-type pairs, "
              f"fc ({fc_dec} dec, {fc_same} same, {fc_inc} inc), "
              f"joint violations: {joint_viol} ({viol_pct})")


if __name__ == "__main__":
    main()
