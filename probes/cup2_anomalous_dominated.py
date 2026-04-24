#!/usr/bin/env python3
"""Check if anomalous edges are DOMINATED by the Δfc≤0 DAG.

Key claim: for every anomalous edge c→c' (both in bad_set),
c' is already reachable from c via Δfc≤0 edges.

If true, then anomalous edges are just "shortcuts" in the DAG.
Adding shortcuts to a DAG never creates cycles.

Proof: if every anomalous edge (u,v) has v reachable from u in G₀,
then the reachability relation of G₀ ∪ E_anomalous equals that of G₀.
Since G₀ is a DAG, G₀ ∪ E_anomalous is a DAG.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def main():
    print("ANOMALOUS EDGE DOMINATION CHECK")
    print("=" * 70)
    print("Claim: for every anomalous edge c→c' in bad_set,")
    print("       c' is reachable from c via Δfc≤0 edges.")
    print()

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build Δfc≤0 adjacency
        adj_leq0 = {c: [] for c in bad_set}
        anomalous_edges = []
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    dfc = delta_fc(Li, Si, Ri, out)
                    cls = classify_entry(Li, Si, Ri, out)
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        if dfc <= 0:
                            adj_leq0[c].append(succ)
                        if cls == "anomalous":
                            anomalous_edges.append((c, succ, i, dfc))

        # For each anomalous edge c→c', check if c' reachable from c via Δfc≤0
        dominated = 0
        not_dominated = 0
        examples = []
        for c, cp, mv, dfc in anomalous_edges:
            # BFS from c using Δfc≤0 edges, looking for c'
            visited = set()
            queue = deque([c])
            visited.add(c)
            found = False
            while queue:
                cur = queue.popleft()
                if cur == cp:
                    found = True
                    break
                for s in adj_leq0[cur]:
                    if s not in visited:
                        visited.add(s)
                        queue.append(s)
            if found:
                dominated += 1
            else:
                not_dominated += 1
                if len(examples) < 5:
                    examples.append((c, cp, mv, dfc))

        status = "ALL DOMINATED ✓" if not_dominated == 0 else f"{not_dominated} NOT dominated"
        print(f"  n={nv}: {len(anomalous_edges)} anomalous edges, "
              f"dominated={dominated}, not_dominated={not_dominated} → {status}")
        for c, cp, mv, dfc in examples:
            fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            fc_cp = sum(1 for j in range(n) if cp[j] != cp[(j+1)%n])
            print(f"    NOT dominated: {c} →[P{mv}]→ {cp} (fc={fc_c}→{fc_cp})")

    print()
    print("If all dominated: anomalous edges are shortcuts in the Δfc≤0 DAG.")
    print("Adding shortcuts to a DAG never creates cycles.")
    print("Therefore: full transition graph is a DAG. QED.")


if __name__ == "__main__":
    main()
