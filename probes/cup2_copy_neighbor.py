#!/usr/bin/env python3
"""Classify ALL privileged entries as copy-neighbor or anomalous.

Key insight: if every privileged entry copies a neighbor (output = L or R),
then Δfc ≤ 0 on every transition. The anomalous entries are the ONLY source
of fc increase. This is the decomposition we need.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict

def classify_entry(L, S, R, out):
    """Classify a privileged entry."""
    if out == S:
        return "stay"
    if out == L:
        return "copy_L"
    if out == R:
        return "copy_R"
    return "anomalous"

def delta_fc(L, S, R, out):
    """Compute frontier count change for a single-processor move."""
    before_left = int(L != S)
    before_right = int(S != R)
    after_left = int(L != out)
    after_right = int(out != R)
    return (after_left - before_left) + (after_right - before_right)

def main():
    print("COPY-NEIGHBOR CLASSIFICATION OF ALL PRIVILEGED ENTRIES")
    print("=" * 70)

    tables = [
        ("T_bot", T_bot, 2, 2, 3),
        ("T_low", T_low, 2, 3, 3),
        ("T_mid", T_mid, 3, 3, 3),
        ("T_high", T_high, 3, 3, 2),
        ("T_top", T_top, 3, 2, 2),
    ]

    anomalous_entries = []
    for name, table, mL, mS, mR in tables:
        print(f"\n{name}:")
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = table[(L, S, R)]
                    if out != S:
                        cls = classify_entry(L, S, R, out)
                        dfc = delta_fc(L, S, R, out)
                        mark = " <<<" if cls == "anomalous" else ""
                        print(f"  ({L},{S},{R})→{out}: {cls:>10}, Δfc={dfc:+d}{mark}")
                        if cls == "anomalous":
                            anomalous_entries.append((name, L, S, R, out, dfc))

    print(f"\n\nANOMALOUS ENTRIES (non-copy-neighbor): {len(anomalous_entries)}")
    for name, L, S, R, out, dfc in anomalous_entries:
        print(f"  {name}({L},{S},{R})→{out}: Δfc={dfc:+d}")

    # KEY THEOREM: copy-neighbor moves have Δfc ≤ 0
    print("\n\nVERIFYING: all copy-neighbor moves have Δfc ≤ 0")
    all_ok = True
    for name, table, mL, mS, mR in tables:
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = table[(L, S, R)]
                    if out != S:
                        cls = classify_entry(L, S, R, out)
                        dfc = delta_fc(L, S, R, out)
                        if cls in ("copy_L", "copy_R") and dfc > 0:
                            print(f"  VIOLATION: {name}({L},{S},{R})→{out} Δfc={dfc}")
                            all_ok = False
    print(f"  Result: {'ALL COPY-NEIGHBOR Δfc ≤ 0 ✓' if all_ok else 'VIOLATIONS FOUND'}")

    # Classify Δfc=0 copy-neighbor moves by frontier propagation direction
    print("\n\nΔfc=0 COPY-NEIGHBOR MOVES (frontier propagation)")
    for name, table, mL, mS, mR in tables:
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = table[(L, S, R)]
                    if out != S:
                        cls = classify_entry(L, S, R, out)
                        dfc = delta_fc(L, S, R, out)
                        if dfc == 0 and cls != "anomalous":
                            if cls == "copy_L":
                                ftype = (S - L) % 3
                                direction = "RIGHT"
                            else:  # copy_R
                                ftype = (R - S) % 3
                                direction = "LEFT"
                            print(f"  {name}({L},{S},{R})→{out}: {cls}, "
                                  f"frontier type d={ftype} moves {direction}")

    # CRITICAL CHECK: is the Δfc=0 subgraph a DAG?
    print("\n\nCRITICAL: Δfc=0 SUBGRAPH DAG CHECK")
    print("-" * 60)
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

        # Build Δfc=0 subgraph and Δfc≤0 subgraph
        from collections import deque
        for label, condition in [("Δfc=0", lambda d: d == 0),
                                  ("Δfc≤0", lambda d: d <= 0),
                                  ("copy-only Δfc=0", None)]:
            in_deg = {c: 0 for c in bad_set}
            adj = {c: [] for c in bad_set}
            edge_count = 0
            for c in bad_set:
                for i in range(n):
                    Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                    out = fs[i](Li, Si, Ri)
                    if out != Si:
                        dfc = delta_fc(Li, Si, Ri, out)
                        cls = classify_entry(Li, Si, Ri, out)
                        if label == "copy-only Δfc=0":
                            keep = (dfc == 0 and cls != "anomalous")
                        else:
                            keep = condition(dfc)
                        if keep:
                            lst = list(c); lst[i] = out; succ = tuple(lst)
                            if succ in bad_set:
                                adj[c].append(succ)
                                in_deg[succ] += 1
                                edge_count += 1

            q = deque(c for c in bad_set if in_deg[c] == 0)
            processed = 0
            while q:
                c = q.popleft()
                processed += 1
                for s in adj[c]:
                    in_deg[s] -= 1
                    if in_deg[s] == 0:
                        q.append(s)
            is_dag = (processed == len(bad_set))
            print(f"  n={nv} {label:>20}: edges={edge_count:>6}, "
                  f"DAG={'Y' if is_dag else 'N'}")

    # Check: what about Δfc≤0 INCLUDING anomalous Δfc=0?
    # (anomalous entries with Δfc=+1 or +2 are excluded by Δfc≤0)
    # But T_mid(2,1,1)→0 has Δfc=+1, T_bot(0,0,0)→1 has Δfc=+2, etc.
    # All anomalous have Δfc>0, so Δfc≤0 excludes ALL anomalous. Good.

if __name__ == "__main__":
    main()
