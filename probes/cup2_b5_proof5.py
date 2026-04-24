"""
B5 CASE SPLIT — Using CORRECT tables from cup2_theorem.py

Previous scripts (proof2-4) had WRONG table definitions.
This script imports directly from cup2_theorem.py.
"""
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def fc(c):
    n = len(c)
    return sum(1 for i in range(n) if c[i] != c[(i + 1) % n])


def delta_fc_firing(c, i, new_val):
    n = len(c)
    old = c[i]
    lv = c[(i - 1) % n]
    rv = c[(i + 1) % n]
    return ((1 if lv != new_val else 0) + (1 if new_val != rv else 0)
            - (1 if lv != old else 0) - (1 if old != rv else 0))


def is_good(c, ms):
    n = len(c)
    for i in range(n):
        ci = c[i]
        cp = c[(i + 1) % n]
        if ci == cp:
            continue
        if ci == 0 and cp == 1:
            continue
        if ci == ms[i] - 1 and cp == 0:
            continue
        return False
    return True


def main():
    print("B5 CASE SPLIT — CORRECT TABLES")
    print("=" * 65)

    # ── PART 0: Verify tables ──
    print("\nPART 0: Table Verification")
    print("-" * 65)
    print(f"  T_mid(2,1,1) = {T_mid[(2,1,1)]}  {'✓ B5' if T_mid[(2,1,1)] == 0 else '✗'}")
    print(f"  T_mid(2,1,0) = {T_mid[(2,1,0)]}  (should be 1)")
    print(f"  T_bot(0,0,2) = {T_bot[(0,0,2)]}  (should be 0)")
    print(f"  T_bot(0,0,0) = {T_bot[(0,0,0)]}  (should be 1)")

    # ── PART 1: Anomalous entries with CORRECT tables ──
    print("\n\nPART 1: Anomalous Entry Catalog (Correct Tables)")
    print("-" * 65)

    all_anomalous = {}
    for name, table in [("T_bot", T_bot), ("T_low", T_low),
                        ("T_mid", T_mid), ("T_high", T_high),
                        ("T_top", T_top)]:
        for (L, S, R), out in table.items():
            if out == S:
                continue
            dfc = ((1 if L != out else 0) + (1 if out != R else 0)
                   - (1 if L != S else 0) - (1 if S != R else 0))
            if dfc > 0:
                print(f"  {name}({L},{S},{R}) → {out}  Δfc=+{dfc}")
                if name not in all_anomalous:
                    all_anomalous[name] = set()
                all_anomalous[name].add((L, S, R))

    if not all_anomalous:
        print("  NO anomalous entries! System has Δfc ≤ 0 everywhere.")
        print("  Convergence trivially follows from (fc, Ψ) potential.")
        # Still check for cycles
    else:
        print(f"\n  Total anomalous: {sum(len(v) for v in all_anomalous.values())}")

    # ── PART 2: Cycle check with correct tables ──
    print("\n\nPART 2: Bad→Bad Cycle Check (Correct Tables)")
    print("-" * 65)

    for nv in range(4, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, fs = build_system(nv)
        n = nv

        # Also verify the system
        result = verify_system(ms, fs)
        is_valid = result.get('valid', False)

        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = result['good_configs']
        bad_set = set(c for c in all_configs if c not in good_set)

        # Use the functions from build_system
        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        # Topological sort
        in_deg = {c: 0 for c in bad_set}
        for c in bad_set:
            for s in adj[c]:
                in_deg[s] += 1

        queue = deque([c for c in bad_set if in_deg[c] == 0])
        processed = 0
        while queue:
            c = queue.popleft()
            processed += 1
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    queue.append(s)

        has_cycle = processed < len(bad_set)
        cyc_count = len(bad_set) - processed
        dag_str = ("✓ DAG" if not has_cycle
                   else f"✗ CYCLE ({cyc_count} in SCC)")
        valid_str = "✓" if is_valid else "✗"
        print(f"  n={nv}: {len(bad_set)} bad, {dag_str}, "
              f"verified={valid_str}")

    # ── PART 3: T_mid entry analysis for B5 (correct) ──
    print("\n\nPART 3: T_mid Entry Analysis (Correct)")
    print("-" * 65)

    print("  B5: T_mid(2,1,1) → 0  Δfc=+1")
    print()

    # c[j]=0 behavior
    print("  c[j]=0 behavior — T_mid(L, 0, R):")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L, 0, R)]
            status = "STAY" if out == 0 else f"FIRE→{out}"
            if out != 0:
                dfc = ((1 if L != out else 0) + (1 if out != R else 0)
                       - (1 if L != 0 else 0) - (1 if 0 != R else 0))
                status += f" Δfc={dfc:+d}"
            print(f"    T_mid({L},0,{R})={out}  {status}")

    print()
    print("  c[j-1] drops from 2 — T_mid(L, 2, R) where c[j]=R=0:")
    for L in range(3):
        out = T_mid[(L, 2, 0)]
        dfc = ((1 if L != out else 0) + (1 if out != 0 else 0)
               - (1 if L != 2 else 0) - (1 if 2 != 0 else 0))
        status = "STAY" if out == 2 else f"FIRE→{out} Δfc={dfc:+d}"
        print(f"    T_mid({L},2,0)={out}  {status}")

    print()
    print("  c[j-1] rises from 0 — T_mid(L, 0, R)→1:")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L, 0, R)]
            if out == 1:
                dfc = ((1 if L != 1 else 0) + (1 if 1 != R else 0)
                       - (1 if L != 0 else 0) - (1 if 0 != R else 0))
                print(f"    T_mid({L},0,{R})→1  Δfc={dfc:+d}")

    print()
    print("  c[j] rises from 0→1: T_mid(L, 0, R)→1:")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L, 0, R)]
            if out == 1:
                dfc = ((1 if L != 1 else 0) + (1 if 1 != R else 0)
                       - (1 if L != 0 else 0) - (1 if 0 != R else 0))
                print(f"    T_mid({L},0,{R})→1  Δfc={dfc:+d}  "
                      f"needs c[j-1]={L}")

    print()
    print("  c[j+1] behavior with c[j]=0: T_mid(0, 1, R):")
    for R in range(3):
        out = T_mid[(0, 1, R)]
        status = "STAY" if out == 1 else f"FIRE→{out}"
        if out != 1:
            dfc = ((1 if 0 != out else 0) + (1 if out != R else 0)
                   - (1 if 0 != 1 else 0) - (1 if 1 != R else 0))
            status += f" Δfc={dfc:+d}"
        print(f"    T_mid(0,1,{R})={out}  {status}")

    # ── PART 4: Correct B5 convergence check ──
    print("\n\nPART 4: B5 Convergence Check (Correct Tables)")
    print("-" * 65)

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        tables_by_pos = []
        for i in range(n):
            if i == 0:
                tables_by_pos.append(("T_bot", T_bot))
            elif i == 1:
                tables_by_pos.append(("T_low", T_low))
            elif i == n - 2:
                tables_by_pos.append(("T_high", T_high))
            elif i == n - 1:
                tables_by_pos.append(("T_top", T_top))
            else:
                tables_by_pos.append(("T_mid", T_mid))

        # Build adjacency
        non_anom_adj = {c: [] for c in bad_set}
        anom_adj = {c: [] for c in bad_set}

        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        dfc = delta_fc_firing(c, i, out)
                        tname = tables_by_pos[i][0]
                        is_anom = (tname in all_anomalous
                                   and (Li, Si, Ri) in all_anomalous[tname])
                        if is_anom:
                            anom_adj[c].append((succ, i, dfc, tname,
                                                (Li, Si, Ri)))
                        else:
                            non_anom_adj[c].append((succ, i, dfc))

        # Find B5 firings
        b5_firings = []
        for c in bad_set:
            for j in range(2, n - 2):
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    lst = list(c)
                    lst[j] = 0
                    after = tuple(lst)
                    if after in bad_set:
                        b5_firings.append((c, j, after))

        # BFS from after B5, non-anomalous only, check reachable anomalous
        worst_dec = 999
        violations = 0
        total_reach = 0
        absorbed = 0
        anom_types = {}

        for src, j, after in b5_firings:
            fc_src = fc(src)
            visited = {after}
            queue = deque([after])
            found = False

            while queue:
                cur = queue.popleft()
                for succ, pos, dfc, tname, entry in anom_adj[cur]:
                    fc_cur = fc(cur)
                    dec = fc_src - fc_cur
                    worst_dec = min(worst_dec, dec)
                    total_reach += 1
                    found = True
                    key = (tname, entry)
                    if key not in anom_types:
                        anom_types[key] = {'count': 0, 'min': 999, 'max': -999}
                    anom_types[key]['count'] += 1
                    anom_types[key]['min'] = min(anom_types[key]['min'], dec)
                    anom_types[key]['max'] = max(anom_types[key]['max'], dec)
                    if fc_cur >= fc_src:
                        violations += 1

                for succ, pos, dfc in non_anom_adj[cur]:
                    if succ not in visited:
                        visited.add(succ)
                        queue.append(succ)

            if not found:
                absorbed += 1

        wd = worst_dec if total_reach > 0 else "N/A"
        v = "✓" if violations == 0 else "✗"
        print(f"  n={nv}: {len(b5_firings)} B5, "
              f"{total_reach} reach anom, "
              f"{absorbed} absorbed, "
              f"min_dec={wd}, {violations} viol  {v}")

        if anom_types and nv <= 8:
            for (tname, entry), info in sorted(anom_types.items()):
                L, S, R = entry
                print(f"    {tname}({L},{S},{R}): "
                      f"{info['count']}× dec=[{info['min']},{info['max']}]")

    # ── PART 5: 3-window state machine (correct) ──
    print("\n\nPART 5: 3-Window State Machine (Correct Tables)")
    print("-" * 65)

    start = (2, 0, 1)
    goal = (2, 1, 1)

    # All transitions at j-1, j, j+1 (all T_mid)
    all_states = list(cartesian(range(3), range(3), range(3)))
    edges = {s: [] for s in all_states}

    for s in all_states:
        a, b, cv = s  # c[j-1], c[j], c[j+1]

        # j-1 fires: T_mid(env, a, b) for env ∈ {0,1,2}
        for env in range(3):
            out = T_mid[(env, a, b)]
            if out != a:
                ns = (out, b, cv)
                dfc = ((1 if env != out else 0) + (1 if out != b else 0)
                       - (1 if env != a else 0) - (1 if a != b else 0))
                edges[s].append((ns, dfc, f"j-1: ({env},{a},{b})→{out}"))

        # j fires: T_mid(a, b, cv) — fully determined
        out = T_mid[(a, b, cv)]
        if out != b:
            ns = (a, out, cv)
            dfc = ((1 if a != out else 0) + (1 if out != cv else 0)
                   - (1 if a != b else 0) - (1 if b != cv else 0))
            edges[s].append((ns, dfc, f"j: ({a},{b},{cv})→{out}"))

        # j+1 fires: T_mid(b, cv, env) for env ∈ {0,1,2}
        for env in range(3):
            out = T_mid[(b, cv, env)]
            if out != cv:
                ns = (a, b, out)
                dfc = ((1 if b != out else 0) + (1 if out != env else 0)
                       - (1 if b != cv else 0) - (1 if cv != env else 0))
                edges[s].append((ns, dfc, f"j+1: ({b},{cv},{env})→{out}"))

    # BFS from start
    reachable = set()
    queue = deque([start])
    reachable.add(start)
    while queue:
        s = queue.popleft()
        for ns, dfc, desc in edges[s]:
            if ns not in reachable:
                reachable.add(ns)
                queue.append(ns)

    print(f"  Start: {start}")
    print(f"  Goal:  {goal}")
    print(f"  Reachable: {len(reachable)} states")
    print(f"  Goal reachable: {goal in reachable}")

    if goal in reachable:
        # Find all simple paths
        all_paths = []

        def dfs(state, path, total, visited):
            if state == goal:
                all_paths.append((list(path), total))
                return
            if len(path) > 20:
                return
            for ns, dfc, desc in edges[state]:
                if ns not in visited or ns == goal:
                    visited.add(ns)
                    path.append((state, ns, desc, dfc))
                    dfs(ns, path, total + dfc,
                        visited if ns != goal else visited)
                    path.pop()
                    if ns != goal:
                        visited.discard(ns)

        dfs(start, [], 0, {start})

        print(f"  Simple paths: {len(all_paths)}")
        if all_paths:
            max_t = max(t for _, t in all_paths)
            min_t = min(t for _, t in all_paths)
            print(f"  Max Δfc: {max_t:+d}  (net with B5: {max_t+1:+d})")
            print(f"  Min Δfc: {min_t:+d}  (net with B5: {min_t+1:+d})")

            if max_t <= -2:
                print("  ✓ All paths give net ≤ -1")

            # Show worst 5 paths
            print("\n  Worst paths:")
            for path, total in sorted(all_paths, key=lambda x: -x[1])[:5]:
                print(f"\n    Δfc={total:+d} ({len(path)} steps):")
                running = 0
                for prev, nxt, desc, dfc in path:
                    running += dfc
                    print(f"      {prev}→{nxt} {dfc:+d} "
                          f"(cum:{running:+d}) {desc}")
    else:
        # Check what states with c[j-1]=2 are reachable
        reach2 = [s for s in reachable if s[0] == 2]
        print(f"  Reachable states with c[j-1]=2: {reach2}")

        # What transitions go TO (2,1,1)?
        print("  States that can reach (2,1,1):")
        for s in all_states:
            for ns, dfc, desc in edges[s]:
                if ns == goal:
                    in_r = "✓" if s in reachable else "✗"
                    print(f"    {s}→{goal} Δfc={dfc:+d} {desc}  "
                          f"reachable={in_r}")

    # ── PART 6: Forced sequence (correct) ──
    print("\n\nPART 6: Forced Sequence (Correct Tables)")
    print("-" * 65)

    print("  After B5: (c[j-1], c[j], c[j+1]) = (2, 0, 1). Δfc = +1.")
    print()

    # Check if c[j] is stuck
    print("  Is c[j]=0 stuck while c[j-1]=2?")
    for R in range(3):
        out = T_mid[(2, 0, R)]
        print(f"    T_mid(2, 0, {R}) = {out}  "
              f"{'STAY' if out == 0 else 'FIRE→'+str(out)}")

    print()
    print("  c[j-1]=2 drops with R=c[j]=0:")
    for L in range(3):
        out = T_mid[(L, 2, 0)]
        if out != 2:
            dfc = ((1 if L != out else 0) + (1 if out != 0 else 0)
                   - (1 if L != 2 else 0) - (1 if 2 != 0 else 0))
            print(f"    T_mid({L}, 2, 0) → {out}  Δfc={dfc:+d}")
        else:
            print(f"    T_mid({L}, 2, 0) → 2  STAY")

    print()
    print("  c[j+1]=1 with c[j]=0: T_mid(0, 1, R):")
    for R in range(3):
        out = T_mid[(0, 1, R)]
        if out != 1:
            dfc = ((1 if 0 != out else 0) + (1 if out != R else 0)
                   - (1 if 0 != 1 else 0) - (1 if 1 != R else 0))
            print(f"    T_mid(0, 1, {R}) = {out}  FIRE Δfc={dfc:+d}")
        else:
            print(f"    T_mid(0, 1, {R}) = 1  STAY")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
