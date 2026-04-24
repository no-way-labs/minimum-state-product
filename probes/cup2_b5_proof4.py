"""
B5 CASE SPLIT — Trace specific violations at n=5

Find the exact configs where B5 → non-anomalous BFS → anomalous
with fc not decreasing. Trace the full path.
"""
import sys
from itertools import product as cartesian
from collections import deque

# ── CUP-2 tables ──
T_bot = {}
for L in range(2):
    for S in range(2):
        for R in range(3):
            T_bot[(L, S, R)] = S
T_bot[(0, 0, 1)] = 1
T_bot[(0, 0, 2)] = 1
T_bot[(0, 1, 0)] = 0
T_bot[(1, 0, 1)] = 1
T_bot[(1, 0, 2)] = 1
T_bot[(1, 1, 0)] = 0

T_low = {}
for L in range(2):
    for S in range(3):
        for R in range(3):
            T_low[(L, S, R)] = S
T_low[(0, 0, 1)] = 1
T_low[(0, 0, 2)] = 1
T_low[(0, 1, 0)] = 0
T_low[(0, 1, 2)] = 0
T_low[(0, 2, 0)] = 0
T_low[(0, 2, 1)] = 0
T_low[(1, 0, 0)] = 1
T_low[(1, 0, 1)] = 1
T_low[(1, 0, 2)] = 1
T_low[(1, 1, 0)] = 0
T_low[(1, 2, 0)] = 0
T_low[(1, 2, 1)] = 1

T_mid = {}
for L in range(3):
    for S in range(3):
        for R in range(3):
            T_mid[(L, S, R)] = S
T_mid[(0, 1, 0)] = 0
T_mid[(0, 2, 0)] = 0
T_mid[(0, 2, 2)] = 0
T_mid[(1, 0, 0)] = 1
T_mid[(1, 0, 1)] = 1
T_mid[(1, 0, 2)] = 1
T_mid[(1, 1, 2)] = 2
T_mid[(1, 2, 1)] = 1
T_mid[(2, 0, 2)] = 2
T_mid[(2, 1, 0)] = 0
T_mid[(2, 1, 1)] = 0  # B5
T_mid[(2, 2, 0)] = 0
T_mid[(1, 2, 0)] = 0
T_mid[(2, 1, 2)] = 2

T_high = {}
for L in range(3):
    for S in range(3):
        for R in range(2):
            T_high[(L, S, R)] = S
T_high[(0, 1, 0)] = 0
T_high[(0, 2, 0)] = 0
T_high[(0, 2, 1)] = 0
T_high[(1, 0, 0)] = 1
T_high[(1, 0, 1)] = 1
T_high[(1, 1, 0)] = 0
T_high[(1, 2, 0)] = 0
T_high[(1, 2, 1)] = 1
T_high[(2, 0, 0)] = 2
T_high[(2, 0, 1)] = 2
T_high[(2, 1, 0)] = 0
T_high[(2, 1, 1)] = 2
T_high[(2, 2, 0)] = 0

T_top = {}
for L in range(3):
    for S in range(2):
        for R in range(2):
            T_top[(L, S, R)] = S
T_top[(0, 1, 0)] = 0
T_top[(0, 1, 1)] = 0
T_top[(1, 0, 0)] = 1
T_top[(1, 1, 0)] = 0
T_top[(2, 0, 0)] = 1
T_top[(2, 0, 1)] = 1
T_top[(2, 1, 0)] = 0
T_top[(2, 1, 1)] = 0


def build_system(n):
    ms = [2] + [3] * (n - 2) + [2]
    tables = [T_bot, T_low] + [T_mid] * (n - 4) + [T_high, T_top]
    return ms, tables


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


def find_anomalous_entries():
    anom = {}
    for name, table in [("T_bot", T_bot), ("T_low", T_low),
                        ("T_mid", T_mid), ("T_high", T_high),
                        ("T_top", T_top)]:
        for (L, S, R), out in table.items():
            if out == S:
                continue
            dfc = ((1 if L != out else 0) + (1 if out != R else 0)
                   - (1 if L != S else 0) - (1 if S != R else 0))
            if dfc > 0:
                if name not in anom:
                    anom[name] = set()
                anom[name].add((L, S, R))
    return anom


def main():
    anom_entries = find_anomalous_entries()

    for nv in [5, 6, 7]:
        print(f"\n{'=' * 65}")
        print(f"n = {nv}: Tracing B5 Violations")
        print(f"{'=' * 65}")

        ms, tables = build_system(nv)
        n = nv

        table_name = lambda i: ("T_bot" if i == 0 else "T_low" if i == 1
                                else "T_high" if i == n - 2
                                else "T_top" if i == n - 1 else "T_mid")

        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = set(c for c in all_configs if is_good(c, ms))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build adjacency with anomalous classification
        non_anom_adj = {c: [] for c in bad_set}
        anom_adj = {c: [] for c in bad_set}

        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = tables[i][(Li, Si, Ri)]
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        dfc = delta_fc_firing(c, i, out)
                        tname = table_name(i)
                        is_anom = (tname in anom_entries
                                   and (Li, Si, Ri) in anom_entries[tname])
                        entry_info = (tname, (Li, Si, Ri), out, i)
                        if is_anom:
                            anom_adj[c].append((succ, dfc, entry_info))
                        else:
                            non_anom_adj[c].append((succ, dfc, entry_info,
                                                    i))

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

        # BFS from each B5 firing, find violations, trace shortest path
        violations_found = 0
        for src, j, after in b5_firings:
            fc_src = fc(src)

            # BFS (non-anomalous only), track parent for path reconstruction
            visited = {after: None}  # config → (parent_config, firing_info)
            queue = deque([after])
            violation_targets = []

            while queue:
                cur = queue.popleft()
                # Check anomalous transitions at cur
                for succ, dfc, entry_info in anom_adj[cur]:
                    fc_cur = fc(cur)
                    if fc_cur >= fc_src:
                        violation_targets.append(
                            (cur, fc_cur, entry_info, fc_cur - fc_src))

                for succ, dfc, entry_info, pos in non_anom_adj[cur]:
                    if succ not in visited:
                        visited[succ] = (cur, entry_info, pos, dfc)
                        queue.append(succ)

            if violation_targets:
                violations_found += 1
                # Show worst violation
                worst = max(violation_targets, key=lambda x: x[3])
                cur, fc_cur, (tname, entry, out, pos), fc_diff = worst

                if violations_found <= 3:
                    print(f"\n  Violation #{violations_found}:")
                    print(f"  B5 source: {src}  fc={fc_src}")
                    print(f"  B5 fires at pos {j}: c[{j}]=1→0")
                    print(f"  Post-B5:   {after}  fc={fc(after)}")

                    # Trace path from after to cur
                    path = []
                    c_trace = cur
                    while visited[c_trace] is not None:
                        parent, einfo, epos, edfc = visited[c_trace]
                        path.append((parent, c_trace, einfo, epos, edfc))
                        c_trace = parent
                    path.reverse()

                    print(f"\n  Non-anomalous path ({len(path)} steps):")
                    running_dfc = 1  # B5 contribution
                    for i, (p, c_next, einfo, epos, edfc) in enumerate(path):
                        running_dfc += edfc
                        tname_e, entry_e, out_e, _ = einfo
                        print(f"    {p} → {c_next}")
                        print(f"      pos {epos}: {tname_e}{entry_e}→{out_e}"
                              f"  Δfc={edfc:+d}  (running: {running_dfc:+d})")

                    print(f"\n  Reached: {cur}  fc={fc_cur}")
                    print(f"  Anomalous entry: {tname}{entry}→{out} at pos"
                          f" {pos}")
                    print(f"  fc_diff = fc_cur - fc_src = {fc_diff:+d}")

        print(f"\n  Total violations: {violations_found} "
              f"out of {len(b5_firings)} B5 firings")

    # ── PART 2: Check if bad→bad graph has cycles ──
    print(f"\n\n{'=' * 65}")
    print("PART 2: Does the bad→bad graph have cycles?")
    print(f"{'=' * 65}")

    for nv in range(4, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, tables = build_system(nv)
        n = nv
        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = set(c for c in all_configs if is_good(c, ms))
        bad_set = set(c for c in all_configs if c not in good_set)
        bad_list = sorted(bad_set)

        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = tables[i][(Li, Si, Ri)]
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        # Topological sort check (Kahn's algorithm)
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
        v = "✓ DAG" if not has_cycle else f"✗ CYCLE ({cyc_count} in SCC)"
        print(f"  n={nv}: {len(bad_set)} bad configs, {v}")

    # ── PART 3: DAG rank analysis ──
    print(f"\n\n{'=' * 65}")
    print("PART 3: DAG Rank of B5 Source vs Next Anomalous")
    print(f"{'=' * 65}")

    for nv in [5, 6, 7, 8]:
        ms, tables = build_system(nv)
        n = nv
        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = set(c for c in all_configs if is_good(c, ms))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build full adjacency
        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = tables[i][(Li, Si, Ri)]
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        # Compute DAG ranks (longest path from each node)
        # Since it's a DAG, we can do reverse topological order
        in_deg = {c: 0 for c in bad_set}
        for c in bad_set:
            for s in adj[c]:
                in_deg[s] += 1

        topo_order = []
        queue = deque([c for c in bad_set if in_deg[c] == 0])
        while queue:
            c = queue.popleft()
            topo_order.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    queue.append(s)

        # Longest path (DAG rank)
        rank = {c: 0 for c in bad_set}
        for c in reversed(topo_order):
            for s in adj[c]:
                rank[c] = max(rank[c], rank[s] + 1)

        # For B5 firings: compare rank of src vs rank of after
        # and rank of src vs rank of non-anomalous reachable anomalous
        max_rank = max(rank.values())

        # Check: does B5 firing always decrease rank?
        b5_rank_ok = True
        for c in bad_set:
            for j in range(2, n - 2):
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    lst = list(c)
                    lst[j] = 0
                    after = tuple(lst)
                    if after in bad_set:
                        if rank[after] >= rank[c]:
                            b5_rank_ok = False

        print(f"  n={nv}: max_rank={max_rank}, "
              f"B5 always decreases rank: {b5_rank_ok}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
