"""
B5 CASE SPLIT — Trace specific violations at n=5,6,7 with CORRECT tables.
Import tables directly from cup2_theorem.py.
"""
import sys, os
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


def find_anomalous():
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
    all_anomalous = find_anomalous()
    print("Anomalous entries:")
    for name in sorted(all_anomalous):
        table = {"T_bot": T_bot, "T_low": T_low, "T_mid": T_mid,
                 "T_high": T_high, "T_top": T_top}[name]
        for (L, S, R) in sorted(all_anomalous[name]):
            out = table[(L, S, R)]
            dfc = ((1 if L != out else 0) + (1 if out != R else 0)
                   - (1 if L != S else 0) - (1 if S != R else 0))
            print(f"  {name}({L},{S},{R})→{out}  Δfc=+{dfc}")

    for nv in [5, 6, 7]:
        print(f"\n{'=' * 70}")
        print(f"n={nv}: B5 VIOLATION TRACE")
        print(f"{'=' * 70}")

        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        def table_name(i):
            if i == 0: return "T_bot"
            if i == 1: return "T_low"
            if i == n - 2: return "T_high"
            if i == n - 1: return "T_top"
            return "T_mid"

        # Build adjacency
        non_anom_adj = {c: [] for c in bad_set}
        anom_at = {c: [] for c in bad_set}  # anomalous entries that can fire

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
                    dfc = delta_fc_firing(c, i, out)
                    tname = table_name(i)
                    is_anom = (tname in all_anomalous
                               and (Li, Si, Ri) in all_anomalous[tname])
                    if succ in bad_set:
                        if is_anom:
                            anom_at[c].append((i, tname, (Li, Si, Ri),
                                               out, dfc, succ))
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

        # For each B5, BFS non-anomalous, find violated anomalous
        violation_count = 0
        for src, j, after in b5_firings:
            fc_src = fc(src)

            # BFS
            parent = {after: None}
            queue = deque([after])
            violations = []

            while queue:
                cur = queue.popleft()
                # Check anomalous at cur
                for pos, tname, entry, out, dfc, succ in anom_at[cur]:
                    fc_cur = fc(cur)
                    if fc_cur >= fc_src:
                        violations.append((cur, pos, tname, entry, out,
                                           dfc, fc_cur))
                # Continue BFS
                for succ, pos, dfc in non_anom_adj[cur]:
                    if succ not in parent:
                        parent[succ] = (cur, pos, dfc)
                        queue.append(succ)

            if violations:
                violation_count += 1
                if violation_count <= 5:
                    # Show worst violation
                    worst = max(violations, key=lambda x: x[6])
                    cur, vpos, vtname, ventry, vout, vdfc, vfc = worst

                    print(f"\n  Violation #{violation_count}:")
                    print(f"    B5 source: {src}  fc={fc_src}")
                    print(f"    B5 at pos {j}: c[{j}]=1→0  Δfc=+1")
                    print(f"    Post-B5:   {after}  fc={fc(after)}")

                    # Trace path
                    path = []
                    c_trace = cur
                    while parent[c_trace] is not None:
                        p, pos, dfc = parent[c_trace]
                        Li = p[(pos - 1) % n]
                        Si = p[pos]
                        Ri = p[(pos + 1) % n]
                        out = fs[pos](Li, Si, Ri)
                        path.append((p, c_trace, pos, dfc,
                                     table_name(pos), (Li, Si, Ri), out))
                        c_trace = p
                    path.reverse()

                    if path:
                        print(f"\n    Non-anom path ({len(path)} steps):")
                        running = 1  # include B5
                        for p, nxt, pos, dfc, tn, entry, out in path:
                            running += dfc
                            print(f"      {p}")
                            print(f"        pos {pos}: {tn}{entry}→{out}"
                                  f"  Δfc={dfc:+d}  (run:{running:+d})")
                        print(f"      {cur}")
                    else:
                        print("    0-step path (immediately at post-B5)")

                    print(f"\n    Anomalous at {cur}  fc={vfc}:")
                    print(f"      pos {vpos}: {vtname}{ventry}→{vout}"
                          f"  Δfc={vdfc:+d}")
                    print(f"      fc_diff = {vfc - fc_src:+d}")

        print(f"\n  Total: {violation_count} violations "
              f"out of {len(b5_firings)} B5 firings")

    # ── PART 2: Position-specific Δfc tracking ──
    print(f"\n\n{'=' * 70}")
    print("POSITION-SPECIFIC B5 CASCADE ANALYSIS")
    print(f"{'=' * 70}")

    # For each B5 firing, compute DAG rank of src and after
    for nv in [5, 6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

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

        # DAG rank (longest path)
        in_deg = {c: 0 for c in bad_set}
        for c in bad_set:
            for s in adj[c]:
                in_deg[s] += 1
        topo = []
        queue = deque([c for c in bad_set if in_deg[c] == 0])
        while queue:
            c = queue.popleft()
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    queue.append(s)

        rank = {c: 0 for c in bad_set}
        for c in reversed(topo):
            for s in adj[c]:
                rank[c] = max(rank[c], rank[s] + 1)

        # Check B5 rank decrease
        b5_rank_dec = []
        for c in bad_set:
            for j in range(2, n - 2):
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    lst = list(c)
                    lst[j] = 0
                    after = tuple(lst)
                    if after in bad_set:
                        dec = rank[c] - rank[after]
                        b5_rank_dec.append(dec)

        if b5_rank_dec:
            print(f"\n  n={nv}: B5 rank decrease: "
                  f"min={min(b5_rank_dec)}, max={max(b5_rank_dec)}, "
                  f"all≥1: {min(b5_rank_dec) >= 1}")

    # ── PART 3: Check if fc is monotone on the DAG ──
    print(f"\n\n{'=' * 70}")
    print("FC MONOTONICITY ON DAG")
    print(f"{'=' * 70}")

    for nv in [5, 6, 7, 8, 9, 10]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        fc_increase_count = 0
        fc_max_increase = 0
        total_edges = 0

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
                        total_edges += 1
                        dfc = fc(succ) - fc(c)
                        if dfc > 0:
                            fc_increase_count += 1
                            fc_max_increase = max(fc_max_increase, dfc)

        print(f"  n={nv}: {total_edges} edges, "
              f"{fc_increase_count} with Δfc>0 "
              f"({100*fc_increase_count/total_edges:.1f}%), "
              f"max_increase={fc_max_increase}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
