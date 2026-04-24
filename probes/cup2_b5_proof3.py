"""
B5 CASE SPLIT — Correct Convergence Check

After B5 fires (+1), BFS only along NON-ANOMALOUS transitions (Δfc ≤ 0),
then check: does any reachable config have an anomalous precondition with
fc ≥ fc_pre_b5?

This is the EXACT condition needed for the convergence proof.
"""
import sys
from itertools import product as cartesian
from collections import deque

# ── CUP-2 tables (original, with B5) ──
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
    old_contrib = (1 if lv != old else 0) + (1 if old != rv else 0)
    new_contrib = (1 if lv != new_val else 0) + (1 if new_val != rv else 0)
    return new_contrib - old_contrib


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
    print("B5 CONVERGENCE CHECK (Correct: non-anomalous BFS)")
    print("=" * 65)

    # ── PART 1: Identify ALL anomalous entries ──
    print("\nPART 1: Anomalous Entry Catalog")
    print("-" * 65)

    # For each table, find entries with Δfc > 0
    # Δfc depends on L, S, R, out = table(L,S,R)
    # Δfc = [(L≠out)+(out≠R)] - [(L≠S)+(S≠R)]

    def find_anomalous(table, name):
        anom = []
        for (L, S, R), out in table.items():
            if out == S:
                continue
            dfc = ((1 if L != out else 0) + (1 if out != R else 0)
                   - (1 if L != S else 0) - (1 if S != R else 0))
            if dfc > 0:
                anom.append(((L, S, R), out, dfc))
        return anom

    anomalous_by_table = {}
    for name, table in [("T_bot", T_bot), ("T_low", T_low),
                        ("T_mid", T_mid), ("T_high", T_high),
                        ("T_top", T_top)]:
        anom = find_anomalous(table, name)
        if anom:
            anomalous_by_table[name] = anom
            for (L, S, R), out, dfc in anom:
                print(f"  {name}({L},{S},{R}) → {out}  Δfc=+{dfc}")

    # ── PART 2: For each n, full correct check ──
    print("\n\nPART 2: Correct B5 Convergence Verification")
    print("-" * 65)

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, tables = build_system(nv)
        n = nv

        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = set(c for c in all_configs if is_good(c, ms))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build adjacency: separate anomalous vs non-anomalous transitions
        non_anom_adj = {c: [] for c in bad_set}
        anom_adj = {c: [] for c in bad_set}

        table_name_by_pos = {}
        for i in range(n):
            if i == 0:
                table_name_by_pos[i] = "T_bot"
            elif i == 1:
                table_name_by_pos[i] = "T_low"
            elif i == n - 2:
                table_name_by_pos[i] = "T_high"
            elif i == n - 1:
                table_name_by_pos[i] = "T_top"
            else:
                table_name_by_pos[i] = "T_mid"

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
                        tname = table_name_by_pos[i]
                        is_anom = (tname in anomalous_by_table and
                                   any(e[0] == (Li, Si, Ri)
                                       for e in anomalous_by_table[tname]))
                        if is_anom:
                            anom_adj[c].append((succ, i, dfc))
                        else:
                            non_anom_adj[c].append((succ, i, dfc))

        # Find B5 configs
        b5_firings = []
        for c in bad_set:
            for j in range(2, n - 2):
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    lst = list(c)
                    lst[j] = 0
                    after = tuple(lst)
                    if after in bad_set:
                        b5_firings.append((c, j, after))

        # For each B5 firing:
        # 1. Fire B5 (anomalous, Δfc=+1)
        # 2. BFS from after config using ONLY non-anomalous transitions
        # 3. At each reached config, check if any anomalous entry applies
        # 4. Record fc at that anomalous precondition vs fc at B5 source

        worst_ratio = 999  # min(fc_anom_precond - fc_b5_source)
        violations = 0
        total_anom_reach = 0
        total_absorbed = 0

        for src, j, after in b5_firings:
            fc_src = fc(src)

            # BFS using non-anomalous transitions only
            visited = {after}
            queue = deque([after])

            found_anom = False
            while queue:
                cur = queue.popleft()
                # Check: does cur have any anomalous transition?
                for succ, pos, dfc in anom_adj[cur]:
                    fc_cur = fc(cur)
                    decrease = fc_src - fc_cur
                    worst_ratio = min(worst_ratio, decrease)
                    total_anom_reach += 1
                    found_anom = True
                    if fc_cur >= fc_src:
                        violations += 1

                for succ, pos, dfc in non_anom_adj[cur]:
                    if succ not in visited:
                        visited.add(succ)
                        queue.append(succ)

            if not found_anom:
                total_absorbed += 1

        wd = worst_ratio if total_anom_reach > 0 else "N/A"
        v = "✓" if violations == 0 else "✗"
        print(f"  n={nv}: {len(b5_firings)} B5 firings, "
              f"{total_anom_reach} reach anomalous, "
              f"{total_absorbed} absorbed, "
              f"min_decrease={wd}, "
              f"{violations} violations  {v}")

    # ── PART 3: What anomalous entries are reachable after B5? ──
    print("\n\nPART 3: Which Anomalous Entries Are Reachable After B5?")
    print("-" * 65)

    # For small n, track which anomalous entries are reached
    for nv in [5, 6, 7, 8]:
        ms, tables = build_system(nv)
        n = nv
        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = set(c for c in all_configs if is_good(c, ms))
        bad_set = set(c for c in all_configs if c not in good_set)

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
                        tname = table_name_by_pos.get(i, "T_mid")
                        # Recompute for this n
                        if i == 0:
                            tname = "T_bot"
                        elif i == 1:
                            tname = "T_low"
                        elif i == n - 2:
                            tname = "T_high"
                        elif i == n - 1:
                            tname = "T_top"
                        else:
                            tname = "T_mid"

                        is_anom = (tname in anomalous_by_table and
                                   any(e[0] == (Li, Si, Ri)
                                       for e in anomalous_by_table[tname]))
                        if is_anom:
                            anom_adj[c].append((succ, i, dfc, tname,
                                                (Li, Si, Ri)))
                        else:
                            non_anom_adj[c].append((succ, i, dfc))

        b5_firings = []
        for c in bad_set:
            for j in range(2, n - 2):
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    lst = list(c)
                    lst[j] = 0
                    after = tuple(lst)
                    if after in bad_set:
                        b5_firings.append((c, j, after))

        anom_types_reached = {}
        for src, j, after in b5_firings:
            fc_src = fc(src)
            visited = {after}
            queue = deque([after])
            while queue:
                cur = queue.popleft()
                for succ, pos, dfc, tname, entry in anom_adj[cur]:
                    fc_cur = fc(cur)
                    key = (tname, entry)
                    if key not in anom_types_reached:
                        anom_types_reached[key] = {
                            'count': 0, 'min_dec': 999, 'max_dec': -999}
                    anom_types_reached[key]['count'] += 1
                    dec = fc_src - fc_cur
                    anom_types_reached[key]['min_dec'] = min(
                        anom_types_reached[key]['min_dec'], dec)
                    anom_types_reached[key]['max_dec'] = max(
                        anom_types_reached[key]['max_dec'], dec)

                for succ, pos, dfc in non_anom_adj[cur]:
                    if succ not in visited:
                        visited.add(succ)
                        queue.append(succ)

        print(f"\n  n={nv}:")
        if not anom_types_reached:
            print("    No anomalous entries reachable after B5!")
        else:
            for (tname, entry), info in sorted(anom_types_reached.items()):
                L, S, R = entry
                out = {"T_bot": T_bot, "T_low": T_low, "T_mid": T_mid,
                       "T_high": T_high, "T_top": T_top}[tname][(L, S, R)]
                print(f"    {tname}({L},{S},{R})→{out}: "
                      f"{info['count']} times, "
                      f"fc_decrease=[{info['min_dec']}, {info['max_dec']}]")

    # ── PART 4: Forced sequence proof ──
    print("\n\nPART 4: Analytical Proof")
    print("=" * 65)
    print("""
  THEOREM (B5 Compensation): Let B5 fire at position j, 2 ≤ j ≤ n-3.
  Pre-B5: c[j-1]=2, c[j]=1, c[j+1]=1. Δfc(B5)=+1.
  Post-B5: c[j-1]=2, c[j]=0, c[j+1]=1.

  CLAIM: The non-anomalous transitions reachable from the post-B5
  config reach only anomalous preconditions with fc ≤ fc_pre_B5 - 1.
  Equivalently: any anomalous entry reachable via non-anomalous BFS
  sees fc decreased by at least 1 from the B5 source.

  PROOF SKETCH:
  The key insight is that B5 creates a LOCAL OBLIGATION at position j:
  c[j]=0 is "stuck" (cannot fire) while c[j-1]=2.

  This obligation forces a sequence of events:
  (a) c[j-1] drops 2→0 (Δfc ≤ 0, non-anomalous)
  (b) c[j-1] rises 0→1 (Δfc = 0, non-anomalous)
  (c) c[j] rises 0→1 (Δfc ≤ 0, non-anomalous)

  The minimum cost of (a)+(b)+(c) is -2 (worst case for each step):
  - (a): T_mid(2,2,0)→0, Δfc=0 [worst case c[j-2]=2]
  - (b): T_mid(1,0,0)→1, Δfc=0
  - (c): T_mid(1,0,0)→1, Δfc=0 [worst case c[j+1]=0]

  But (c) with c[j+1]=0 means c[j+1] dropped from 1 to 0 first:
  T_mid(0,1,0)→0 at j+1, Δfc=-2. This COMPENSATES for the worse (c).

  CASE ANALYSIS:
  Case 1: c[j+1]=1 when c[j] fires 0→1.
    (c) = T_mid(1,0,1)→1, Δfc=-2.
    Total (a)+(b)+(c) ≤ 0+0+(-2) = -2. Net with B5: ≤ -1. ✓

  Case 2: c[j+1]=0 when c[j] fires 0→1.
    c[j+1] dropped: T_mid(0,1,0)→0, Δfc=-2 at j+1.
    (c) = T_mid(1,0,0)→1, Δfc=0.
    Total (drop)+(a)+(b)+(c) ≤ -2+0+0+0 = -2. Net with B5: ≤ -1. ✓

  Case 3: c[j+1]=2 when c[j] fires 0→1.
    c[j+1] went 1→2: T_mid(L,1,R)→2 needs R=c[j+2]=2.
    But T_mid(0,1,2)=1 (stays). So c[j+1] can't go to 2 while c[j]=0.
    IMPOSSIBLE. ✓

  Hence in all cases, net Δfc ≤ -1 between B5 and the completion
  of the forced cascade. QED (modulo the claim that intervening
  transitions at other positions are non-anomalous).
""")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
