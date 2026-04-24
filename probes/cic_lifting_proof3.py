#!/usr/bin/env python3
"""CIC Exploration 10b: P0 same-L, P2 different-R, P3 switching.

Focused investigation of three structural properties:
1. P0 same-L: l = l' universally?
2. P2 different-R: r != r' universally?
3. P3 switching: can P3 always change t_0 from r to r' at binary (1,0,0)?
4. Tube closure: does t_{n-4} = l persist under ternary transitions?
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))


def enumerate_cycles(ms, n, max_cycles=200, max_time=60.0, max_path_len=None):
    if max_path_len is None:
        max_path_len = 10 * n
    t0 = time.time()
    P = 1
    for m in ms:
        P *= m
    if P > 500:
        return []
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    for start_idx in range(min(len(all_configs), P)):
        if time.time() - t0 > max_time:
            break
        start = all_configs[start_idx]
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 500000:
            if time.time() - t0 > max_time:
                break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for new_val in range(ms[p]):
                    if new_val == config[p]:
                        continue
                    if movers:
                        last = movers[-1]
                        diff = min(abs(p - last), n - abs(p - last))
                        if diff > 1:
                            continue
                    new_det = dict(det)
                    consistent = True
                    L = config[(p - 1) % n]
                    S = config[p]
                    R = config[(p + 1) % n]
                    key_m = (p, L, S, R)
                    if key_m in new_det:
                        if new_det[key_m] != new_val:
                            consistent = False
                    else:
                        new_det[key_m] = new_val
                    if consistent:
                        for i in range(n):
                            if i == p:
                                continue
                            Li = config[(i - 1) % n]
                            Si = config[i]
                            Ri = config[(i + 1) % n]
                            key_i = (i, Li, Si, Ri)
                            if key_i in new_det:
                                if new_det[key_i] != Si:
                                    consistent = False
                                    break
                            else:
                                new_det[key_i] = Si
                    if not consistent:
                        continue
                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)
                    if new_config == start and len(path) >= n:
                        me_ok = True
                        for idx in range(len(path)):
                            c = path[idx]
                            priv = []
                            for i in range(n):
                                Li = c[(i - 1) % n]
                                Si = c[i]
                                Ri = c[(i + 1) % n]
                                ki = (i, Li, Si, Ri)
                                if ki in new_det and new_det[ki] != Si:
                                    priv.append(i)
                            if len(priv) != 1:
                                me_ok = False
                                break
                        if me_ok:
                            cycle_tup = tuple(path)
                            if cycle_tup not in [tuple(c) for c, _, _ in cycles]:
                                cycles.append((path, movers + [p], new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue
                    if new_config not in set(path) and len(path) < max_path_len:
                        stack.append((new_config, path + [new_config],
                                      new_det, movers + [p]))
    return cycles


def extract_binary_entries(det, n):
    """Extract P0 and P2 mover entries."""
    p0_up_L = []
    p0_down_L = []
    p2_down_R = []
    p2_up_R = []

    for key, val in det.items():
        proc, Lv, Sv, Rv = key
        if val == Sv:
            continue  # nonmover
        if proc == 0:
            if val > Sv:  # UP
                p0_up_L.append(Lv)
            else:  # DOWN
                p0_down_L.append(Lv)
        elif proc == 2:
            if val > Sv:  # UP
                p2_up_R.append(Rv)
            else:  # DOWN
                p2_down_R.append(Rv)

    return p0_up_L, p0_down_L, p2_down_R, p2_up_R


# ============================================================
# PART 1: P0 same-L and P2 different-R — universal check
# ============================================================
print("=" * 70)
print("PART 1: P0 same-L and P2 different-R universality")
print("=" * 70)
print()

test_cases = [
    (5, (2,2,2,3,3)),
    (5, (2,2,2,2,3)),
    (5, (2,2,2,4,3)),
    (5, (2,2,2,3,4)),
    (5, (2,2,2,2,2)),
    (6, (2,2,2,3,3,3)),
    (6, (2,2,2,4,3,3)),
]

p0_same_total = 0
p0_same_yes = 0
p2_diff_total = 0
p2_diff_yes = 0

for n, ms in test_cases:
    P = 1
    for m in ms:
        P *= m
    if P > 500:
        continue

    cycles = enumerate_cycles(ms, n, max_cycles=50, max_time=20.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]

    same_l = 0
    diff_r = 0
    total = len(full)

    for cycle, movers, det in full:
        p0_up_L, p0_down_L, p2_down_R, p2_up_R = extract_binary_entries(det, n)

        if p0_up_L and p0_down_L:
            p0_same_total += 1
            if set(p0_up_L) == set(p0_down_L):
                same_l += 1
                p0_same_yes += 1

        if p2_down_R and p2_up_R:
            p2_diff_total += 1
            if set(p2_down_R) != set(p2_up_R):
                diff_r += 1
                p2_diff_yes += 1

    print(f"n={n}, ms={list(ms)}, P={P}: {total} cycles")
    print(f"  P0 same-L: {same_l}/{total}")
    print(f"  P2 diff-R: {diff_r}/{total}")

    # Show actual values for first cycle
    if full:
        det0 = full[0][2]
        p0u, p0d, p2d, p2u = extract_binary_entries(det0, n)
        print(f"  Cycle 0: P0 UP L={p0u}, P0 DOWN L={p0d}, "
              f"P2 DOWN R={p2d}, P2 UP R={p2u}")
    print()

print(f"TOTAL: P0 same-L = {p0_same_yes}/{p0_same_total}, "
      f"P2 diff-R = {p2_diff_yes}/{p2_diff_total}")
print()


# ============================================================
# PART 2: P3 switching at binary (1,0,0)
# ============================================================
print("=" * 70)
print("PART 2: P3 switching — can t_0 go from r to r'?")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=20, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    print(f"n={n}, ms={list(ms)}, T={T}")

    for ci, (cycle, movers, det) in enumerate(full[:5]):
        _, _, p2d_R, p2u_R = extract_binary_entries(det, n)
        r = p2d_R[0] if p2d_R else None
        r_prime = p2u_R[0] if p2u_R else None

        if r is None or r_prime is None:
            continue

        # P3 entries at binary (1,0,0): L = P2 = 0
        p3_entries_at_100 = {}
        for key, val in det.items():
            proc, Lv, Sv, Rv = key
            if proc == 3 and Lv == 0 and val != Sv:
                p3_entries_at_100[(Sv, Rv)] = val

        # Can we reach r' from r via P3 transitions?
        # P3 changes t_0 (its own state). Build t_0 transition graph.
        t0_adj = {}  # t_0_old -> t_0_new (for specific t_1 values)
        for (s, rv), new_s in p3_entries_at_100.items():
            t0_adj[(s, rv)] = new_s

        # BFS from t_0=r: can we reach t_0=r'?
        reachable_from_r = {r}
        # But t_0 transitions depend on t_1. Let's track (t_0, t_1) pairs.
        # Actually, P3 transition at (1,0,0): context (P2=0, P3=t_0, P4=t_1)
        # P3 fires: t_0 -> new_t_0. t_1 unchanged.
        # After P3 fires, P4 might fire: context (P3=new_t_0, P4=t_1, P5=t_2)

        # Build full ternary chain at binary (1,0,0)
        # All ternary transitions: proc j fires if (c[j-1], c[j], c[j+1]) matches
        non_good_at_100 = []
        all_configs = list(iproduct(*[range(m) for m in ms]))
        good_set = set(cycle)
        for c in all_configs:
            if c[:3] == (1, 0, 0) and c not in good_set:
                non_good_at_100.append(c)

        # For each non-good config at (1,0,0), trace ternary chain
        can_reach_rprime = 0
        for c in non_good_at_100:
            t0 = c[3]
            if t0 == r_prime:
                can_reach_rprime += 1
                continue
            # BFS through ternary transitions
            visited = {c}
            queue = [c]
            reached = False
            while queue and not reached:
                curr = queue.pop(0)
                for p in range(3, n):
                    Lp = curr[(p-1) % n]
                    Sp = curr[p]
                    Rp = curr[(p+1) % n]
                    key = (p, Lp, Sp, Rp)
                    if key in det and det[key] != Sp:
                        nc = list(curr)
                        nc[p] = det[key]
                        nc = tuple(nc)
                        if nc[:3] == (1, 0, 0) and nc not in good_set:
                            if nc[3] == r_prime:
                                reached = True
                                break
                            if nc not in visited:
                                visited.add(nc)
                                queue.append(nc)
            if reached:
                can_reach_rprime += 1

        print(f"\n  Cycle {ci}: r={r}, r'={r_prime}")
        print(f"    P3 entries at L=0 (binary 1,0,0): {p3_entries_at_100}")
        print(f"    Non-good at (1,0,0): {len(non_good_at_100)}")
        print(f"    Can reach t_0={r_prime} via ternary: "
              f"{can_reach_rprime}/{len(non_good_at_100)}")

        # Same analysis at binary (0,0,1) — can reach t_0=r from t_0=r'?
        non_good_at_001 = []
        for c in all_configs:
            if c[:3] == (0, 0, 1) and c not in good_set:
                non_good_at_001.append(c)

        can_reach_r = 0
        for c in non_good_at_001:
            t0 = c[3]
            if t0 == r:
                can_reach_r += 1
                continue
            visited = {c}
            queue = [c]
            reached = False
            while queue and not reached:
                curr = queue.pop(0)
                for p in range(3, n):
                    Lp = curr[(p-1) % n]
                    Sp = curr[p]
                    Rp = curr[(p+1) % n]
                    key = (p, Lp, Sp, Rp)
                    if key in det and det[key] != Sp:
                        nc = list(curr)
                        nc[p] = det[key]
                        nc = tuple(nc)
                        if nc[:3] == (0, 0, 1) and nc not in good_set:
                            if nc[3] == r:
                                reached = True
                                break
                            if nc not in visited:
                                visited.add(nc)
                                queue.append(nc)
            if reached:
                can_reach_r += 1

        print(f"    At (0,0,1): can reach t_0={r}: "
              f"{can_reach_r}/{len(non_good_at_001)}")

    print()


# ============================================================
# PART 3: Tube closure — does t_{n-4} = l persist?
# ============================================================
print("=" * 70)
print("PART 3: Tube closure — P_{n-1} firing within tube")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=10, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    p0u, p0d, _, _ = extract_binary_entries(det, n)
    l = p0u[0] if p0u else None

    if l is None:
        continue

    print(f"n={n}, ms={list(ms)}, l={l}")

    # P_{n-1} mover entries
    pnm1_entries = {}
    for key, val in det.items():
        proc, Lv, Sv, Rv = key
        if proc == n - 1 and val != Sv:
            pnm1_entries[key] = val

    print(f"  P_{n-1} mover entries:")
    for key, val in sorted(pnm1_entries.items()):
        _, Lv, Sv, Rv = key
        print(f"    ({Lv},{Sv},{Rv}) -> {val}")

    # Check: does any entry have S = l (fires when P_{n-1} = l)?
    fires_at_l = [(key, val) for key, val in pnm1_entries.items() if key[2] == l]
    print(f"  Entries with S={l} (fires when P_{{n-1}}={l}): {len(fires_at_l)}")
    for key, val in fires_at_l:
        _, Lv, Sv, Rv = key
        print(f"    ({Lv},{l},{Rv}) -> {val}")

    # At which binary states would P_{n-1} fire with S=l?
    # P_{n-1}'s context: (P_{n-2}, P_{n-1}, P0)
    # L = P_{n-2} = t_{n-5} (ternary), R = P0 (binary)
    if fires_at_l:
        print(f"  At binary states where P0 = R:")
        for key, val in fires_at_l:
            _, Lv, _, Rv = key
            print(f"    P_{n-2}={Lv}, P0={Rv} -> P_{n-1} fires ({l}->{val})")
            # Which binary states have P0=Rv?
            matching = [b for b in [(0,0,1),(0,1,1),(0,1,0),(1,1,0),(1,0,0),(1,0,1)]
                        if b[0] == Rv]
            print(f"    Matching binary states: {matching}")

    # Count: within tube (t_{n-4}=l), how many configs have P_{n-1} firing?
    tube_total = 0
    tube_pnm1_fires = 0
    all_configs = list(iproduct(*[range(m) for m in ms]))
    for c in all_configs:
        if c[n-1] == l and c not in good_set:
            tube_total += 1
            # Check if P_{n-1} fires
            Lp = c[n-2]
            Sp = c[n-1]
            Rp = c[0]
            key = (n-1, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                tube_pnm1_fires += 1

    print(f"\n  Tube (t_{{n-4}}={l}): {tube_total} non-good configs")
    print(f"  P_{{n-1}} fires within tube: {tube_pnm1_fires} "
          f"({100*tube_pnm1_fires/max(1,tube_total):.0f}%)")

    if tube_pnm1_fires > 0:
        print(f"  TUBE IS NOT CLOSED — P_{{n-1}} fires and changes t_{{n-4}}")
    else:
        print(f"  TUBE IS CLOSED — P_{{n-1}} never fires within tube")

    print()


# ============================================================
# PART 4: Explicit cycle construction attempt
# ============================================================
print("=" * 70)
print("PART 4: Explicit cycle — trace through tube with P3 switching")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=5, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    p0u, p0d, p2d, p2u = extract_binary_entries(det, n)
    l = p0u[0] if p0u else 0
    r = p2d[0] if p2d else 0
    r_prime = p2u[0] if p2u else 1

    print(f"n={n}, ms={list(ms)}, r={r}, r'={r_prime}, l={l}")

    # Try to trace: (0,0,1, r, ?, ..., ?, l) through the 6-cycle
    # with ternary detours.
    # Start: binary (0,0,1), t_0=r, t_{n-4}=l
    # Middle coords: try all possibilities

    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good_set = set(c for c in all_configs if c not in good_set)

    # Starting configs: (0,0,1, r, ?, l) non-good
    starts = [c for c in all_configs
              if c[:3] == (0,0,1) and c[3] == r and c[n-1] == l
              and c not in good_set]

    print(f"  Starting configs (0,0,1, t_0={r}, ..., t_{{n-4}}={l}): {len(starts)}")

    # For each start, try to follow the 6-cycle + ternary chain
    for start in starts[:3]:
        print(f"\n  Tracing from {start}:")
        c = start
        path = [c]
        procs = []
        stuck = False

        for binary_step, (target_bin, expected_proc) in enumerate([
            ((0,1,1), 1),  # P1 UP
            ((0,1,0), 2),  # P2 DOWN (may need ternary first)
            ((1,1,0), 0),  # P0 UP (may need ternary first)
            ((1,0,0), 1),  # P1 DOWN
            ((1,0,1), 2),  # P2 UP (needs t_0=r', may need ternary)
            ((0,0,1), 0),  # P0 DOWN (may need ternary)
        ]):
            # First try direct binary transition
            cur_bin = tuple(c[:3])

            # Try ternary adjustments first if needed
            ternary_steps = 0
            max_ternary = 20
            while ternary_steps < max_ternary:
                # Check if the binary transition fires
                p = expected_proc
                Lp = c[(p-1) % n]
                Sp = c[p]
                Rp = c[(p+1) % n]
                key = (p, Lp, Sp, Rp)
                if key in det and det[key] != Sp:
                    # Binary transition fires!
                    nc = list(c)
                    nc[p] = det[key]
                    nc = tuple(nc)
                    if nc not in good_set:
                        c = nc
                        path.append(c)
                        procs.append(f"P{p}")
                        break
                    else:
                        # Goes to good — try different path
                        pass

                # Try ternary transitions
                fired = False
                for tp in range(3, n):
                    Ltp = c[(tp-1) % n]
                    Stp = c[tp]
                    Rtp = c[(tp+1) % n]
                    tkey = (tp, Ltp, Stp, Rtp)
                    if tkey in det and det[tkey] != Stp:
                        nc = list(c)
                        nc[tp] = det[tkey]
                        nc = tuple(nc)
                        if nc not in good_set and tuple(nc[:3]) == cur_bin:
                            c = nc
                            path.append(c)
                            procs.append(f"t{tp}")
                            fired = True
                            ternary_steps += 1
                            break

                if not fired:
                    # No ternary transition available — stuck
                    stuck = True
                    break

            if stuck:
                print(f"    STUCK at binary {cur_bin}, config {c}")
                break

        if not stuck:
            # Check if we returned close to start
            end = c
            end_bin = tuple(end[:3])
            start_bin = tuple(start[:3])
            print(f"    Completed! Start: {start}, End: {end}")
            print(f"    Binary path: {[tuple(p[:3]) for p in path]}")
            print(f"    Proc sequence: {procs}")
            print(f"    Total steps: {len(path)-1}")
            print(f"    Returned to same binary: {end_bin == start_bin}")
            print(f"    Same config: {end == start}")

            # If not same config, continue tracing to see if we cycle back
            if end != start and end_bin == start_bin:
                # Keep going from end, try another round
                for _ in range(5):  # up to 5 more rounds
                    for binary_step, (target_bin, expected_proc) in enumerate([
                        ((0,1,1), 1), ((0,1,0), 2), ((1,1,0), 0),
                        ((1,0,0), 1), ((1,0,1), 2), ((0,0,1), 0),
                    ]):
                        cur_bin = tuple(c[:3])
                        ternary_steps = 0
                        while ternary_steps < max_ternary:
                            p = expected_proc
                            Lp = c[(p-1) % n]
                            Sp = c[p]
                            Rp = c[(p+1) % n]
                            key = (p, Lp, Sp, Rp)
                            if key in det and det[key] != Sp:
                                nc = list(c)
                                nc[p] = det[key]
                                nc = tuple(nc)
                                if nc not in good_set:
                                    c = nc
                                    path.append(c)
                                    break
                            fired = False
                            for tp in range(3, n):
                                Ltp = c[(tp-1) % n]
                                Stp = c[tp]
                                Rtp = c[(tp+1) % n]
                                tkey = (tp, Ltp, Stp, Rtp)
                                if tkey in det and det[tkey] != Stp:
                                    nc = list(c)
                                    nc[tp] = det[tkey]
                                    nc = tuple(nc)
                                    if nc not in good_set and tuple(nc[:3]) == cur_bin:
                                        c = nc
                                        path.append(c)
                                        fired = True
                                        ternary_steps += 1
                                        break
                            if not fired:
                                stuck = True
                                break
                        if stuck:
                            break
                    if stuck:
                        break
                    if c == start:
                        print(f"    CYCLE FOUND after {len(path)-1} total steps!")
                        break
                if c != start and not stuck:
                    print(f"    No return after 5 rounds, current: {c}")

    print()


# ============================================================
# PART 5: WHY l = l'? Analytical check
# ============================================================
print("=" * 70)
print("PART 5: WHY l = l'? P_{n-1} state at P0 firing times")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m

    cycles = enumerate_cycles(ms, n, max_cycles=5, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    print(f"n={n}, ms={list(ms)}")

    for ci, (cycle, mvrs, det) in enumerate(full[:3]):
        # Find P0 firing steps
        p0_steps = []
        for step, p in enumerate(mvrs):
            if p == 0:
                c = cycle[step]
                direction = "UP" if det[(0, c[n-1], c[0], c[1])] > c[0] else "DOWN"
                p0_steps.append((step, c, direction, c[n-1]))

        # Find P_{n-1} firing steps
        pn_steps = []
        for step, p in enumerate(mvrs):
            if p == n - 1:
                c = cycle[step]
                pn_steps.append((step, c, c[n-1]))

        print(f"\n  Cycle {ci} (L={len(cycle)}):")
        print(f"  P0 fires at steps: ", end="")
        for step, c, d, pnv in p0_steps:
            print(f"{step}({d},P_{n-1}={pnv})", end=" ")
        print()

        print(f"  P_{n-1} fires at steps: ", end="")
        for step, c, val in pn_steps:
            print(f"{step}(val={val})", end=" ")
        print()

        # Between P0 UP and P0 DOWN: how many P_{n-1} firings?
        p0_up_step = [s for s, _, d, _ in p0_steps if d == "UP"]
        p0_down_step = [s for s, _, d, _ in p0_steps if d == "DOWN"]
        if p0_up_step and p0_down_step:
            up = p0_up_step[0]
            down = p0_down_step[0]
            between = [s for s, _, _ in pn_steps
                       if (up < s < down if up < down
                           else (s > up or s < down))]
            print(f"  P_{n-1} firings between P0 UP (step {up}) "
                  f"and P0 DOWN (step {down}): {len(between)} at steps {between}")

    print()
