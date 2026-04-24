"""
Complete enumeration of length-11 cycles for n=5 ms=(2,2,2,3,3).
Uses DP to iterate all 415,800 valid orderings without storing them all.
"""

from itertools import product as iproduct
import time


def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, "non-single mover"
        mover = diffs[0]
        Li = c[(mover - 1) % n]; Si = c[mover]; Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, "conflict"
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}, "conflict"
                required[key] = Si
    return True, required, "OK"


def find_shadow_cycle(determined, good_set, ms, n, max_len=100):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    for start in non_good:
        visited = set()
        path = []
        config = start
        for step in range(max_len + 1):
            if config in good_set:
                break
            if config in visited:
                return path[path.index(config):]
            visited.add(config)
            path.append(config)
            forced = []
            for i in range(n):
                L = config[(i - 1) % n]; S = config[i]; R = config[(i + 1) % n]
                key = (i, L, S, R)
                if key in determined and determined[key] != S:
                    forced.append((i, determined[key]))
            if not forced:
                break
            moved = False
            for proc, new_val in forced:
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config not in good_set:
                    config = new_config
                    moved = True
                    break
            if not moved:
                break
    return None


n = 5
ms = [2, 2, 2, 3, 3]

# Case 1: P3 uses all 3 states (0→1→2→0), P4 uses 2 states (0→v4→0)
# Moves: P0↑(→1), P1↑(→1), P2↑(→1), P3a(0→1), P3b(1→2), P4↑(0→v4)
#         P0↓(→0), P1↓(→0), P2↓(→0), P3c(2→0), P4↓(→0)
# Deps: 0<6, 1<7, 2<8, 3<4<9, 5<10

deps_case1 = {6: frozenset([0]), 7: frozenset([1]), 8: frozenset([2]),
              4: frozenset([3]), 9: frozenset([4]), 10: frozenset([5])}

# Case 2: P4 uses all 3 states (0→1→2→0), P3 uses 2 states (0→v3→0)
# Moves: P0↑, P1↑, P2↑, P3↑(0→v3), P4a(0→1), P4b(1→2)
#         P0↓, P1↓, P2↓, P3↓(→0), P4c(2→0)
# Deps: 0<6, 1<7, 2<8, 3<9, 4<5<10

deps_case2 = {6: frozenset([0]), 7: frozenset([1]), 8: frozenset([2]),
              9: frozenset([3]), 5: frozenset([4]), 10: frozenset([5])}


def enumerate_and_test(move_defs_func, deps, case_name):
    """Enumerate all valid orderings and test each cycle."""
    total_orderings = 0
    total_consistent = 0
    total_shadow = 0
    total_no_shadow = 0
    seen_cycles = set()  # avoid testing duplicate cycles

    def backtrack(done, order, config, cycle):
        nonlocal total_orderings, total_consistent, total_shadow, total_no_shadow

        if len(done) == 11:
            total_orderings += 1

            # Complete the cycle check
            cycle_list = list(cycle)
            if cycle_list[-1] != cycle_list[0]:
                return
            cycle_list = cycle_list[:-1]
            if len(set(cycle_list)) != len(cycle_list):
                return

            # Check single-mover
            for idx in range(len(cycle_list)):
                c = cycle_list[idx]
                c_next = cycle_list[(idx + 1) % len(cycle_list)]
                diffs = [j for j in range(n) if c[j] != c_next[j]]
                if len(diffs) != 1:
                    return

            cycle_key = tuple(cycle_list)
            if cycle_key in seen_cycles:
                return
            seen_cycles.add(cycle_key)

            ok, det, msg = check_cycle_consistency(cycle_list, n, ms)
            if not ok:
                return

            total_consistent += 1
            good_set = set(cycle_list)
            shadow = find_shadow_cycle(det, good_set, ms, n)
            if shadow:
                total_shadow += 1
            else:
                total_no_shadow += 1
                print(f"  *** NO SHADOW! ***")
                for idx, c in enumerate(cycle_list):
                    c_next = cycle_list[(idx + 1) % len(cycle_list)]
                    m = [k for k in range(n) if c[k] != c_next[k]][0]
                    print(f"    {idx}: {c} → P{m}")
            return

        for m_idx in range(11):
            if m_idx in done:
                continue
            if m_idx in deps and not deps[m_idx].issubset(done):
                continue

            proc, new_val = move_defs_func(m_idx)
            if config[proc] == new_val:
                continue  # invalid move

            old_val = config[proc]
            config[proc] = new_val
            new_config_t = tuple(config)
            cycle.append(new_config_t)

            backtrack(done | frozenset([m_idx]), order + [m_idx], config, cycle)

            config[proc] = old_val
            cycle.pop()

    return total_orderings, total_consistent, total_shadow, total_no_shadow, backtrack


print("=" * 70)
print("COMPLETE LENGTH-11 ENUMERATION FOR n=5 ms=(2,2,2,3,3)")
print("=" * 70)

for v4 in [1, 2]:
    def make_move_defs_c1(v4_val):
        defs = {
            0: (0, 1), 1: (1, 1), 2: (2, 1),
            3: (3, 1), 4: (3, 2), 5: (4, v4_val),
            6: (0, 0), 7: (1, 0), 8: (2, 0),
            9: (3, 0), 10: (4, 0),
        }
        return lambda idx: defs[idx]

    move_func = make_move_defs_c1(v4)

    t0 = time.time()
    config = [0] * n
    cycle = [tuple(config)]

    total_ord = [0]
    total_con = [0]
    total_sh = [0]
    total_nosh = [0]
    seen = set()

    def backtrack(done, config, cycle):
        if len(done) == 11:
            total_ord[0] += 1
            cycle_list = list(cycle)
            if cycle_list[-1] != cycle_list[0]:
                return
            cycle_list = cycle_list[:-1]
            if len(set(cycle_list)) != len(cycle_list):
                return
            for idx in range(len(cycle_list)):
                c = cycle_list[idx]
                c_next = cycle_list[(idx + 1) % len(cycle_list)]
                if sum(1 for j in range(n) if c[j] != c_next[j]) != 1:
                    return
            ck = tuple(cycle_list)
            if ck in seen:
                return
            seen.add(ck)
            ok, det, msg = check_cycle_consistency(cycle_list, n, ms)
            if not ok:
                return
            total_con[0] += 1
            good_set = set(cycle_list)
            shadow = find_shadow_cycle(det, good_set, ms, n)
            if shadow:
                total_sh[0] += 1
            else:
                total_nosh[0] += 1
                print(f"  *** NO SHADOW! v4={v4} ***")
            return

        for m_idx in range(11):
            if m_idx in done:
                continue
            if m_idx in deps_case1 and not deps_case1[m_idx].issubset(done):
                continue
            proc, new_val = move_func(m_idx)
            if config[proc] == new_val:
                continue
            old_val = config[proc]
            config[proc] = new_val
            cycle.append(tuple(config))
            backtrack(done | frozenset([m_idx]), config, cycle)
            config[proc] = old_val
            cycle.pop()

    backtrack(frozenset(), config, cycle)
    t1 = time.time()

    print(f"Case 1, v4={v4}: orderings={total_ord[0]}, consistent={total_con[0]}, "
          f"shadow={total_sh[0]}, no_shadow={total_nosh[0]} ({t1-t0:.1f}s)")

for v3 in [1, 2]:
    def make_move_defs_c2(v3_val):
        defs = {
            0: (0, 1), 1: (1, 1), 2: (2, 1),
            3: (3, v3_val), 4: (4, 1), 5: (4, 2),
            6: (0, 0), 7: (1, 0), 8: (2, 0),
            9: (3, 0), 10: (4, 0),
        }
        return lambda idx: defs[idx]

    move_func = make_move_defs_c2(v3)
    config = [0] * n
    cycle = [tuple(config)]

    total_ord = [0]
    total_con = [0]
    total_sh = [0]
    total_nosh = [0]
    seen = set()

    t0 = time.time()

    def backtrack2(done, config, cycle):
        if len(done) == 11:
            total_ord[0] += 1
            cycle_list = list(cycle)
            if cycle_list[-1] != cycle_list[0]:
                return
            cycle_list = cycle_list[:-1]
            if len(set(cycle_list)) != len(cycle_list):
                return
            for idx in range(len(cycle_list)):
                c = cycle_list[idx]
                c_next = cycle_list[(idx + 1) % len(cycle_list)]
                if sum(1 for j in range(n) if c[j] != c_next[j]) != 1:
                    return
            ck = tuple(cycle_list)
            if ck in seen:
                return
            seen.add(ck)
            ok, det, msg = check_cycle_consistency(cycle_list, n, ms)
            if not ok:
                return
            total_con[0] += 1
            good_set = set(cycle_list)
            shadow = find_shadow_cycle(det, good_set, ms, n)
            if shadow:
                total_sh[0] += 1
            else:
                total_nosh[0] += 1
                print(f"  *** NO SHADOW! v3={v3} ***")
            return

        for m_idx in range(11):
            if m_idx in done:
                continue
            if m_idx in deps_case2 and not deps_case2[m_idx].issubset(done):
                continue
            proc, new_val = move_func(m_idx)
            if config[proc] == new_val:
                continue
            old_val = config[proc]
            config[proc] = new_val
            cycle.append(tuple(config))
            backtrack2(done | frozenset([m_idx]), config, cycle)
            config[proc] = old_val
            cycle.pop()

    backtrack2(frozenset(), config, cycle)
    t1 = time.time()

    print(f"Case 2, v3={v3}: orderings={total_ord[0]}, consistent={total_con[0]}, "
          f"shadow={total_sh[0]}, no_shadow={total_nosh[0]} ({t1-t0:.1f}s)")

# Also check ms=(2,2,3,2,3) — the other rotation class
print("\n--- Same for ms=(2,2,3,2,3) ---")
ms_b = [2, 2, 3, 2, 3]
# Binary: P0, P1, P3. Ternary: P2, P4.
# Case: P2 uses all 3 states (0→1→2→0), P4 uses 2 (0→v→0)
# Moves: P0↑, P1↑, P2a(0→1), P3↑, P2b(1→2), P4↑(0→v4)
#         P0↓, P1↓, P2c(2→0), P3↓, P4↓
# Deps: 0<6, 1<7, 2<4<8, 3<9, 5<10

deps_b = {6: frozenset([0]), 7: frozenset([1]), 4: frozenset([2]),
          8: frozenset([4]), 9: frozenset([3]), 10: frozenset([5])}

for v4 in [1, 2]:
    defs_b = {
        0: (0, 1), 1: (1, 1), 2: (2, 1),
        3: (3, 1), 4: (2, 2), 5: (4, v4),
        6: (0, 0), 7: (1, 0), 8: (2, 0),
        9: (3, 0), 10: (4, 0),
    }
    move_func_b = lambda idx: defs_b[idx]

    config = [0] * n
    cycle = [tuple(config)]
    total_ord = [0]
    total_con = [0]
    total_sh = [0]
    total_nosh = [0]
    seen = set()

    t0 = time.time()

    def backtrack_b(done, config, cycle):
        if len(done) == 11:
            total_ord[0] += 1
            cycle_list = list(cycle)
            if cycle_list[-1] != cycle_list[0]:
                return
            cycle_list = cycle_list[:-1]
            if len(set(cycle_list)) != len(cycle_list):
                return
            for idx in range(len(cycle_list)):
                c = cycle_list[idx]
                c_next = cycle_list[(idx + 1) % len(cycle_list)]
                if sum(1 for j in range(n) if c[j] != c_next[j]) != 1:
                    return
            ck = tuple(cycle_list)
            if ck in seen:
                return
            seen.add(ck)
            ok, det, msg = check_cycle_consistency(cycle_list, n, ms_b)
            if not ok:
                return
            total_con[0] += 1
            good_set = set(cycle_list)
            shadow = find_shadow_cycle(det, good_set, ms_b, n)
            if shadow:
                total_sh[0] += 1
            else:
                total_nosh[0] += 1
                print(f"  *** NO SHADOW! v4={v4} ***")
            return

        for m_idx in range(11):
            if m_idx in done:
                continue
            if m_idx in deps_b and not deps_b[m_idx].issubset(done):
                continue
            proc, new_val = move_func_b(m_idx)
            if config[proc] == new_val:
                continue
            old_val = config[proc]
            config[proc] = new_val
            cycle.append(tuple(config))
            backtrack_b(done | frozenset([m_idx]), config, cycle)
            config[proc] = old_val
            cycle.pop()

    backtrack_b(frozenset(), config, cycle)
    t1 = time.time()

    print(f"ms=(2,2,3,2,3) P2-3state v4={v4}: orderings={total_ord[0]}, "
          f"consistent={total_con[0]}, shadow={total_sh[0]}, no_shadow={total_nosh[0]} ({t1-t0:.1f}s)")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("If all results show 0 'no_shadow', then shadow cycles exist for")
print("ALL consistent length-11 good cycles at n=5, completing the proof")
print("that the obstruction is independent of cycle structure and length.")
