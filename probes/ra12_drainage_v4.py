"""
RA12 v4: Key structural findings and the alternating-01 pattern.

BREAKTHROUGH from v3: The bad cycle configs for Sol1 are EXACTLY the
alternating-{0,1} configs! Look at ms=(2,2,2,2,2) n=5:

Good cycle: wavefront 11100 -> 11110 -> 11111 -> 01111 -> 00111 -> ...
            (contiguous blocks of 0s and 1s)

Bad cycle: 10100 -> 11010 -> 11011 -> 01011 -> 01001 -> 01101 -> 00101 -> ...
           (ALTERNATING pattern - 0s and 1s interleaved)

20 bad cycle configs = all binary strings with the "alternating" property.
These are the configs with L != S at every position (every proc privileged!
or exactly 3 privileged) — the "anti-wavefront" configs.

For Sol1: P_i privileged iff L_i == S_i (for P_0) or L_i != S_i (for others).
So all configs where c[i-1] != c[i] for all i=1,...,n-1 are bad.
These are the "anti-matching" or "checkerboard" configs.

QUESTION: Is this specific to Sol1, or is there a deeper structure?
For the M_5=96 valid system with different rules: NO bad cycles. Why?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
from collections import defaultdict, deque, Counter
from verifier import all_configs, privileged_set, apply_move


def build_sol1_style(ms):
    n = len(ms)
    fs = []
    for i in range(n):
        m = ms[i]
        if i == 0:
            def f(L, S, R, m=m):
                if L == S: return (S + 1) % m
                return S
        else:
            def f(L, S, R, m=m):
                if L != S: return L % m
                return S
        fs.append(f)
    return fs


def analyze_bad_cycle_pattern(ms, label=""):
    """Identify the structural pattern in bad cycle configs."""
    n = len(ms)
    P = 1
    for m in ms: P *= m
    fs = build_sol1_style(list(ms))

    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}

    # Find good cycle
    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        s = apply_move(c, priv_map[c][0], fs, ms)
        succ[c] = (s, priv_map[c][0])

    good_cand = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
        if to_rm:
            good_cand -= to_rm
            changed = True

    visited = set()
    cycle_set = set()
    for c in good_cand:
        if c in visited: continue
        path, ps = [], set()
        node = c
        while node not in visited and node not in ps:
            path.append(node); ps.add(node)
            node = succ[node][0]
        if node in ps:
            cyc = path[path.index(node):]
            cycle_set.update(cyc)
        visited.update(path)

    # Find bad cycle configs
    bad = set(configs) - cycle_set
    bad_succs = defaultdict(set)
    for c in bad:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            if s in bad:
                bad_succs[c].add(s)

    in_cycle = set()
    for c in bad:
        if not bad_succs[c]: continue
        reachable = set(bad_succs[c])
        queue = deque(bad_succs[c])
        while queue:
            node = queue.popleft()
            if node == c:
                in_cycle.add(c)
                break
            for s in bad_succs[node]:
                if s not in reachable:
                    reachable.add(s)
                    queue.append(s)

    print(f"\n{label}: ms={list(ms)}, P={P}, CL={len(cycle_set)}, bad_in_cycle={len(in_cycle)}")

    # Characterize: are bad cycle configs = "all L_i != S_i for i>0" configs?
    # Sol1: P_0 priv iff c[n-1] == c[0]; P_i (i>0) priv iff c[i-1] != c[i]
    anti_matching = set()
    for c in configs:
        # Check if c[i-1] != c[i] for all i = 1, ..., n-1
        all_diff = all(c[(i-1)%n] != c[i] for i in range(1, n))
        if all_diff:
            anti_matching.add(c)

    print(f"  Anti-matching configs (c[i-1]!=c[i] for i>0): {len(anti_matching)}")
    print(f"  Intersection with bad cycles: {len(in_cycle & anti_matching)}")
    print(f"  Bad cycles \\ anti-matching: {len(in_cycle - anti_matching)}")
    print(f"  Anti-matching \\ bad cycles: {len(anti_matching - in_cycle)}")

    # Also check: c[i-1] != c[i] for ALL i (including wraparound)
    full_anti = set()
    for c in configs:
        all_diff = all(c[(i-1)%n] != c[i] for i in range(n))
        if all_diff:
            full_anti.add(c)

    print(f"  Full anti-matching (ALL i): {len(full_anti)}")
    print(f"  Intersection with bad cycles: {len(in_cycle & full_anti)}")

    return in_cycle, anti_matching, full_anti, cycle_set


def main():
    print("=" * 70)
    print("BAD CYCLE STRUCTURAL PATTERN")
    print("=" * 70)

    # All-binary at various n
    for n in [4, 5, 6, 7]:
        ms = tuple([2]*n)
        analyze_bad_cycle_pattern(ms, f"All binary n={n}")

    # Mixed
    for ms in [(2,2,2,3,3), (2,2,2,2,3), (2,2,2,3,4)]:
        analyze_bad_cycle_pattern(ms, "Mixed")

    # ─── THE KEY: How the bad cycle relates to the good cycle ───
    print("\n\n" + "=" * 70)
    print("GOOD vs BAD CYCLE STRUCTURE")
    print("=" * 70)

    ms = [2]*5
    n = 5
    fs = build_sol1_style(ms)
    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}

    in_cycle, anti_match, full_anti, cycle_set = analyze_bad_cycle_pattern(ms, "n=5 binary")

    print(f"\nGood cycle configs (sorted):")
    for c in sorted(cycle_set):
        adj_diffs = sum(1 for i in range(1, n) if c[i-1] != c[i])
        print(f"  {c}  adj_diffs={adj_diffs}")

    print(f"\nBad cycle configs (sorted):")
    for c in sorted(in_cycle):
        adj_diffs = sum(1 for i in range(1, n) if c[i-1] != c[i])
        wrap_diff = 1 if c[n-1] != c[0] else 0
        print(f"  {c}  adj_diffs={adj_diffs}  wrap_diff={wrap_diff}")

    print(f"\nRemaining configs (neither good nor bad cycle):")
    remaining = set(configs) - cycle_set - in_cycle
    for c in sorted(remaining):
        adj_diffs = sum(1 for i in range(1, n) if c[i-1] != c[i])
        print(f"  {c}  adj_diffs={adj_diffs}")

    # ─── Hamming distance analysis ───
    print(f"\n\n{'='*70}")
    print("HAMMING DISTANCE FROM GOOD CYCLE")
    print("=" * 70)

    for ms_test in [(2,2,2,2,2), (2,2,2,3,3)]:
        n = len(ms_test)
        fs = build_sol1_style(list(ms_test))
        configs = list(all_configs(ms_test))
        priv_map = {c: privileged_set(c, fs, ms_test) for c in configs}

        # Find cycle
        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        succ = {}
        for c in single_priv:
            s = apply_move(c, priv_map[c][0], fs, ms_test)
            succ[c] = (s, priv_map[c][0])
        good_cand = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
            if to_rm:
                good_cand -= to_rm
                changed = True
        cycle_set = set()
        visited = set()
        for c in good_cand:
            if c in visited: continue
            path, ps = [], set()
            node = c
            while node not in visited and node not in ps:
                path.append(node); ps.add(node)
                node = succ[node][0]
            if node in ps:
                cycle_set.update(path[path.index(node):])
            visited.update(path)

        # Min Hamming distance from each config to the good cycle
        print(f"\nms={list(ms_test)}:")
        for c in sorted(configs):
            min_ham = min(sum(1 for i in range(n) if c[i] != gc[i]) for gc in cycle_set)
            priv = priv_map[c]
            in_gc = c in cycle_set
            status = "GOOD" if in_gc else ""
            print(f"  {c}  min_ham={min_ham}  priv={len(priv)}  {status}")

    # ─── OBSERVATION: Bad cycles are the "complement" of the good cycle ───
    print(f"\n\n{'='*70}")
    print("COMPLEMENT STRUCTURE")
    print("=" * 70)

    ms = [2]*5
    n = 5
    fs = build_sol1_style(ms)

    in_cycle, _, _, cycle_set = analyze_bad_cycle_pattern(ms, "n=5")

    # For all-binary: check if bad cycle = bitwise complement of good cycle shifted
    print("\nGood cycle:")
    good_list = sorted(cycle_set)
    for c in good_list:
        comp = tuple(1-x for x in c)
        in_bad = comp in in_cycle
        print(f"  {c} -> complement {comp}: in_bad={in_bad}")

    # Check: is the bad cycle the SAME cycle with alternating values shifted?
    print("\nBad cycle configs as XOR with (1,0,1,0,1):")
    xor_mask = tuple(i % 2 for i in range(5))
    for c in sorted(in_cycle):
        xored = tuple((c[i] + xor_mask[i]) % 2 for i in range(5))
        in_good = xored in cycle_set
        print(f"  {c} XOR {xor_mask} = {xored}: in_good={in_good}")

    # ─── CRITICAL: transition-function independence ───
    print(f"\n\n{'='*70}")
    print("TRANSITION-FUNCTION INDEPENDENCE TEST")
    print("=" * 70)
    print("Do bad cycles exist for ALL possible transition functions")
    print("at sub-threshold, or just Sol1?")
    print()

    # For n=4, ms=(2,2,2,2), P=16: enumerate ALL transition functions
    # Too many (2^(2*2*2) per proc = 2^8 = 256 per proc, 256^4 total = 4B)
    # Instead: enumerate STRUCTURED functions (incrementing or decrementing)

    ms4 = [2,2,2,2]
    n4 = 4

    # For binary procs: f(L,S,R) is determined by which of the 8 contexts
    # (L,S,R) trigger a privilege (change S).
    # There are 2^8 = 256 possible functions per proc (for each context, either flip or stay)
    # But many are equivalent. Let's try a sample.

    import random
    rng = random.Random(42)

    bad_cycle_counts = []
    no_cycle_count = 0
    has_bad_count = 0
    no_bad_count = 0

    # Systematic: for each proc, privilege iff some condition on (L,S,R)
    # Try 1000 random systems
    for trial in range(2000):
        fs = []
        for i in range(n4):
            # Random table: for each (L,S,R), flip S with probability p
            table = {}
            for L in range(2):
                for S in range(2):
                    for R in range(2):
                        table[(L,S,R)] = rng.randint(0, 1)
            def f(L, S, R, t=table):
                return t[(L,S,R)]
            fs.append(f)

        configs = list(all_configs(ms4))
        priv_map = {c: privileged_set(c, fs, ms4) for c in configs}

        # Check for dead configs
        if any(len(priv_map[c]) == 0 for c in configs):
            continue  # skip systems with dead configs

        # Find good cycle
        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        succ = {}
        for c in single_priv:
            s = apply_move(c, priv_map[c][0], fs, ms4)
            succ[c] = (s, priv_map[c][0])

        good_cand = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
            if to_rm:
                good_cand -= to_rm
                changed = True

        cycle_set = set()
        visited = set()
        for c in good_cand:
            if c in visited: continue
            path, ps = [], set()
            node = c
            while node not in visited and node not in ps:
                path.append(node); ps.add(node)
                node = succ[node][0]
            if node in ps:
                cycle_set.update(path[path.index(node):])
            visited.update(path)

        if not cycle_set:
            no_cycle_count += 1
            continue

        # Check fairness
        movers = set()
        for c in cycle_set:
            if c in succ:
                _, p = succ[c]
                movers.add(p)
        if movers != set(range(n4)):
            no_cycle_count += 1
            continue

        # Find bad cycles
        bad = set(configs) - cycle_set
        bad_succs = defaultdict(set)
        for c in bad:
            for p in priv_map[c]:
                s = apply_move(c, p, fs, ms4)
                if s in bad:
                    bad_succs[c].add(s)

        has_bad = False
        for c in bad:
            if not bad_succs[c]: continue
            reachable = set(bad_succs[c])
            queue = deque(bad_succs[c])
            while queue:
                node = queue.popleft()
                if node == c:
                    has_bad = True
                    break
                for s in bad_succs[node]:
                    if s not in reachable:
                        reachable.add(s)
                        queue.append(s)
            if has_bad:
                break

        if has_bad:
            has_bad_count += 1
        else:
            no_bad_count += 1
            # This is a VALID system! Print it
            print(f"  Trial {trial}: VALID! CL={len(cycle_set)}, ms={ms4}, P={16}")

    print(f"\n  n=4, ms=(2,2,2,2), P=16 (sub-threshold={4*3**2}=36)")
    print(f"  Random trials: {no_cycle_count} no fair cycle, {has_bad_count} had bad cycles, {no_bad_count} NO bad cycles (VALID)")
    print(f"  Valid fraction among fair-cycle systems: {no_bad_count}/{has_bad_count+no_bad_count}")

    # ─── Do the same for n=4, ms=(2,2,2,3), P=24 ───
    ms4b = [2,2,2,3]
    bad_count2 = 0
    no_bad_count2 = 0
    fair_count = 0

    for trial in range(2000):
        fs = []
        for i in range(4):
            m = ms4b[i]
            mL = ms4b[(i-1)%4]
            mR = ms4b[(i+1)%4]
            table = {}
            for L in range(mL):
                for S in range(m):
                    for R in range(mR):
                        table[(L,S,R)] = rng.randint(0, m-1)
            def f(L, S, R, t=table):
                return t[(L,S,R)]
            fs.append(f)

        configs = list(all_configs(ms4b))
        priv_map = {c: privileged_set(c, fs, ms4b) for c in configs}
        if any(len(priv_map[c]) == 0 for c in configs):
            continue

        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        succ = {}
        for c in single_priv:
            s = apply_move(c, priv_map[c][0], fs, ms4b)
            succ[c] = (s, priv_map[c][0])

        good_cand = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
            if to_rm:
                good_cand -= to_rm
                changed = True

        cycle_set = set()
        visited = set()
        for c in good_cand:
            if c in visited: continue
            path, ps = [], set()
            node = c
            while node not in visited and node not in ps:
                path.append(node); ps.add(node)
                node = succ[node][0]
            if node in ps:
                cycle_set.update(path[path.index(node):])
            visited.update(path)

        if not cycle_set:
            continue

        movers = set()
        for c in cycle_set:
            if c in succ:
                _, p = succ[c]
                movers.add(p)
        if movers != set(range(4)):
            continue

        fair_count += 1

        bad = set(configs) - cycle_set
        bad_succs = defaultdict(set)
        for c in bad:
            for p in priv_map[c]:
                s = apply_move(c, p, fs, ms4b)
                if s in bad:
                    bad_succs[c].add(s)

        has_bad = False
        for c in bad:
            if not bad_succs[c]: continue
            reachable = set(bad_succs[c])
            queue = deque(bad_succs[c])
            while queue:
                node = queue.popleft()
                if node == c:
                    has_bad = True
                    break
                for s in bad_succs[node]:
                    if s not in reachable:
                        reachable.add(s)
                        queue.append(s)
            if has_bad:
                break

        if has_bad:
            bad_count2 += 1
        else:
            no_bad_count2 += 1

    print(f"\n  n=4, ms=(2,2,2,3), P=24 (sub-threshold={4*3**2}=36)")
    print(f"  Fair-cycle systems found: {fair_count}")
    print(f"  With bad cycles: {bad_count2}, without (VALID): {no_bad_count2}")

    # ─── ALSO at threshold: n=4, ms=(2,2,3,3), P=36 ───
    ms4c = [2,2,3,3]
    bad_count3 = 0
    no_bad_count3 = 0
    fair_count3 = 0

    for trial in range(2000):
        fs = []
        for i in range(4):
            m = ms4c[i]
            mL = ms4c[(i-1)%4]
            mR = ms4c[(i+1)%4]
            table = {}
            for L in range(mL):
                for S in range(m):
                    for R in range(mR):
                        table[(L,S,R)] = rng.randint(0, m-1)
            def f(L, S, R, t=table):
                return t[(L,S,R)]
            fs.append(f)

        configs = list(all_configs(ms4c))
        priv_map = {c: privileged_set(c, fs, ms4c) for c in configs}
        if any(len(priv_map[c]) == 0 for c in configs):
            continue

        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        succ = {}
        for c in single_priv:
            s = apply_move(c, priv_map[c][0], fs, ms4c)
            succ[c] = (s, priv_map[c][0])

        good_cand = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
            if to_rm:
                good_cand -= to_rm
                changed = True

        cycle_set = set()
        visited = set()
        for c in good_cand:
            if c in visited: continue
            path, ps = [], set()
            node = c
            while node not in visited and node not in ps:
                path.append(node); ps.add(node)
                node = succ[node][0]
            if node in ps:
                cycle_set.update(path[path.index(node):])
            visited.update(path)

        if not cycle_set:
            continue

        movers = set()
        for c in cycle_set:
            if c in succ:
                _, p = succ[c]
                movers.add(p)
        if movers != set(range(4)):
            continue

        fair_count3 += 1

        bad = set(configs) - cycle_set
        bad_succs = defaultdict(set)
        for c in bad:
            for p in priv_map[c]:
                s = apply_move(c, p, fs, ms4c)
                if s in bad:
                    bad_succs[c].add(s)

        has_bad = False
        for c in bad:
            if not bad_succs[c]: continue
            reachable = set(bad_succs[c])
            queue = deque(bad_succs[c])
            while queue:
                node = queue.popleft()
                if node == c:
                    has_bad = True
                    break
                for s in bad_succs[node]:
                    if s not in reachable:
                        reachable.add(s)
                        queue.append(s)
            if has_bad:
                break

        if has_bad:
            bad_count3 += 1
        else:
            no_bad_count3 += 1

    print(f"\n  n=4, ms=(2,2,3,3), P=36 (AT threshold={4*3**2}=36)")
    print(f"  Fair-cycle systems found: {fair_count3}")
    print(f"  With bad cycles: {bad_count3}, without (VALID): {no_bad_count3}")

    # ─── Above threshold ───
    ms4d = [3,3,3,3]
    bad_count4 = 0
    no_bad_count4 = 0
    fair_count4 = 0

    for trial in range(2000):
        fs = []
        for i in range(4):
            table = {}
            for L in range(3):
                for S in range(3):
                    for R in range(3):
                        table[(L,S,R)] = rng.randint(0, 2)
            def f(L, S, R, t=table):
                return t[(L,S,R)]
            fs.append(f)

        configs = list(all_configs(ms4d))
        priv_map = {c: privileged_set(c, fs, ms4d) for c in configs}
        if any(len(priv_map[c]) == 0 for c in configs):
            continue

        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        succ = {}
        for c in single_priv:
            s = apply_move(c, priv_map[c][0], fs, ms4d)
            succ[c] = (s, priv_map[c][0])

        good_cand = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
            if to_rm:
                good_cand -= to_rm
                changed = True

        cycle_set = set()
        visited = set()
        for c in good_cand:
            if c in visited: continue
            path, ps = [], set()
            node = c
            while node not in visited and node not in ps:
                path.append(node); ps.add(node)
                node = succ[node][0]
            if node in ps:
                cycle_set.update(path[path.index(node):])
            visited.update(path)

        if not cycle_set:
            continue

        movers = set()
        for c in cycle_set:
            if c in succ:
                _, p = succ[c]
                movers.add(p)
        if movers != set(range(4)):
            continue

        fair_count4 += 1

        bad = set(configs) - cycle_set
        bad_succs = defaultdict(set)
        for c in bad:
            for p in priv_map[c]:
                s = apply_move(c, p, fs, ms4d)
                if s in bad:
                    bad_succs[c].add(s)

        has_bad = False
        for c in bad:
            if not bad_succs[c]: continue
            reachable = set(bad_succs[c])
            queue = deque(bad_succs[c])
            while queue:
                node = queue.popleft()
                if node == c:
                    has_bad = True
                    break
                for s in bad_succs[node]:
                    if s not in reachable:
                        reachable.add(s)
                        queue.append(s)
            if has_bad:
                break

        if has_bad:
            bad_count4 += 1
        else:
            no_bad_count4 += 1

    print(f"\n  n=4, ms=(3,3,3,3), P=81 (above threshold={4*3**2}=36)")
    print(f"  Fair-cycle systems found: {fair_count4}")
    print(f"  With bad cycles: {bad_count4}, without (VALID): {no_bad_count4}")


if __name__ == "__main__":
    main()
