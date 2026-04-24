#!/usr/bin/env python3
"""Check gap=1 case for the entry conflict argument.

For sub-threshold multisets (product < 4*3^(n-2)) with >=3 binary,
enumerate all zero-winding good cycles and check:
1. Does every such cycle have some binary processor with consecutive firings?
2. What does the global min gap look like? Can it be 1?
3. If gap=1 at the global min, what structure do the binary firings have?

Also: for CW-CCW gap=1 at edge (p, rp) with rp binary,
since rp fires at step a+1, and rp fires >= 2 times total (binary, even, >=2),
find the consecutive firing pair for rp and check contiguous_run applies.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system, all_configs, privileged_set, apply_move

def get_good_cycle(ms, fs):
    """Extract the good cycle as list of (config, mover) pairs."""
    n = len(ms)
    configs = list(all_configs(ms))
    single_priv = {c for c in configs if len(privileged_set(c, fs, ms)) == 1}

    # Build functional graph on single-priv configs
    succ = {}
    mover_map = {}
    for c in single_priv:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            i = priv[0]
            s = apply_move(c, i, fs, ms)
            if s in single_priv:
                succ[c] = s
                mover_map[c] = i

    # Find cycle
    visited = set()
    start = next(iter(succ))
    path = [start]
    visited.add(start)
    c = succ[start]
    while c != start:
        if c in visited or c not in succ:
            return None
        path.append(c)
        visited.add(c)
        c = succ[c]

    cycle = [(path[i], mover_map[path[i]]) for i in range(len(path))]
    return cycle

def analyze_cycle(cycle, ms, n):
    """Analyze a good cycle for zero winding, gap structure, etc."""
    L = len(cycle)
    movers = [cycle[i][1] for i in range(L)]

    # Compute direction at each step
    directions = []
    for i in range(L):
        mover_now = movers[i]
        mover_next = movers[(i + 1) % L]
        if mover_next == (mover_now + 1) % n:
            directions.append('CW')
        elif mover_next == (mover_now - 1) % n:
            directions.append('CCW')
        else:
            directions.append('STAY')

    # CW step count
    cw_count = sum(1 for d in directions if d == 'CW')
    ccw_count = sum(1 for d in directions if d == 'CCW')

    # Edge crossings: edge (p, right(p)) has CW crossing when mover=p and dir=CW,
    # CCW crossing when mover=right(p) and dir=CCW.
    # Actually: CW crossing at edge (p, p+1): mover=p, dir=CW
    # CCW crossing at edge (p, p+1): mover=p+1, dir=CCW

    # Zero winding: for each edge, count CW - CCW crossings
    edge_net = {}
    for p in range(n):
        rp = (p + 1) % n
        cw_cross = sum(1 for i in range(L) if movers[i] == p and directions[i] == 'CW')
        ccw_cross = sum(1 for i in range(L) if movers[i] == rp and directions[i] == 'CCW')
        edge_net[p] = cw_cross - ccw_cross

    is_zero_winding = all(v == 0 for v in edge_net.values())

    # Check no safe processor
    has_safe = False
    for q in range(n):
        lq = (q - 1) % n
        rq = (q + 1) % n
        if all(movers[i] != q and movers[i] != lq and movers[i] != rq for i in range(L)):
            has_safe = True
            break

    # Binary processors
    binary_procs = [p for p in range(n) if ms[p] == 2]

    # Check consecutive firings for each binary proc
    binary_has_consec = {}
    for p in binary_procs:
        fire_steps = [i for i in range(L) if movers[i] == p]
        has_consec = False
        for i in range(len(fire_steps) - 1):
            if fire_steps[i + 1] == fire_steps[i] + 1:
                has_consec = True
                break
        # Also check wrap-around
        if len(fire_steps) >= 2 and fire_steps[-1] == L - 1 and fire_steps[0] == 0:
            has_consec = True
        binary_has_consec[p] = has_consec

    any_binary_consec = any(binary_has_consec.values())

    # Find all paired crossings and their gaps
    min_gap = float('inf')
    min_gap_info = None
    for p in range(n):
        rp = (p + 1) % n
        # Find all crossings at edge (p, rp)
        crossings = []
        for i in range(L):
            if movers[i] == p and directions[i] == 'CW':
                crossings.append((i, 'CW'))
            elif movers[i] == rp and directions[i] == 'CCW':
                crossings.append((i, 'CCW'))

        # Find paired opposite-direction crossings
        for idx1 in range(len(crossings)):
            for idx2 in range(idx1 + 1, len(crossings)):
                s1, d1 = crossings[idx1]
                s2, d2 = crossings[idx2]
                if d1 != d2:
                    # Check no crossing between s1 and s2
                    has_interior = False
                    for idx3 in range(len(crossings)):
                        s3, _ = crossings[idx3]
                        if s1 < s3 < s2:
                            has_interior = True
                            break
                    if not has_interior:
                        gap = s2 - s1
                        if gap < min_gap:
                            min_gap = gap
                            min_gap_info = (p, s1, s2, d1, d2)

    return {
        'L': L,
        'is_zero_winding': is_zero_winding,
        'has_safe': has_safe,
        'cw_count': cw_count,
        'binary_procs': binary_procs,
        'binary_has_consec': binary_has_consec,
        'any_binary_consec': any_binary_consec,
        'min_gap': min_gap,
        'min_gap_info': min_gap_info,
        'edge_net': edge_net,
    }


def check_sub_threshold_multisets(n):
    """Check all sub-threshold multisets at given n."""
    threshold = 4 * 3**(n-2)

    # Generate multisets with >= 3 binary (state=2) and product < threshold
    # State counts >= 2
    from itertools import combinations_with_replacement

    # Enumerate possible state vectors
    results = {'gap1_found': 0, 'gap1_no_consec': 0, 'total_zw': 0, 'total_cycles': 0}

    # For small n, enumerate directly
    max_state = min(n + 2, 10)  # cap state count

    # Generate all state vectors with product < threshold, >= 3 binary
    def gen_state_vectors(pos, current, prod_so_far):
        if pos == n:
            binary_count = sum(1 for x in current if x == 2)
            if binary_count >= 3 and prod_so_far < threshold:
                yield tuple(current)
            return
        for s in range(2, max_state + 1):
            new_prod = prod_so_far * s
            if new_prod >= threshold * max_state**(n - pos - 1):
                continue  # prune
            if new_prod < threshold or pos < n - 1:
                current.append(s)
                yield from gen_state_vectors(pos + 1, current, new_prod)
                current.pop()

    # Actually for n=5..9, just enumerate all valid multisets
    # This is faster with a simpler approach
    from itertools import product as cart

    count = 0
    gap1_examples = []

    for ms_tuple in cart(*(range(2, max_state + 1) for _ in range(n))):
        ms = list(ms_tuple)
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue
        binary_count = sum(1 for m in ms if m == 2)
        if binary_count < 3:
            continue

        count += 1
        if count % 100 == 0:
            print(f"  Checked {count} multisets...", flush=True)

        # Try to build a valid system
        # We don't have a universal builder for arbitrary ms,
        # so use exhaustive search for very small configs
        total_configs = prod
        if total_configs > 50000:
            continue

        # Use verifier to search for valid systems
        # Actually, we need to check ALL good cycles, not just one system.
        # For the lower bound proof, we need to show that NO system works.
        # The claim is: for any transition functions, any good cycle has entry conflict.

        # For checking gap=1: we just need examples of good cycles.
        # Let's use some specific systems.
        pass

    print(f"  Total multisets checked: {count}")
    return results


def check_cup2_gap(n):
    """Check gap structure for the CUP-2 system at given n."""
    from cup2_theorem import build_system
    ms, fs = build_system(n)
    cycle = get_good_cycle(ms, fs)
    if cycle is None:
        print(f"  n={n}: no cycle found")
        return

    info = analyze_cycle(cycle, ms, n)
    print(f"  n={n}: L={info['L']}, zw={info['is_zero_winding']}, "
          f"safe={info['has_safe']}, cw={info['cw_count']}, "
          f"min_gap={info['min_gap']}")
    print(f"    binary={info['binary_procs']}, "
          f"consec={info['binary_has_consec']}, "
          f"any_consec={info['any_binary_consec']}")
    if info['min_gap_info']:
        p, s1, s2, d1, d2 = info['min_gap_info']
        print(f"    min_gap at edge {p}: steps {s1}({d1})->{s2}({d2}), gap={s2-s1}")


def check_sol3_gap(n):
    """Check gap for Dijkstra's Solution 3 (ms=(2,3,...,3))."""
    ms = [2] + [3] * (n - 1)
    # Build Sol 3 transition functions
    # Sol3 v1: f_0(L,S,R) = (S+1)%2 if S==L else S
    # For i > 0: f_i(L,S,R) = L if S != L else S
    fs = []
    # P0: binary, fires when S == L
    def f0(L, S, R):
        return (S + 1) % 2 if S == L else S
    fs.append(f0)
    for i in range(1, n):
        def fi(L, S, R, m=ms[i]):
            return L if S != L else S
        fs.append(fi)

    cycle = get_good_cycle(ms, fs)
    if cycle is None:
        print(f"  Sol3 n={n}: no cycle found")
        return

    info = analyze_cycle(cycle, ms, n)
    print(f"  Sol3 n={n}: L={info['L']}, zw={info['is_zero_winding']}, "
          f"safe={info['has_safe']}, cw={info['cw_count']}, "
          f"min_gap={info['min_gap']}")
    print(f"    binary={info['binary_procs']}, "
          f"consec={info['binary_has_consec']}, "
          f"any_consec={info['any_binary_consec']}")


def check_all_cycles_at_ms(ms, max_systems=1000):
    """For given ms, enumerate random/all transition functions and check all good cycles."""
    n = len(ms)
    prod = 1
    for m in ms:
        prod *= m

    # For very small configs, try exhaustive
    # Actually let's just check a few hand-built systems
    pass


def investigate_gap1_globally():
    """Main investigation: does gap=1 occur at global min? If so, what happens?"""
    print("="*60)
    print("INVESTIGATION: Gap=1 at global minimum crossing")
    print("="*60)

    print("\n--- CUP-2 system (ms=(2,3,...,3,2)) ---")
    for n in range(5, 13):
        check_cup2_gap(n)

    print("\n--- Sol3 v1 (ms=(2,3,...,3)) ---")
    for n in range(5, 10):
        check_sol3_gap(n)

    # Now check: for the lower bound, what matters is sub-threshold multisets.
    # At n=9, sub-threshold means product < 4*3^7 = 8748.
    # All such multisets with >= 3 binary have product <= 7776 = 2^5 * 3^5.
    # Let's check specific systems.
    print("\n--- M_5 = 96 witness (ms=[2,2,2,3,4]) ---")
    # From memory: this is a valid system
    # Let's try a few sub-threshold multisets with manual systems

    # The key question for the Lean proof:
    # Given CW-CCW gap=1 at global min with right(p) binary,
    # right(p) fires >= 2 times. Find consecutive firings of right(p).
    # This always gives entry conflict via contiguous_run or gap1.
    #
    # PROOF SKETCH for gap=1:
    # 1. right(p) is binary, fires at step b = a+1
    # 2. binary_fireCount_ge_two: right(p) fires >= 2 times
    # 3. exists_two_firing_steps: get s1 < s2 with moverAt(s1) = moverAt(s2) = right(p)
    # 4. exists_consecutive_firing_pair: get a' < b' with moverAt(a') = moverAt(b') = right(p)
    #    and no right(p) firing between
    # 5. Case b' - a' = 1: right(p) fires at consecutive steps a' and a'+1 = b'
    #    - Extend to maximal run: find t >= b' such that right(p) fires at a'..t
    #      and moverAt(t+1) != right(p) (or t+1 wraps)
    #    - If t >= a' + 1 (always true since b' = a'+1):
    #      contiguous_run_entry_conflict gives hasEntryConflict
    # 6. Case b' - a' >= 2: gap >= 2 between consecutive right(p) firings
    #    - Hmm, this doesn't directly give contiguous_run...
    #    - But what is the mover between a' and b'?
    #    - NOT right(p) by assumption.
    #    - Does the mover stay? If it CW/CCW from some position, it creates edge crossings.

    # Let's check case 6 empirically
    print("\n--- Detailed firing structure for binary procs ---")
    from cup2_theorem import build_system
    for n in [5, 7, 9, 11]:
        ms, fs = build_system(n)
        cycle = get_good_cycle(ms, fs)
        if cycle is None:
            continue
        L = len(cycle)
        movers = [cycle[i][1] for i in range(L)]
        binary_procs = [p for p in range(n) if ms[p] == 2]

        print(f"\n  n={n}, L={L}, binary={binary_procs}")
        for p in binary_procs:
            fire_steps = [i for i in range(L) if movers[i] == p]
            gaps = [fire_steps[i+1] - fire_steps[i] for i in range(len(fire_steps)-1)]
            print(f"    P{p}: fires at {fire_steps}, gaps={gaps}")

    # KEY INSIGHT:
    # For the gap=1 case in the LEAN PROOF, we don't need the global min gap.
    # We just need: right(p_g) is binary and fires >= 2 times.
    # consecutive firing pair of right(p_g) gives entry conflict:
    # - If consecutive (gap=0 between them): gap1_entry_conflict
    # - If gap >= 1: contiguous_run might not apply directly.
    #
    # WAIT: consecutive firing pair means moverAt(a')=moverAt(b')=right(p_g)
    # with NO right(p_g) firing between. This doesn't mean they fire at
    # adjacent steps. It means right(p_g) fires at a', then fires again at b',
    # and doesn't fire at any step strictly between.
    #
    # So b' - a' could be large. Between a' and b', the mover is something
    # other than right(p_g). This gives us a contiguous run? No.
    #
    # ALTERNATIVE: Consider the maximal run of right(p_g) at step a+1.
    # - Step a+1: right(p_g) fires (CCW crossing)
    # - Step a+2: mover = p_g (from CCW). So right(p_g) does NOT fire.
    # So right(p_g) fires at step a+1, does NOT fire at step a+2.
    # right(p_g) fires again at some later step (since fireCount >= 2).
    # At that later step, say step c, right(p_g) fires again.
    # Between a+1 and c, right(p_g) does not fire.
    #
    # Now, step a+1 is an isolated firing of right(p_g) (length-1 run).
    # For contiguous_run_entry_conflict, we need a run of length >= 2.
    #
    # So the question is: does right(p_g) EVER fire at two consecutive steps?
    # If yes: contiguous_run gives EC.
    # If no: right(p_g) always fires in isolated bursts of length 1.

    print("\n\n--- Key test: binary fires always have consecutive pair? ---")
    # Check: for every binary proc that fires >= 2 times,
    # does it always have at least one pair of consecutive firings?
    for n in [5, 7, 9, 11]:
        ms, fs = build_system(n)
        cycle = get_good_cycle(ms, fs)
        if cycle is None:
            continue
        L = len(cycle)
        movers = [cycle[i][1] for i in range(L)]
        binary_procs = [p for p in range(n) if ms[p] == 2]

        all_have_consec = True
        for p in binary_procs:
            fire_steps = [i for i in range(L) if movers[i] == p]
            if len(fire_steps) < 2:
                continue
            has_consec = any(fire_steps[i+1] == fire_steps[i] + 1
                           for i in range(len(fire_steps)-1))
            # Check wrap
            if not has_consec and len(fire_steps) >= 2:
                if fire_steps[-1] == L-1 and fire_steps[0] == 0:
                    has_consec = True
            if not has_consec:
                all_have_consec = False
                print(f"  n={n}, P{p}: fires={fire_steps}, NO CONSECUTIVE!")

        if all_have_consec:
            print(f"  n={n}: all binary procs with >=2 fires have consecutive pairs")


if __name__ == '__main__':
    investigate_gap1_globally()
