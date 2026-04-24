#!/usr/bin/env python3
"""binscc_conflict_mechanism.py — Identify the universal conflict mechanism.

Focus: Why does EVERY good cycle with ≥3 non-adjacent binary have conflict?
Study the 58 cycles at n=5 that lack sandwich conflict — where IS their conflict?
Then identify the general mechanism.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def analyze_conflicts(ms, n, word, cycle):
    """Return per-proc conflict info."""
    ell = len(cycle)
    result = {}
    for p in range(n):
        mL = (p-1) % n
        mR = (p+1) % n
        mover_set = set()
        nonmover_set = set()
        mover_steps = []
        nonmover_steps = []
        for step in range(ell):
            c = cycle[step]
            L, S, R = c[mL], c[p], c[mR]
            if word[step] == p:
                mover_set.add((L, S, R))
                mover_steps.append((step, L, S, R))
            else:
                nonmover_set.add((L, S, R))
                nonmover_steps.append((step, L, S, R))
        overlap = mover_set & nonmover_set
        result[p] = {
            'mover': mover_set, 'nonmover': nonmover_set,
            'overlap': overlap, 'mover_steps': mover_steps,
            'nonmover_steps': nonmover_steps,
        }
    return result


def main():
    print("=" * 70)
    print("CONFLICT MECHANISM: WHY EVERY CYCLE HAS CONFLICT")
    print("=" * 70)

    # PART 1: Study the 58 no-sandwich cycles at n=5
    print("\nPART 1: THE 58 NO-SANDWICH CYCLES AT n=5")
    print("=" * 60)

    n, ms = 5, [2, 3, 2, 3, 2]
    bin_procs = [0, 2, 4]
    sandwiched = [1, 3]

    words = enumerate_mover_words(ms, n, 21)
    print(f"  {len(words)} mover words")

    no_sandwich = []
    all_conflict = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue

        info = analyze_conflicts(ms, n, word, cycle)

        # Check sandwich conflict
        has_sandwich = any(info[q]['overlap'] for q in sandwiched)
        # Check any conflict
        has_any = any(info[p]['overlap'] for p in range(n))

        if has_any:
            all_conflict += 1

        if not has_sandwich:
            # Where IS the conflict?
            conflict_at = [p for p in range(n) if info[p]['overlap']]
            no_sandwich.append((word, cycle, info, conflict_at))

    print(f"  Total with ANY conflict: {all_conflict}")
    print(f"  No sandwich conflict: {len(no_sandwich)}")

    if no_sandwich:
        print(f"\n  Analyzing {len(no_sandwich)} no-sandwich cycles:")

        # Where do conflicts occur?
        loc_counter = Counter()
        for word, cycle, info, conflict_at in no_sandwich:
            for p in conflict_at:
                loc_counter[f"P{p}({'BIN' if ms[p]==2 else f'm={ms[p]}'})" ] += 1
        print(f"  Conflict location: {dict(loc_counter)}")

        # Show first few in detail
        for word, cycle, info, conflict_at in no_sandwich[:5]:
            ell = len(cycle)
            print(f"\n    word len={ell}: {word[:20]}...")
            print(f"    Conflict at: {conflict_at}")
            for p in conflict_at:
                ov = info[p]['overlap']
                print(f"      P{p} overlap: {sorted(ov)}")
                for ctx in sorted(ov):
                    m_steps = [s for s in info[p]['mover_steps'] if (s[1],s[2],s[3]) == ctx]
                    nm_steps = [s for s in info[p]['nonmover_steps'] if (s[1],s[2],s[3]) == ctx]
                    print(f"        ({ctx[0]},{ctx[1]},{ctx[2]}): mover@{[s[0] for s in m_steps]} nonmover@{[s[0] for s in nm_steps]}")

            # What's special about sandwich procs?
            for q in sandwiched:
                print(f"      P{q} NM coverage: {len(info[q]['nonmover'])} ctx, mover: {sorted(info[q]['mover'])}")

    # PART 2: Binary UP/DOWN context analysis
    print(f"\n\n{'='*70}")
    print("PART 2: BINARY UP/DOWN CONTEXT OVERLAP")
    print("=" * 70)
    print()
    print("For each binary proc b, check if DOWN creates nonmover at UP context.")
    print("After b fires DOWN (1→0), b is at state 0. Next mover is neighbor.")
    print("b sees (L_down, 0, R_down) as nonmover if that step exists.")
    print()

    # For every cycle, check: right after DOWN, does b see (L_up, 0, R_up)?
    up_down_same = 0  # UP and DOWN at same (L,R)
    down_creates_up = 0  # after DOWN, (L_down, R_down) = (L_up, R_up) as nonmover
    neither = 0
    total_valid = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        total_valid += 1
        ell = len(cycle)

        found_any = False
        for b in bin_procs:
            mL = (b-1) % n
            mR = (b+1) % n

            # Find UP and DOWN steps
            up_step = down_step = None
            for step in range(ell):
                if word[step] == b:
                    if cycle[step][b] == 0:  # state 0 → fires UP
                        up_step = step
                    else:  # state 1 → fires DOWN
                        down_step = step

            if up_step is None or down_step is None:
                continue

            L_up, R_up = cycle[up_step][mL], cycle[up_step][mR]
            L_down, R_down = cycle[down_step][mL], cycle[down_step][mR]

            if (L_up, R_up) == (L_down, R_down):
                up_down_same += 1
                found_any = True
                continue

            # Check: right after DOWN, b is at state 0, same (L,R) as DOWN
            # That nonmover step has context (L_down, 0, R_down)
            # Does (L_down, 0, R_down) = (L_up, 0, R_up)?
            # Only if (L_down, R_down) = (L_up, R_up), which we just ruled out.
            # But the step AFTER DOWN might change (L,R)...
            # Actually: at step down_step, b fires DOWN. Config changes b: 1→0.
            # At step (down_step+1)%ell, some neighbor fires. b is nonmover at
            # (L_down, 0, R_down). This is already ≠ (L_up, 0, R_up).
            # But after more neighbor firings, (L,R) might reach (L_up, R_up).

            # Track b's nonmover while b=0
            # b=0 after DOWN until UP (wrapping)
            nm_while_0 = set()
            step = (down_step + 1) % ell
            while step != up_step:
                if word[step] != b:
                    c = cycle[step]
                    if c[b] == 0:
                        nm_while_0.add((c[mL], c[mR]))
                step = (step + 1) % ell

            if (L_up, R_up) in nm_while_0:
                down_creates_up += 1
                found_any = True

        if not found_any:
            neither += 1

    print(f"  Total valid: {total_valid}")
    print(f"  UP/DOWN same (L,R): {up_down_same} binary firings")
    print(f"  DOWN→UP nonmover path hits UP context: {down_creates_up}")
    print(f"  Neither mechanism: {neither} CYCLES")

    # PART 3: Investigate binary context walk on {0,1}²
    print(f"\n\n{'='*70}")
    print("PART 3: BINARY NEIGHBOR WALK ON {{0,1}}²")
    print("=" * 70)
    print()
    print("For binary b with binary neighbors: track (L,R) walk while b=0 and b=1.")
    print("Each neighbor firing flips one coordinate. Walk on corners of unit square.")
    print()

    # For n=5 [2,3,2,3,2]: b=0 has L=P4(m=2), R=P1(m=3) — NOT binary neighbor
    # b=2 has L=P1(m=3), R=P3(m=3) — NOT binary neighbors!
    # b=4 has L=P3(m=3), R=P0(m=2) — only R is binary
    # So at n=5 alternating, NO binary proc has BOTH neighbors binary.
    # Sandwich only applies to non-binary procs.

    # For binary proc with non-binary neighbors:
    # Context space is larger: m_L × 2 × m_R = 3×2×3 = 18 for b=2
    # Harder to force coverage.

    print("  n=5 [2,3,2,3,2]: No binary proc has both neighbors binary.")
    print("  b=0: L=P4(m=2), R=P1(m=3) → ctx_space = 2×2×3 = 12")
    print("  b=2: L=P1(m=3), R=P3(m=3) → ctx_space = 3×2×3 = 18")
    print("  b=4: L=P3(m=3), R=P0(m=2) → ctx_space = 3×2×2 = 12")
    print()

    # For each binary, count nonmover contexts
    nm_coverage_binary = defaultdict(Counter)

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for b in bin_procs:
            mL = (b-1) % n
            mR = (b+1) % n
            nm = set()
            for step in range(ell):
                if word[step] != b:
                    c = cycle[step]
                    nm.add((c[mL], c[b], c[mR]))
            ctx_space = ms[mL] * 2 * ms[mR]
            nm_coverage_binary[b][len(nm)] += 1

    for b in bin_procs:
        mL = (b-1) % n; mR = (b+1) % n
        ctx_space = ms[mL] * 2 * ms[mR]
        print(f"  P{b} (ctx_space={ctx_space}): NM coverage dist: {dict(sorted(nm_coverage_binary[b].items()))}")

    # PART 4: The fundamental mechanism
    print(f"\n\n{'='*70}")
    print("PART 4: MOVER CONTEXT AT CONFIG JUST AFTER PREV MOVER")
    print("=" * 70)
    print()
    print("Key: when b fires at step k, step k-1 had b's neighbor as mover.")
    print("At step k-1, b was nonmover. The config at step k differs from k-1")
    print("by one coord change (at b's neighbor). So b's nonmover context at k-1")
    print("is CLOSE to b's mover context at k (differs in L or R by one step).")
    print()
    print("If BOTH UP and DOWN have the neighbor firing the SAME side just before,")
    print("then one of them must create a nonmover context that = the other's mover.")
    print()

    # For each binary, track: which neighbor fires just before UP? before DOWN?
    before_up = Counter()
    before_down = Counter()
    match_pattern = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for b in bin_procs:
            mL = (b-1) % n
            mR = (b+1) % n
            for step in range(ell):
                if word[step] != b:
                    continue
                prev = word[(step-1) % ell]
                nxt = word[(step+1) % ell]
                if cycle[step][b] == 0:  # UP
                    side = 'L' if prev == mL else 'R'
                    before_up[(b, side)] += 1
                else:  # DOWN
                    side = 'L' if prev == mL else 'R'
                    before_down[(b, side)] += 1

    print("  Before UP:  ", dict(before_up))
    print("  Before DOWN:", dict(before_down))

    # PART 5: The sharp pigeonhole — binary proc neighbor firing distribution
    print(f"\n\n{'='*70}")
    print("PART 5: NEIGHBOR FIRING PATTERN AROUND BINARY PROCS")
    print("=" * 70)
    print()

    # When b fires UP at step k, the config is c_k. The mover at k-1 was a neighbor.
    # Key: is the context at k-1 (nonmover for b) the same as some OTHER mover of b?

    # Specifically: b fires UP at c_k (b=0), DOWN at c_j (b=1).
    # At step k-1: b nonmover, context = c_{k-1}. This differs from c_k in one neighbor.
    # At step j-1: b nonmover, context = c_{j-1}. This differs from c_j in one neighbor.
    # Question: does c_{k-1}[b] = 0 and c_{k-1}'s (L,S,R) match c_j's mover? No, S differs.
    # Actually: c_{k-1}[b] = 0 (before UP), c_{j-1}[b] = 1 (before DOWN).
    # So: nonmover at k-1 has b=0, differs from UP mover in one coord → could match DOWN? No, b=0≠b=1.
    # nonmover at j-1 has b=1, differs from DOWN mover in one coord → could match UP? No, b=1≠b=0.

    # OK so adjacent-step doesn't directly create cross-state conflict.
    # The conflict must come from FURTHER steps where b is nonmover.

    # Let me study: for each binary, how many nonmover steps at each state?
    nm_by_state = defaultdict(Counter)

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for b in bin_procs:
            count_0 = sum(1 for step in range(ell) if word[step] != b and cycle[step][b] == 0)
            count_1 = sum(1 for step in range(ell) if word[step] != b and cycle[step][b] == 1)
            nm_by_state[b][(count_0, count_1)] += 1

    for b in bin_procs:
        print(f"  P{b} nonmover (state0, state1) counts: {dict(sorted(nm_by_state[b].items()))}")

    # PART 6: THE KEY — (L,R) pair coverage while binary at each state
    print(f"\n\n{'='*70}")
    print("PART 6: (L,R) PAIR COVERAGE WHILE BINARY AT EACH STATE")
    print("=" * 70)
    print()
    print("For binary b: while b=0, how many distinct (L,R) nonmover pairs?")
    print("While b=1? If ALL (L,R) pairs appear as nonmover at a state,")
    print("then the mover context at that state MUST overlap → conflict.")
    print()

    for b in bin_procs:
        mL = (b-1) % n; mR = (b+1) % n
        lr_space = ms[mL] * ms[mR]
        full_at_0 = 0
        full_at_1 = 0

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            ell = len(cycle)

            nm0_lr = set()
            nm1_lr = set()
            for step in range(ell):
                if word[step] != b:
                    c = cycle[step]
                    if c[b] == 0:
                        nm0_lr.add((c[mL], c[mR]))
                    else:
                        nm1_lr.add((c[mL], c[mR]))

            if len(nm0_lr) == lr_space:
                full_at_0 += 1
            if len(nm1_lr) == lr_space:
                full_at_1 += 1

        print(f"  P{b}: (L,R) space={lr_space}, full coverage at state 0: {full_at_0}/{total_valid}, state 1: {full_at_1}/{total_valid}")

    sys.stdout.flush()

    # PART 7: Check if 3-binary COMBINED covers everything
    print(f"\n\n{'='*70}")
    print("PART 7: COMBINED 3-BINARY COVERAGE")
    print("=" * 70)
    print()
    print("For each cycle: does ANY binary proc have full (L,R) at either state?")
    print()

    any_full = 0
    no_full_but_conflict = 0
    no_conflict = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        found_full = False
        found_conflict = False
        for b in bin_procs:
            mL = (b-1) % n; mR = (b+1) % n
            lr_space = ms[mL] * ms[mR]
            mover_set = set()
            nonmover_set = set()
            nm0_lr = set()
            nm1_lr = set()

            for step in range(ell):
                c = cycle[step]
                L, S, R = c[mL], c[b], c[mR]
                if word[step] == b:
                    mover_set.add((L, S, R))
                else:
                    nonmover_set.add((L, S, R))
                    if S == 0:
                        nm0_lr.add((L, R))
                    else:
                        nm1_lr.add((L, R))

            if len(nm0_lr) == lr_space or len(nm1_lr) == lr_space:
                found_full = True
            if mover_set & nonmover_set:
                found_conflict = True

        if found_full:
            any_full += 1
        elif found_conflict:
            no_full_but_conflict += 1
        else:
            no_conflict += 1

    print(f"  ANY binary full coverage: {any_full}/{total_valid}")
    print(f"  No full but still conflict: {no_full_but_conflict}/{total_valid}")
    print(f"  No conflict anywhere: {no_conflict}/{total_valid}")


if __name__ == "__main__":
    main()
