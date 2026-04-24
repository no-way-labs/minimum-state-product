#!/usr/bin/env python3
"""RA12 Part 3: Redirect strategy for Case 2.

Key finding: Case 2 has NO EC at q, but ALWAYS has EC elsewhere.
This means the proof strategy of "EC at q" is wrong for Case 2.

New investigation:
1. For Case 2: WHERE does EC occur? At the sandwiched ternary? At q's neighbors?
2. Is there a DIFFERENT all-binary-context processor that works?
   (Maybe the proof should pick a DIFFERENT q for Case 2 instances)
3. Can we guarantee: for every cycle, there EXISTS an all-binary-context q
   where Case 1 holds?
4. Alternative: Does every cycle have EC at the sandwiched ternary t?
5. Check whether the proof should be: "either EC at q OR EC at t"
"""

from collections import Counter

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
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

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def has_ec_at_proc(word, cycle, ms, n, p):
    ell = len(word)
    pL = (p - 1) % n
    pR = (p + 1) % n
    mover_ctx = set()
    nonmover_ctx = set()
    for s in range(ell):
        ctx = (cycle[s][pL], cycle[s][p], cycle[s][pR])
        if word[s] == p:
            mover_ctx.add(ctx)
        else:
            nonmover_ctx.add(ctx)
    return bool(mover_ctx & nonmover_ctx)

# ===== ANALYSIS =====
print("=" * 70)
print("RA12 REDIRECT: Where does EC live when q fails?")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2, 2, 2, 3, 2], 16, "n=5"),
    (7, [2, 2, 2, 3, 2, 3, 3], 24, "n=7a"),
    (7, [2, 2, 2, 3, 3, 2, 3], 24, "n=7b"),
]:
    print(f"\n{'='*70}")
    print(f"  {label}: ms={ms}")
    print(f"{'='*70}")

    words = enumerate_mover_words(ms, n, max_len)
    all_bin_ctx = [q for q in range(n)
                   if ms[q] == 2 and ms[(q-1)%n] == 2 and ms[(q+1)%n] == 2]
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    total_cycles = 0
    # Track: for each cycle, which all-binary-context q's are Case 1?
    cycle_has_case1_q = 0
    cycle_no_case1_q = 0
    cycle_no_case1_examples = []

    # Track EC at sandwiched ternary
    ec_at_sandwiched = 0
    ec_not_at_sandwiched = 0

    # Track: for Case 2, where is EC?
    case2_ec_at_sandwiched = 0
    case2_ec_at_neighbor_of_q = 0
    case2_ec_proc_types = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        ell = len(word)
        fc = Counter(word)

        # (1,1) phase check
        has_11 = False
        for t in sandwiched:
            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover = [s for s in phase_steps if word[s] == t]
                t_nonmover = [s for s in phase_steps if word[s] != t]
                if len(t_mover) == 1 and len(t_nonmover) >= 1:
                    has_11 = True
                    break
            if has_11:
                break
        if not has_11:
            continue

        total_cycles += 1

        # For each all-binary-context q with fc=2
        any_case1_q = False
        this_cycle_case2_qs = []

        for q in all_bin_ctx:
            if fc[q] != 2:
                continue

            qL = (q - 1) % n
            qR = (q + 1) % n
            q_steps = [s for s in range(ell) if word[s] == q]
            s1, s2 = q_steps

            a1, b1 = cycle[s1][qL], cycle[s1][qR]
            a2, b2 = cycle[s2][qL], cycle[s2][qR]

            if (a1, b1) == (a2, b2):
                any_case1_q = True
            else:
                this_cycle_case2_qs.append(q)

        if any_case1_q:
            cycle_has_case1_q += 1
        else:
            cycle_no_case1_q += 1
            if len(cycle_no_case1_examples) < 5:
                cycle_no_case1_examples.append(word)

        # EC at sandwiched ternary?
        ec_at_t = any(has_ec_at_proc(word, cycle, ms, n, t) for t in sandwiched)
        if ec_at_t:
            ec_at_sandwiched += 1
        else:
            ec_not_at_sandwiched += 1

        # For Case 2 instances: where is EC?
        for q in this_cycle_case2_qs:
            qL = (q - 1) % n
            qR = (q + 1) % n

            if ec_at_t:
                case2_ec_at_sandwiched += 1

            # EC at q's neighbors?
            ec_qL = has_ec_at_proc(word, cycle, ms, n, qL)
            ec_qR = has_ec_at_proc(word, cycle, ms, n, qR)
            if ec_qL or ec_qR:
                case2_ec_at_neighbor_of_q += 1

            # Classify EC proc type
            for p in range(n):
                if has_ec_at_proc(word, cycle, ms, n, p):
                    if p in sandwiched:
                        case2_ec_proc_types['sandwiched_ternary'] += 1
                    elif ms[p] == 2:
                        case2_ec_proc_types[f'binary_{p}'] += 1
                    else:
                        case2_ec_proc_types[f'ternary_{p}'] += 1

    print(f"Total cycles with (1,1) phase: {total_cycles}")
    print(f"\nCan we always find a Case-1 q?")
    print(f"  Cycles with at least one Case-1 q: {cycle_has_case1_q} ({100*cycle_has_case1_q/max(1,total_cycles):.1f}%)")
    print(f"  Cycles with NO Case-1 q: {cycle_no_case1_q}")

    print(f"\nEC at sandwiched ternary t:")
    print(f"  Has EC at t: {ec_at_sandwiched} ({100*ec_at_sandwiched/max(1,total_cycles):.1f}%)")
    print(f"  No EC at t: {ec_not_at_sandwiched}")

    total_case2 = case2_ec_at_sandwiched  # Just for denominator
    n_case2 = sum(1 for word in words
                  if build_cycle(ms, n, word) is not None and is_wrap_adjacent(word, n)
                  for q in all_bin_ctx
                  if Counter(word).get(q, 0) == 2)
    # simpler count
    print(f"\nFor Case 2 instances where q has no EC:")
    print(f"  EC at sandwiched ternary: {case2_ec_at_sandwiched}")
    print(f"  EC at q's neighbor: {case2_ec_at_neighbor_of_q}")
    print(f"  EC proc type distribution: {dict(case2_ec_proc_types)}")

    if cycle_no_case1_examples:
        print(f"\nExamples of cycles with NO Case-1 q:")
        for word in cycle_no_case1_examples[:3]:
            print(f"  word_len={len(word)}, fc={dict(Counter(word))}")

# ===== KEY QUESTION: is the right approach to check ALL binary procs, not just all-binary-context? =====
print("\n" + "=" * 70)
print("ALT: EC at ANY binary proc (not just all-binary-context)")
print("=" * 70)

for n, ms, max_len, label in [
    (7, [2, 2, 2, 3, 2, 3, 3], 24, "n=7a"),
]:
    words = enumerate_mover_words(ms, n, max_len)
    binary_procs = [p for p in range(n) if ms[p] == 2]

    total = 0
    ec_at_some_binary = 0
    ec_at_some_binary_fc2 = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        fc = Counter(word)

        # EC at any binary proc?
        found = any(has_ec_at_proc(word, cycle, ms, n, p) for p in binary_procs)
        if found:
            ec_at_some_binary += 1

        # EC at any binary proc with fc=2?
        found2 = any(has_ec_at_proc(word, cycle, ms, n, p)
                     for p in binary_procs if fc[p] == 2)
        if found2:
            ec_at_some_binary_fc2 += 1

    print(f"\n{label}: {total} cycles")
    print(f"  EC at some binary proc: {ec_at_some_binary} ({100*ec_at_some_binary/total:.1f}%)")
    print(f"  EC at some binary proc with fc=2: {ec_at_some_binary_fc2} ({100*ec_at_some_binary_fc2/total:.1f}%)")

# ===== MOST IMPORTANT: Case 1 at q-1 or q+1 (shifted) =====
print("\n" + "=" * 70)
print("SHIFTED ANALYSIS: For each cycle, check ALL fc=2 binary procs")
print("Check Case 1 vs Case 2 at EACH such proc")
print("=" * 70)

for n, ms, max_len, label in [
    (7, [2, 2, 2, 3, 2, 3, 3], 24, "n=7a"),
]:
    words = enumerate_mover_words(ms, n, max_len)
    binary_procs = [p for p in range(n) if ms[p] == 2]

    total = 0
    cycle_has_case1_some_binary = 0
    cycle_all_case2 = 0
    all_case2_examples = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        ell = len(word)
        fc = Counter(word)

        # (1,1) phase check
        sandwiched = [t for t in range(n)
                      if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]
        has_11 = False
        for t in sandwiched:
            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover = [s for s in phase_steps if word[s] == t]
                t_nonmover = [s for s in phase_steps if word[s] != t]
                if len(t_mover) == 1 and len(t_nonmover) >= 1:
                    has_11 = True
                    break
            if has_11:
                break
        if not has_11:
            continue

        total += 1

        found_case1 = False
        for q in binary_procs:
            if fc[q] != 2:
                continue
            qL = (q - 1) % n
            qR = (q + 1) % n
            q_steps = [s for s in range(ell) if word[s] == q]
            s1, s2 = q_steps

            a1, b1 = cycle[s1][qL], cycle[s1][qR]
            a2, b2 = cycle[s2][qL], cycle[s2][qR]

            if (a1, b1) == (a2, b2):
                found_case1 = True
                break

        if found_case1:
            cycle_has_case1_some_binary += 1
        else:
            cycle_all_case2 += 1
            if len(all_case2_examples) < 3:
                all_case2_examples.append(word)

    print(f"\n{label}: {total} cycles with (1,1) phase")
    print(f"  Has Case-1 at SOME binary fc=2 proc: {cycle_has_case1_some_binary}")
    print(f"  ALL binary fc=2 procs are Case 2: {cycle_all_case2}")

    if all_case2_examples:
        print(f"\n  Examples where ALL fc=2 binary procs are Case 2:")
        for word in all_case2_examples:
            fc = Counter(word)
            cycle = build_cycle(ms, n, word)
            ell = len(word)
            print(f"    word_len={ell}, fc={dict(fc)}")
            for q in binary_procs:
                if fc[q] != 2:
                    continue
                qL, qR = (q-1)%n, (q+1)%n
                q_steps = [s for s in range(ell) if word[s] == q]
                s1, s2 = q_steps
                a1, b1 = cycle[s1][qL], cycle[s1][qR]
                a2, b2 = cycle[s2][qL], cycle[s2][qR]
                print(f"      q={q}: (a1,b1)=({a1},{b1}), (a2,b2)=({a2},{b2})")
                # Check EC at q
                print(f"        EC at q: {has_ec_at_proc(word, cycle, ms, n, q)}")
            # Where IS ec?
            ep = [p for p in range(n) if has_ec_at_proc(word, cycle, ms, n, p)]
            print(f"      EC procs: {ep}")
