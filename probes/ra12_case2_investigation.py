#!/usr/bin/env python3
"""RA12: Case 2 investigation for all-binary-context EC proof.

Setup: ring with all state sizes in {2,3}, ≥3 consecutive binary, sub-threshold product.
A sandwiched ternary t has a normalForm (1,1) phase.
Processor q has all-binary context: m_{q-1}=m_q=m_{q+1}=2, fc(q)=2.

q fires at steps s1 and s2 (cyclically ordered).
At s1: context (a1, v, b1)   [v = c[q] before firing]
At s2: context (a2, 1-v, b2) [value = 1-v since binary, fc=2]

Case 1: (a1,b1) = (a2,b2) — PROVED
Case 2: (a1,b1) != (a2,b2) — NEEDS INVESTIGATION

Questions:
1. Does Case 2 actually occur?
2. If so: properties of the differing coordinates
3. Target pair overlap in intervals
4. Gap analysis (non-neighbor steps after both neighbors settle)
"""

import sys
from collections import Counter
from itertools import product as iprod

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

def cyclic_interval(start, end, ell):
    """Steps from start+1 to end-1 (exclusive both endpoints), mod ell."""
    steps = []
    s = (start + 1) % ell
    while s != end:
        steps.append(s)
        s = (s + 1) % ell
    return steps

def analyze_n(n, ms, max_len, label):
    """Full analysis for given n and state vector."""
    print(f"\n{'='*70}")
    print(f"  {label}: n={n}, ms={ms}, max_len={max_len}")
    print(f"{'='*70}")

    words = enumerate_mover_words(ms, n, max_len)

    # Find all-binary-context processors: m_{q-1}=m_q=m_{q+1}=2
    all_bin_ctx = [q for q in range(n)
                   if ms[q] == 2 and ms[(q-1)%n] == 2 and ms[(q+1)%n] == 2]

    # Find sandwiched ternary processors
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    print(f"All-binary-context procs: {all_bin_ctx}")
    print(f"Sandwiched ternary procs: {sandwiched}")

    total_cycles = 0
    cycles_with_11_phase = 0

    # Counters for questions
    case1_count = 0
    case2_count = 0
    case2_one_diff = 0
    case2_both_diff = 0
    case2_depart_toward_diff = 0
    case2_depart_away = 0
    case2_interval_len_min = float('inf')

    # Target pair overlap analysis
    target_appears_I1 = 0  # target (a2,b2) appears at non-mover step in I1
    target_appears_I2 = 0  # target (a1,b1) appears at non-mover step in I2
    target_appears_either = 0  # at least one interval has target overlap
    target_appears_neither = 0

    # Gap analysis
    min_gap_overall = float('inf')
    gap_distribution = Counter()

    # Actual EC check
    ec_at_q_count = 0
    no_ec_at_q = 0

    # Instance tracking for Case 2
    case2_examples = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total_cycles += 1

        ell = len(word)
        fc = Counter(word)

        # Check for (1,1) phase at sandwiched ternary
        has_11_phase = False
        for t in sandwiched:
            for phase_val in range(3):
                # Steps where t has value phase_val
                phase_steps = [s for s in range(ell) if cycle[s][t] == phase_val]
                # Count how many of these are t-mover steps
                t_mover_in_phase = [s for s in phase_steps if word[s] == t]
                t_nonmover_in_phase = [s for s in phase_steps if word[s] != t]

                if len(t_mover_in_phase) == 1 and len(t_nonmover_in_phase) >= 1:
                    has_11_phase = True
                    break
            if has_11_phase:
                break

        if not has_11_phase:
            continue
        cycles_with_11_phase += 1

        # For each all-binary-context processor q with fc(q)=2
        for q in all_bin_ctx:
            if fc[q] != 2:
                continue

            qL = (q - 1) % n
            qR = (q + 1) % n

            # Find q's two firing steps
            q_steps = [s for s in range(ell) if word[s] == q]
            if len(q_steps) != 2:
                continue

            s1, s2 = q_steps[0], q_steps[1]

            # Contexts at s1 and s2
            a1, v1, b1 = cycle[s1][qL], cycle[s1][q], cycle[s1][qR]
            a2, v2, b2 = cycle[s2][qL], cycle[s2][q], cycle[s2][qR]

            # Verify binary alternation: v2 = 1 - v1
            assert v2 == 1 - v1, f"Binary alternation failed: v1={v1}, v2={v2}"

            # Check actual EC at q
            mover_contexts = set()
            nonmover_contexts = set()
            for s in range(ell):
                ctx = (cycle[s][qL], cycle[s][q], cycle[s][qR])
                if word[s] == q:
                    mover_contexts.add(ctx)
                else:
                    nonmover_contexts.add(ctx)

            has_ec_at_q = bool(mover_contexts & nonmover_contexts)
            if has_ec_at_q:
                ec_at_q_count += 1
            else:
                no_ec_at_q += 1

            # Case classification
            if (a1, b1) == (a2, b2):
                case1_count += 1
            else:
                case2_count += 1

                # How many coordinates differ?
                a_diff = (a1 != a2)
                b_diff = (b1 != b2)
                if a_diff and b_diff:
                    case2_both_diff += 1
                else:
                    case2_one_diff += 1

                # Which side departs? Step s2+1 is the step right after q fires at s2.
                s2_next = (s2 + 1) % ell
                s1_next = (s1 + 1) % ell

                # After s2: which direction does walk go?
                depart_s2 = word[s2_next]
                diff_side = None
                if a_diff and not b_diff:
                    diff_side = qL
                elif b_diff and not a_diff:
                    diff_side = qR

                if diff_side is not None:
                    if depart_s2 == diff_side:
                        case2_depart_toward_diff += 1
                    else:
                        case2_depart_away += 1

                # Interval lengths
                I2_steps = cyclic_interval(s2, s1, ell)  # from s2 to s1
                I1_steps = cyclic_interval(s1, s2, ell)  # from s1 to s2
                case2_interval_len_min = min(case2_interval_len_min,
                                              len(I1_steps), len(I2_steps))

                if len(case2_examples) < 5:
                    case2_examples.append({
                        'word': word, 'q': q, 's1': s1, 's2': s2,
                        'ctx1': (a1, v1, b1), 'ctx2': (a2, v2, b2),
                        'I1_len': len(I1_steps), 'I2_len': len(I2_steps),
                        'depart_s2': depart_s2, 'diff_side': diff_side,
                    })

            # ===== TARGET PAIR OVERLAP ANALYSIS =====
            # I2: interval from s2 to s1 (where q has value v1 after firing at s2)
            # Target in I2: (a1, b1) — the LR values at q's next firing
            # I1: interval from s1 to s2 (where q has value v2 after firing at s1)
            # Target in I1: (a2, b2) — the LR values at q's next firing

            I2_steps = cyclic_interval(s2, s1, ell)
            I1_steps = cyclic_interval(s1, s2, ell)

            # Check I2: does (a1, b1) appear at a non-mover-of-q step?
            found_I2 = False
            for s in I2_steps:
                if word[s] != q:  # non-mover step for q
                    lr = (cycle[s][qL], cycle[s][qR])
                    if lr == (a1, b1):
                        found_I2 = True
                        break

            # Check I1: does (a2, b2) appear at a non-mover-of-q step?
            found_I1 = False
            for s in I1_steps:
                if word[s] != q:
                    lr = (cycle[s][qL], cycle[s][qR])
                    if lr == (a2, b2):
                        found_I1 = True
                        break

            if found_I2:
                target_appears_I2 += 1
            if found_I1:
                target_appears_I1 += 1
            if found_I1 or found_I2:
                target_appears_either += 1
            else:
                target_appears_neither += 1

            # ===== GAP ANALYSIS =====
            # For interval I2 (s2 -> s1):
            # After the LAST firing of qL or qR in I2, how many non-neighbor steps?
            # At that point, qL and qR have reached their "target" values a1, b1

            # Find last firing of qL in I2 and last firing of qR in I2
            last_qL_in_I2 = None
            last_qR_in_I2 = None
            for s in I2_steps:
                if word[s] == qL:
                    last_qL_in_I2 = s
                if word[s] == qR:
                    last_qR_in_I2 = s

            # The "settle" step is whichever fires last
            if last_qL_in_I2 is not None and last_qR_in_I2 is not None:
                # Which fires later? Use cyclic position relative to s2
                pos_L = (last_qL_in_I2 - s2) % ell
                pos_R = (last_qR_in_I2 - s2) % ell
                settle = last_qL_in_I2 if pos_L > pos_R else last_qR_in_I2
            elif last_qL_in_I2 is not None:
                settle = last_qL_in_I2
            elif last_qR_in_I2 is not None:
                settle = last_qR_in_I2
            else:
                settle = None  # Neither neighbor fires in I2!

            if settle is not None:
                # Count non-neighbor-of-q steps between settle and s1
                gap = 0
                s = (settle + 1) % ell
                while s != s1:
                    if word[s] not in (qL, qR, q):
                        gap += 1
                    s = (s + 1) % ell
                min_gap_overall = min(min_gap_overall, gap)
                gap_distribution[gap] += 1

            # Same for I1
            last_qL_in_I1 = None
            last_qR_in_I1 = None
            for s in I1_steps:
                if word[s] == qL:
                    last_qL_in_I1 = s
                if word[s] == qR:
                    last_qR_in_I1 = s

            if last_qL_in_I1 is not None and last_qR_in_I1 is not None:
                pos_L = (last_qL_in_I1 - s1) % ell
                pos_R = (last_qR_in_I1 - s1) % ell
                settle = last_qL_in_I1 if pos_L > pos_R else last_qR_in_I1
            elif last_qL_in_I1 is not None:
                settle = last_qL_in_I1
            elif last_qR_in_I1 is not None:
                settle = last_qR_in_I1
            else:
                settle = None

            if settle is not None:
                gap = 0
                s = (settle + 1) % ell
                while s != s2:
                    if word[s] not in (qL, qR, q):
                        gap += 1
                    s = (s + 1) % ell
                min_gap_overall = min(min_gap_overall, gap)
                gap_distribution[gap] += 1

    # ===== RESULTS =====
    print(f"\nTotal valid ring-walk cycles: {total_cycles}")
    print(f"Cycles with (1,1) phase at sandwiched ternary: {cycles_with_11_phase}")

    total_q_instances = case1_count + case2_count
    print(f"\nAll-binary-context q instances (fc=2): {total_q_instances}")
    print(f"  Case 1 (same LR pair): {case1_count} ({100*case1_count/max(1,total_q_instances):.1f}%)")
    print(f"  Case 2 (different LR pair): {case2_count} ({100*case2_count/max(1,total_q_instances):.1f}%)")

    if case2_count > 0:
        print(f"\n  Case 2 details:")
        print(f"    Exactly one coord differs: {case2_one_diff}")
        print(f"    Both coords differ: {case2_both_diff}")
        one_diff_total = case2_depart_toward_diff + case2_depart_away
        if one_diff_total > 0:
            print(f"    Depart toward differing side: {case2_depart_toward_diff}")
            print(f"    Depart away from differing side: {case2_depart_away}")
        print(f"    Min interval length: {case2_interval_len_min}")

    print(f"\n  Actual EC at q (brute force): {ec_at_q_count}/{total_q_instances}")
    print(f"  No EC at q: {no_ec_at_q}")

    print(f"\n  TARGET PAIR OVERLAP:")
    print(f"    Target appears in I2: {target_appears_I2}/{total_q_instances}")
    print(f"    Target appears in I1: {target_appears_I1}/{total_q_instances}")
    print(f"    Target appears in EITHER: {target_appears_either}/{total_q_instances} ({100*target_appears_either/max(1,total_q_instances):.1f}%)")
    print(f"    Target appears in NEITHER: {target_appears_neither}")

    print(f"\n  GAP ANALYSIS (non-neighbor steps after settle):")
    print(f"    Min gap: {min_gap_overall}")
    print(f"    Distribution: {dict(sorted(gap_distribution.items()))}")

    if case2_count > 0 and case2_examples:
        print(f"\n  Case 2 examples (first {len(case2_examples)}):")
        for ex in case2_examples[:3]:
            print(f"    word_len={len(ex['word'])}, q={ex['q']}, "
                  f"ctx1={ex['ctx1']}, ctx2={ex['ctx2']}, "
                  f"|I1|={ex['I1_len']}, |I2|={ex['I2_len']}, "
                  f"depart={ex['depart_s2']}, diff_side={ex['diff_side']}")

    return {
        'case1': case1_count, 'case2': case2_count,
        'target_either': target_appears_either,
        'target_neither': target_appears_neither,
        'no_ec': no_ec_at_q,
    }

# ===== RUN =====
print("=" * 70)
print("RA12: CASE 2 INVESTIGATION — ALL-BINARY-CONTEXT EC")
print("=" * 70)

# n=5: [2,2,2,3,2] — 3 consecutive binary (0,1,2), sandwiched ternary at 3
# All-binary-context: q=1 (m0=m1=m2=2)
results = {}
results['n5'] = analyze_n(5, [2,2,2,3,2], 16, "n=5: [2,2,2,3,2]")

# n=7: [2,2,2,3,2,3,3] — 3 consecutive binary (0,1,2)
results['n7a'] = analyze_n(7, [2,2,2,3,2,3,3], 24, "n=7: [2,2,2,3,2,3,3]")

# n=7: [2,2,2,3,3,3,2] — 3 consecutive binary (0,1,2)
results['n7b'] = analyze_n(7, [2,2,2,3,3,3,2], 24, "n=7: [2,2,2,3,3,3,2]")

# n=7: [2,2,2,2,3,3,3] — 4 consecutive binary (0,1,2,3)
results['n7c'] = analyze_n(7, [2,2,2,2,3,3,3], 24, "n=7: [2,2,2,2,3,3,3]")
