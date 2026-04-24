#!/usr/bin/env python3
"""PA Phase Analysis: For arbitrary good cycles with >=3 non-consecutive binary,
extract the (J,K) phase data at every boundary ternary.

Key question: Can ALL phases at ALL boundary ternary procs simultaneously be
in normalForm {(1,0),(0,1),(1,1),(2,1),(1,2)}?

If not: some phase is dispatchable -> EC.

The COUNTING ARGUMENT:
- Binary proc b has fc[b] = k_b * 2 (must be even, since m_b=2)
- The total firings of b are distributed across phases at b's ternary neighbors
- Each boundary ternary t adjacent to b sees b fire J_phase times across its phases
- Sum of J across all phases of t = total b-firings seen by t

With >=3 non-consecutive binary, the constraints interact.
"""
import itertools
from collections import Counter, defaultdict
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
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


def extract_phases_detailed(word, cycle, ms, n, t):
    """Extract detailed phase info for ternary proc t.

    A 'phase' = interval between consecutive t-firings.
    t fires fc[t] times total, so there are fc[t] phases.
    In each phase, count J (left-neighbor firings) and K (right-neighbor firings).

    We also track M = number of t-firings per ternary-value-phase (fc[t]//3).
    """
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n

    # Find all t-firing steps in order
    t_steps = [s for s in range(ell) if word[s] == t]
    fc_t = len(t_steps)
    if fc_t == 0:
        return []

    phases = []
    for i in range(fc_t):
        # Phase i: from step after t_steps[i] to step at t_steps[(i+1)%fc_t]
        start = (t_steps[i] + 1) % ell
        end = t_steps[(i + 1) % fc_t]

        J, K = 0, 0
        s = start
        while s != end:
            if word[s] == bL:
                J += 1
            elif word[s] == bR:
                K += 1
            s = (s + 1) % ell

        phases.append((J, K))

    return phases


def is_dispatchable(J, K, M_per_phase):
    """Check if (J,K) is dispatchable (not normalForm)."""
    # Both-Even: J even, K even, M=1
    if M_per_phase == 1 and J % 2 == 0 and K % 2 == 0:
        return True, "both-even"
    # Toggle-FR: one side >=3, other 0
    if (J >= 3 and K == 0) or (J == 0 and K >= 3):
        return True, "toggle-FR"
    # Zero-Side: M=1, one side >=2, other 0
    if M_per_phase == 1 and ((J >= 2 and K == 0) or (J == 0 and K >= 2)):
        return True, "zero-side"
    return False, None


def is_normalForm(J, K):
    """Is (J,K) in the normalForm residual set?"""
    return (J, K) in [(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)]


print("=" * 70)
print("PHASE ANALYSIS: normalForm residual at boundary ternary procs")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    threshold = 4 * (3 ** (n - 2))
    prod = 1
    for m in ms_list:
        prod *= m

    binary_pos = [p for p in range(n) if ms_list[p] == 2]
    boundary_t = []
    for t in range(n):
        if ms_list[t] > 2:
            bL = (t - 1) % n
            bR = (t + 1) % n
            if ms_list[bL] == 2 or ms_list[bR] == 2:
                boundary_t.append(t)

    print(f"\nn={n}, ms={ms_list}, prod={prod}, threshold={threshold}")
    print(f"  binary={binary_pos}, boundary_ternary={boundary_t}")

    words = enumerate_mover_words(ms_list, n, max_len)
    print(f"  {len(words)} mover words enumerated")

    total = 0
    all_normalForm_count = 0
    phase_dispatch_count = 0
    phase_data_examples = []

    # Track (J,K) distributions
    jk_all = Counter()
    jk_nondispatch = Counter()

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        fc = Counter(word)
        has_dispatch = False
        all_nf = True

        for t in boundary_t:
            phases = extract_phases_detailed(word, cycle, ms_list, n, t)
            fc_t = fc[t]
            M_per_phase = fc_t // ms_list[t]

            for J, K in phases:
                jk_all[(J, K)] += 1
                disp, mech = is_dispatchable(J, K, M_per_phase)
                if disp:
                    has_dispatch = True
                if not is_normalForm(J, K):
                    all_nf = False
                    jk_nondispatch[(J, K)] += 1

        if has_dispatch:
            phase_dispatch_count += 1
        if all_nf:
            all_normalForm_count += 1
            if len(phase_data_examples) < 5:
                # Save example
                example = {}
                for t in boundary_t:
                    phases = extract_phases_detailed(word, cycle, ms_list, n, t)
                    example[t] = phases
                phase_data_examples.append((word, fc, example))

    print(f"\n  Total cycles: {total}")
    print(f"  Phase-dispatchable: {phase_dispatch_count}/{total} ({100*phase_dispatch_count/total:.1f}%)")
    print(f"  ALL phases normalForm: {all_normalForm_count}/{total} ({100*all_normalForm_count/total:.1f}%)")

    print(f"\n  (J,K) distribution across all phases:")
    for jk, cnt in sorted(jk_all.items(), key=lambda x: -x[1]):
        nf = "NF" if is_normalForm(*jk) else "DISP"
        print(f"    {jk}: {cnt} [{nf}]")

    if all_normalForm_count > 0:
        print(f"\n  EXAMPLES of all-normalForm cycles ({min(len(phase_data_examples), 3)}):")
        for word, fc, example in phase_data_examples[:3]:
            print(f"    word={word}")
            print(f"    fc={dict(fc)}")
            for t, phases in example.items():
                print(f"    proc {t}: phases={phases}")

    # Now check: for all-normalForm cycles, do they still have EC
    # via brute-force context check?
    print(f"\n  Checking all-normalForm cycles for brute-force EC...")
    nf_with_ec = 0
    nf_without_ec = 0
    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue

        fc = Counter(word)
        # Check if all phases are normalForm
        all_nf = True
        for t in boundary_t:
            phases = extract_phases_detailed(word, cycle, ms_list, n, t)
            for J, K in phases:
                if not is_normalForm(J, K):
                    all_nf = False
                    break
            if not all_nf:
                break

        if not all_nf:
            continue

        # Brute force EC check at boundary ternary
        has_ec = False
        ell = len(word)
        for t in boundary_t:
            bL = (t - 1) % n
            bR = (t + 1) % n
            mover_ctx = set()
            nonmover_ctx = set()
            for s in range(ell):
                ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if word[s] == t:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if mover_ctx & nonmover_ctx:
                has_ec = True
                break

        if has_ec:
            nf_with_ec += 1
        else:
            nf_without_ec += 1
            # Print details
            print(f"\n    *** NO EC in normalForm cycle ***")
            print(f"    word={word}")
            print(f"    fc={dict(fc)}")
            for t in boundary_t:
                phases = extract_phases_detailed(word, cycle, ms_list, n, t)
                print(f"    proc {t}: phases={phases}")
                bL = (t - 1) % n
                bR = (t + 1) % n
                mover_ctx = set()
                nonmover_ctx = set()
                for s in range(ell):
                    ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                    if word[s] == t:
                        mover_ctx.add(ctx)
                    else:
                        nonmover_ctx.add(ctx)
                print(f"      mover_ctx={mover_ctx}")
                print(f"      nonmover_ctx={nonmover_ctx}")

    print(f"\n  All-normalForm with EC: {nf_with_ec}")
    print(f"  All-normalForm without EC: {nf_without_ec}")
    if nf_without_ec == 0 and all_normalForm_count > 0:
        print(f"  *** Even normalForm cycles have EC (via other mechanism) ***")
