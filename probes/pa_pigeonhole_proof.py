#!/usr/bin/env python3
"""PA: Pigeonhole proof for EC at boundary ternary procs.

OBSERVATION from n=7 data: At boundary ternary t with both neighbors binary,
the context space is 2 * 3 * 2 = 12 contexts. The cycle has ell >= 2n steps.
Ternary t fires 3*M_t times (mover steps) and has ell - 3*M_t nonmover steps.

For M_t = 1 (minimum): 3 mover contexts, ell - 3 nonmover contexts.
If ell >= 14 (for n=7): nonmover has >=11 contexts from 12 possible.
Mover has 3 contexts from 12 possible.
Probability of overlap is high, but not certain (can dodge 1 of 12).

But the contexts aren't arbitrary. The SEQUENCE of contexts is constrained
by the ring walk structure. Let me check what the ACTUAL mechanism is.

KEY IDEA: At boundary ternary t between binary bL, bR:
- During a phase (interval between t-firings), bL and bR each toggle 0/1
- The context (L,S,R) at t changes as neighbors fire
- The mover context is the one RIGHT BEFORE t fires
- The nonmover contexts are all others

When the cycle passes through t's neighborhood repeatedly, the binary
neighbors create a LIMITED set of possible context patterns.

PROOF STRATEGY: Pigeonhole on the (bL_value, bR_value) pair.
Each pair (l,r) ∈ {0,1}² can appear with t-value s ∈ {0,1,2}.
So there are 12 possible (L,S,R) triples.

Mover uses 3 of them (one per phase: at S=0,1,2).
But the mover at S=k sees (bL_val, k, bR_val) just before firing.
The three mover contexts have S=0, S=1, S=2 (one each).

Nonmover: ALL other (L,S,R) that appear. The binary neighbors visit
all 4 (l,r) patterns at every ternary value level.

If at some level k, the (l,r) pattern before t's firing matches
a (l,r) pattern at a nonmover step with the same S=k, then EC.

QUESTION: Can all 3 mover (l,r) pairs be DISTINCT from all nonmover
(l,r) pairs at the same S level?

Let's enumerate and check.
"""
from collections import Counter, defaultdict
import itertools


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


# Check context structure at boundary ternary
print("=" * 70)
print("CONTEXT STRUCTURE AT BOUNDARY TERNARY")
print("=" * 70)

for n, ms_list, max_len, label in [
    (5, [2, 3, 2, 3, 2], 16, "n=5"),
    (7, [2, 3, 2, 3, 2, 3, 2], 22, "n=7"),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)
    print(f"\n{label}: {len(words)} words, boundary_t={boundary_t}")

    total = 0
    # For each boundary ternary, track the mover/nonmover context structure
    # per S-level
    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

    # Now focus on the first few cycles and trace the context per S-level
    cycle_count = 0
    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        cycle_count += 1
        if cycle_count > 5:
            break

        ell = len(word)
        fc = Counter(word)

        for t in boundary_t[:1]:  # Just first boundary ternary
            bL = (t - 1) % n
            bR = (t + 1) % n

            # Group by S-level
            mover_by_s = defaultdict(set)   # S -> set of (L, R)
            nonmover_by_s = defaultdict(set)

            for s in range(ell):
                L = cycle[s][bL]
                S = cycle[s][t]
                R = cycle[s][bR]
                lr = (L, R)
                if word[s] == t:
                    mover_by_s[S].add(lr)
                else:
                    nonmover_by_s[S].add(lr)

            print(f"\n  word={word[:20]}... ell={ell}")
            print(f"  proc {t}: fc={fc[t]}, M={fc[t]//3}")
            for s_val in range(3):
                m_lr = mover_by_s[s_val]
                n_lr = nonmover_by_s[s_val]
                overlap = m_lr & n_lr
                print(f"    S={s_val}: mover_LR={m_lr} nonmover_LR={n_lr} overlap={overlap}")

    # Now: the key question. At each S-level, mover sees exactly M (L,R) pairs.
    # Nonmover sees the rest. Out of 4 possible (L,R) pairs {(0,0),(0,1),(1,0),(1,1)}.
    # If M=1: mover uses 1 pair per level. Nonmover has >=3 pairs per level.
    # No overlap requires the 1 mover pair to be the 1 nonmover AVOIDS.
    # Across all 3 levels, need 3 simultaneous avoidances.
    # Each avoidance requires the nonmover to use exactly 3 of 4 pairs, and
    # the mover to hit the remaining one.

    # HOW MANY nonmover (L,R) pairs per S-level?
    print(f"\n  NONMOVER (L,R) COUNT PER S-LEVEL:")
    nonmover_lr_counts = Counter()
    mover_lr_counts = Counter()

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue

        ell = len(word)
        for t in boundary_t:
            bL = (t - 1) % n
            bR = (t + 1) % n
            for s_val in range(3):
                m_lrs = set()
                n_lrs = set()
                for s in range(ell):
                    if cycle[s][t] == s_val:
                        lr = (cycle[s][bL], cycle[s][bR])
                        if word[s] == t:
                            m_lrs.add(lr)
                        else:
                            n_lrs.add(lr)
                nonmover_lr_counts[len(n_lrs)] += 1
                mover_lr_counts[len(m_lrs)] += 1

    print(f"    nonmover |LR| dist: {dict(nonmover_lr_counts)}")
    print(f"    mover |LR| dist: {dict(mover_lr_counts)}")

    # If nonmover always has ALL 4 (L,R) pairs at every S-level:
    # Then no matter what the mover chooses, overlap is guaranteed!
    if nonmover_lr_counts.get(4, 0) == sum(nonmover_lr_counts.values()):
        print(f"    *** NONMOVER ALWAYS HAS ALL 4 (L,R) PAIRS → EC GUARANTEED ***")
    else:
        # Check: when nonmover has <4 pairs, does overlap still occur?
        missing_4 = sum(v for k, v in nonmover_lr_counts.items() if k < 4)
        print(f"    Nonmover has <4 LR pairs in {missing_4} cases")

# DEFINITIVE CHECK: at M=1, when nonmover has only 3 (L,R) pairs at
# some S-level, does the mover ALWAYS hit one of the 3?
print(f"\n{'='*70}")
print("DEFINITIVE: Can mover avoid ALL nonmover (L,R) pairs?")
print("=" * 70)

for n, ms_list, max_len, label in [
    (5, [2, 3, 2, 3, 2], 16, "n=5"),
    (7, [2, 3, 2, 3, 2, 3, 2], 22, "n=7"),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    total = 0
    any_proc_ec = 0  # At SOME boundary ternary
    all_4_count = 0
    avoidance_at_some_level = 0

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        ell = len(word)
        fc = Counter(word)

        has_ec = False
        for t in boundary_t:
            bL = (t - 1) % n
            bR = (t + 1) % n

            # Check per S-level
            ec_at_t = False
            for s_val in range(3):
                m_lrs = set()
                n_lrs = set()
                for s in range(ell):
                    if cycle[s][t] == s_val:
                        lr = (cycle[s][bL], cycle[s][bR])
                        if word[s] == t:
                            m_lrs.add(lr)
                        else:
                            n_lrs.add(lr)
                if m_lrs & n_lrs:
                    ec_at_t = True
                    break

            if ec_at_t:
                has_ec = True
                break

        if has_ec:
            any_proc_ec += 1

    print(f"\n{label}: {total} cycles")
    print(f"  EC at some boundary ternary (per-level check): {any_proc_ec}/{total}")
    print(f"  Rate: {100*any_proc_ec/total:.1f}%")
