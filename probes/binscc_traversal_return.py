#!/usr/bin/env python3
"""Traversal Return EC: prove (2,1)/(1,2) anti-diagonal phases ALWAYS have EC when M=1.

SETUP: Phase with J=2, K=1, M=1 at ternary T (fc[T]=3).
- L starts at L₀, toggles twice → returns to L₀
- R starts at R₀, toggles once → ends at R̄₀
- Mover (last step) sees (L₀, R̄₀)
- First nonmover sees (L₀, R₀) ≠ mover

QUESTION: Does some nonmover step also see (L₀, R̄₀)?

This depends on the ORDERING of bL and bR firings within the phase.
Key: After bR fires, R = R̄₀. If at that point L = L₀ (either before 1st bL or after 2nd bL),
then a nonmover step sees (L₀, R̄₀) = mover → EC.

Three orderings of {bL₁, bL₂, bR}:
  A) bR, bL, bL: after bR, L=L₀ → nonmover at (L₀,R̄₀) → EC
  B) bL, bR, bL: after bR, L=L̄₀. After 2nd bL, L=L₀, R=R̄₀ → (L₀,R̄₀).
     But is there a nonmover step at (L₀,R̄₀)?
  C) bL, bL, bR: after 2nd bL, L=L₀, R=R₀. After bR: (L₀,R̄₀).
     Next step is T (mover) or far-step. If far-step → nonmover at (L₀,R̄₀) → EC.
     If directly T → no nonmover at (L₀,R̄₀).

So the critical case is: does the walk always have a step between the last neighbor firing and T?

On the alternating ring, T is ternary with binary neighbors bL, bR.
After bR fires (bR is binary), the walk moves to an adjacent position.
bR's neighbors: T and some other ternary T'.
If walk goes T → T fires → but T firing ends the phase, so if bR was the LAST neighbor...

Wait, the walk is on the ring. At step s, processor word[s] fires. The walk moves from
word[s-1] to word[s], which must be adjacent on the ring.

After bR fires at step s, the walk at step s+1 must be adjacent to bR on the ring.
bR's ring neighbors are T and some processor q ≠ T.
If step s+1 = T → that's the mover (T fires). Nonmover at bR-step saw (L_before_bR, R₀).
   After bR: (L_before_bR, R̄₀). Then T sees (L_before_bR, R̄₀).
   If L_before_bR = L₀: mover = (L₀, R̄₀). But the nonmover at bR-step saw (L₀, R₀) ≠ mover.
   Need another nonmover at (L₀, R̄₀). Only get this if far-step after bR and before T.
   But walk went bR → T directly. So NO nonmover at (L₀, R̄₀).

So if the last neighbor to fire is bR, and the walk goes directly bR → T, we might NOT get EC
from the (L₀,R̄₀) match. But the FIRST nonmover is at (L₀,R₀), and the walk visits other
intermediate states too.

Let me check computationally: for the 768 uncovered n=8 cycles and the 56 uncovered n=5 cycles,
what EXACTLY is the EC mechanism? Do ALL (2,1)/(1,2) phases have EC?
"""
import time
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

# Check: for uncovered cycles, does EVERY (2,1)/(1,2) phase have EC?
for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    # Find uncovered cycles (not covered by 3 proved mechanisms)
    phase_21_ec = Counter()  # does (2,1)/(1,2) phase have EC?
    phase_11_ec = Counter()
    cycle_21_coverage = Counter()  # per uncovered cycle, does (2,1)/(1,2) give EC at ALL ternary?

    uncovered_examples = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        # Check if covered by 3 proved mechanisms
        cycle_covered = False
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            m = fc[t]
            M_per_phase = m // 3
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if M_per_phase == 1 and J % 2 == 0 and K % 2 == 0:
                    cycle_covered = True; break
                if (J >= 3 and K == 0) or (J == 0 and K >= 3):
                    cycle_covered = True; break
                if M_per_phase == 1:
                    if (J >= 2 and K == 0) or (J == 0 and K >= 2):
                        cycle_covered = True; break
            if cycle_covered:
                break

        if cycle_covered:
            continue

        # Uncovered cycle — analyze (2,1)/(1,2) and (1,1) phases
        has_21_ec = False
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                M = sum(1 for s in steps if word[s] == t)

                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t:
                        m_lr.add(lr)
                    else:
                        nm_lr.add(lr)
                has_ec = bool(m_lr & nm_lr)

                if (J, K) in [(2, 1), (1, 2)]:
                    phase_21_ec[has_ec] += 1
                    if has_ec:
                        has_21_ec = True
                        # What's the ordering?
                        if len(uncovered_examples) < 5:
                            seq = []
                            for s in steps:
                                if word[s] == bL: role = 'bL'
                                elif word[s] == bR: role = 'bR'
                                elif word[s] == t: role = 'T'
                                else: role = 'far'
                                seq.append((s, role, (cycle[s][bL], cycle[s][bR])))
                            uncovered_examples.append({
                                't': t, 'k': k, 'J': J, 'K': K, 'M': M,
                                'd': len(steps), 'seq': seq,
                                'm_lr': m_lr, 'nm_lr': nm_lr,
                            })
                elif (J, K) == (1, 1):
                    phase_11_ec[has_ec] += 1

        cycle_21_coverage[has_21_ec] += 1

    elapsed = time.time() - t0
    print(f"\n{label} ({elapsed:.1f}s):")
    print(f"  (2,1)/(1,2) phase EC: True={phase_21_ec[True]}, False={phase_21_ec[False]}")
    print(f"  (1,1) phase EC: True={phase_11_ec[True]}, False={phase_11_ec[False]}")
    print(f"  Uncovered cycles with (2,1)/(1,2) EC: {cycle_21_coverage}")

    if uncovered_examples:
        print(f"\n  Example (2,1)/(1,2) phase sequences:")
        for ex in uncovered_examples[:3]:
            print(f"    P{ex['t']} phase {ex['k']}: (J,K)=({ex['J']},{ex['K']}) M={ex['M']} d={ex['d']}")
            print(f"      m_lr={ex['m_lr']} nm_lr={ex['nm_lr']}")
            for s, role, lr in ex['seq']:
                print(f"        s={s:2d} {role:3s} (L,R)={lr}")

# PART 2: What is the precise nonmover trajectory in (2,1) phases?
# Focus on the ORDERING of bL and bR relative to far-away firings
print(f"\n{'='*70}")
print("ORDERING ANALYSIS: position of bR relative to bL firings in (2,1) phases")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    ordering_counts = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if not ((J == 2 and K == 1) or (J == 1 and K == 2)):
                    continue

                # Extract the bL/bR ordering (ignore far)
                # Also: what's right before T?
                mover_idx = [s for s in steps if word[s] == t]
                neighbor_seq = []
                for s in steps:
                    if word[s] == bL: neighbor_seq.append('L')
                    elif word[s] == bR: neighbor_seq.append('R')
                    elif word[s] == t: neighbor_seq.append('T')
                    else: neighbor_seq.append('f')

                # What fires immediately before T in the phase?
                t_pos = next(i for i, x in enumerate(neighbor_seq) if x == 'T')
                before_t = neighbor_seq[t_pos - 1] if t_pos > 0 else 'start'

                # Ordering of L and R (ignoring f)
                lr_order = ''.join(x for x in neighbor_seq if x in ('L', 'R'))

                ordering_counts[(label, J, K, lr_order, before_t)] += 1

    print(f"\n  {label}:")
    for (lab, J, K, order, before), cnt in sorted(ordering_counts.items()):
        if lab == label:
            print(f"    ({J},{K}) order={order} before_T={before}: {cnt}")
