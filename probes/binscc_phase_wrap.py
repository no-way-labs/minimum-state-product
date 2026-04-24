#!/usr/bin/env python3
"""Debug: phases can WRAP AROUND the cycle boundary.
steps = [s for s in range(ell) if cycle[s][t] == k] is sorted by index,
but temporally the phase might start at a high index and wrap to a low index.

This affects the neighbor ordering and gap detection.
Fix: reorder steps temporally within each phase.
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

def temporal_order(steps, ell):
    """Reorder phase steps into temporal (cyclic) order.
    Phase steps are contiguous in the cycle (mod ell).
    Find the largest gap to determine the start."""
    if len(steps) <= 1:
        return steps
    # Find largest gap
    max_gap = 0
    start_after = 0
    for i in range(len(steps)):
        nxt = (i + 1) % len(steps)
        gap = (steps[nxt] - steps[i]) % ell
        if gap > max_gap:
            max_gap = gap
            start_after = i
    # Reorder: start from the step AFTER the largest gap
    start_idx = (start_after + 1) % len(steps)
    return [steps[(start_idx + i) % len(steps)] for i in range(len(steps))]

# Test with n=5
n, ms = 5, [2, 3, 2, 3, 2]
words = enumerate_mover_words(ms, n, 16)
sandwiched = [1, 3]

# First: check how many phases wrap
wrap_count = 0
total_phases = 0
for word in words[:200]:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    for t in sandwiched:
        for k in range(3):
            steps = sorted(s for s in range(ell) if cycle[s][t] == k)
            temporal = temporal_order(steps, ell)
            total_phases += 1
            if temporal != steps:
                wrap_count += 1

print(f"Phases that wrap: {wrap_count}/{total_phases}")

# Now: redo the exact EC test with temporal ordering
print("\n" + "=" * 70)
print("CORRECTED: temporal ordering + gap detection")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2, 3, 2, 3, 2], "n=5", 16),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p - 1) % n] == 2 and ms[(p + 1) % n] == 2]

    exact_test = Counter()
    claim_test = Counter()
    debug_cases = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue
            bL, bR = (t - 1) % n, (t + 1) % n
            for k in range(3):
                raw_steps = sorted(s for s in range(ell) if cycle[s][t] == k)
                steps = temporal_order(raw_steps, ell)
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)

                if not ((J == 2 and K == 1) or (J == 1 and K == 2)):
                    continue

                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t:
                        m_lr.add(lr)
                    else:
                        nm_lr.add(lr)
                actual_ec = bool(m_lr & nm_lr)

                if J == 2:
                    pair, single = bL, bR
                else:
                    pair, single = bR, bL

                # Temporal ordering
                ne_types = ''
                for s in steps:
                    if word[s] == pair:
                        ne_types += 'P'
                    elif word[s] == single:
                        ne_types += 'S'

                if ne_types == 'PPS':
                    ordering = 'A'
                elif ne_types == 'PSP':
                    ordering = 'B'
                elif ne_types == 'SPP':
                    ordering = 'C'
                else:
                    ordering = ne_types

                # Gap: far-step between last neighbor and T (temporal)
                mover_tidx = next(i for i, s in enumerate(steps) if word[s] == t)
                ne_indices = [i for i, s in enumerate(steps)
                              if word[s] in (bL, bR)]
                last_ne_tidx = max(ne_indices)
                gap = (mover_tidx - last_ne_tidx > 1)

                exact_test[(ordering, gap, actual_ec)] += 1

                if ordering == 'C':
                    predicted_ec = True
                else:
                    predicted_ec = gap

                claim_test[(predicted_ec, actual_ec)] += 1

                if predicted_ec != actual_ec and len(debug_cases) < 3:
                    debug_cases.append({
                        't': t, 'k': k, 'J': J, 'K': K,
                        'ordering': ordering, 'gap': gap,
                        'actual_ec': actual_ec, 'predicted': predicted_ec,
                        'm_lr': m_lr, 'nm_lr': nm_lr,
                        'steps': steps,
                        'seq': [(s, word[s], (cycle[s][bL], cycle[s][bR]))
                                for s in steps],
                        'ne_types': ne_types,
                    })

    print(f"\n{label}:")
    print(f"  (ordering, gap, EC):")
    for (o, g, ec), cnt in sorted(exact_test.items()):
        print(f"    order={o} gap={str(g):5s} ec={str(ec):5s}: {cnt}")

    print(f"\n  Claim test:")
    for (pred, actual), cnt in sorted(claim_test.items()):
        match = "Y" if pred == actual else "N"
        print(f"    pred={str(pred):5s} actual={str(actual):5s}: {cnt} {match}")
    total = sum(claim_test.values())
    correct = claim_test.get((True, True), 0) + claim_test.get((False, False), 0)
    print(f"    Accuracy: {correct}/{total} ({100 * correct / total:.1f}%)")

    if debug_cases:
        print(f"\n  Debug mismatches:")
        for dc in debug_cases:
            print(f"    P{dc['t']} phase {dc['k']}: ({dc['J']},{dc['K']})"
                  f" order={dc['ordering']} gap={dc['gap']}"
                  f" pred={dc['predicted']} actual={dc['actual_ec']}")
            print(f"      m_lr={dc['m_lr']} nm_lr={dc['nm_lr']}")
            print(f"      ne_types={dc['ne_types']}")
            for s, who, lr in dc['seq']:
                role = 'T' if who == dc['t'] else (
                    'bL' if who == (dc['t'] - 1) % n else (
                    'bR' if who == (dc['t'] + 1) % n else 'far'))
                print(f"        s={s:2d} P{who}({role:3s}) (L,R)={lr}")
