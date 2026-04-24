"""
Understand the EXACT mechanism that makes ternary procs win.

Hypothesis: For a ternary proc i adjacent to a binary proc b,
between consecutive fires of i, the binary neighbor b fires an even
number of times in some suffix interval [k2, a2).

The key: "stay" steps. When mover[k] = i and the next mover is also i,
that's a "stay". Between consecutive fires of i, there are no stays AT i.
But there can be steps where the mover is far from i, meaning NEITHER
neighbor fires.

Actually, let me think about this more carefully.

Between consecutive fires a1, a2 of proc i:
- i doesn't fire in (a1, a2)
- Each step in (a1, a2), the mover is some proc j != i
- By locality, the movers form a path on the ring starting from a neighbor of i

For the EC mechanism, we need k2 in (a1, a2) where:
- mover[k2] != i
- In [k2, a2): left(i) fires 0 or binary-even times, right(i) fires 0 or binary-even times

The simplest case: there exists k2 where NEITHER left(i) nor right(i) fires in [k2, a2).
This means all movers in [k2, a2) are "far" from i (not i, not L(i), not R(i)).
But by locality, mover[a2] = i and mover[a2-1] is adjacent to i. So mover[a2-1] in {L,R}.
So the interval [a2-1, a2) always has one of L,R firing. We need k2 < a2-1.

Let me look at what actually happens in the winning intervals.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def detailed_analysis(mover_word, moduli, n):
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1

    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None

    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None

    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None

    results = []

    for i in range(n):
        if fc[i] < 2: continue
        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap_len = a2_raw - a1 - 1
            if gap_len == 0: continue

            li = left(i, n)
            ri = right(i, n)

            # Compute cumulative fires of L,R from a2 backwards
            # For each position k in the gap, compute fires of L,R in [k, a2)
            best_k2 = None
            for k2_raw in range(a1 + 1, a2_raw):
                k2 = k2_raw % CL
                if mover_word[k2] == i: continue

                interval = [t % CL for t in range(k2_raw, a2_raw)]
                li_fires = sum(1 for k in interval if mover_word[k] == li)
                ri_fires = sum(1 for k in interval if mover_word[k] == ri)
                li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
                ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)

                if li_ok and ri_ok:
                    # Record the mover sequence in [k2, a2)
                    mover_seq = [mover_word[t % CL] for t in range(k2_raw, a2_raw)]
                    rel_seq = []
                    for m in mover_seq:
                        if m == li: rel_seq.append('L')
                        elif m == ri: rel_seq.append('R')
                        elif m == i: rel_seq.append('I')
                        else: rel_seq.append('O')

                    results.append({
                        'proc': i, 'is_binary': moduli[i] == 2,
                        'li_binary': moduli[li] == 2, 'ri_binary': moduli[ri] == 2,
                        'gap': gap_len, 'dist': a2_raw - k2_raw,
                        'li_fires': li_fires, 'ri_fires': ri_fires,
                        'seq': ''.join(rel_seq),
                        'fc_i': fc[i]
                    })
                    break

    return results if results else None

# Focus on spaced binary case where only ternary wins
n = 9
moduli = [2,3,3,2,3,3,2,3,3]  # binary at 0,3,6

print(f"n={n}, moduli={moduli}")
print("Binary procs: 0, 3, 6")
print("Each binary proc is at distance 3 from others")
print("Ternary procs adjacent to binary: 1,2 (adj to 0,3), 4,5 (adj to 3,6), 7,8 (adj to 6,0)")
print()

all_results = []
n_valid = 0

for trial in range(200000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 4*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))

    result = detailed_analysis(word, moduli, n)
    if result is None: continue
    n_valid += 1
    all_results.extend(result)

print(f"Valid cycles: {n_valid}, winning combos: {len(all_results)}")

print("\n--- Winning proc ---")
print(Counter(r['proc'] for r in all_results).most_common())

print("\n--- Winner is binary? ---")
print(Counter(r['is_binary'] for r in all_results))

print("\n--- L neighbor binary? ---")
print(Counter(r['li_binary'] for r in all_results))

print("\n--- R neighbor binary? ---")
print(Counter(r['ri_binary'] for r in all_results))

print("\n--- Has at least one binary neighbor? ---")
print(Counter(r['li_binary'] or r['ri_binary'] for r in all_results))

print("\n--- Mover sequence in winning interval (top 20) ---")
print(Counter(r['seq'] for r in all_results).most_common(20))

print("\n--- li_fires values ---")
print(Counter(r['li_fires'] for r in all_results).most_common(10))

print("\n--- ri_fires values ---")
print(Counter(r['ri_fires'] for r in all_results).most_common(10))

print("\n--- fc of winning proc ---")
print(Counter(r['fc_i'] for r in all_results).most_common(10))

# Key: does a ternary proc with binary neighbor ALWAYS exist and win?
print("\n--- Ternary proc with binary neighbor winning ---")
count_tern_bin_nbr = sum(1 for r in all_results if not r['is_binary'] and (r['li_binary'] or r['ri_binary']))
print(f"{count_tern_bin_nbr}/{len(all_results)}")
