#!/usr/bin/env python3
"""Direct counting argument for Full Return universality.

Instead of displacement parity, count the (bL, bR) pairs seen by
mover and nonmover steps within each phase of each ternary proc.

For ternary t with binary neighbors bL, bR (both m=2):
  - (bL, bR) ∈ {0,1}^2 = 4 possible values
  - Phase k has 1 mover step (value v_k) and ≥1 nonmover steps
  - FR at phase k: v_k appears at some nonmover step

KEY IDEA: In a proper ring walk, the B-T alternation forces
the first nonmover of each phase to fire bL or bR.
After t fires at step s (mover of phase k):
  - Next step fires bL or bR (ring adjacency)
  - This changes exactly one of (c[bL], c[bR])
  - The first nonmover sees v_k ⊕ e_i for some unit vector e_i

So the first nonmover always DIFFERS from v_k in exactly one coordinate.
But later nonmovers might match.

Count: in each phase, how many nonmover (bL,bR) values are there?
If the phase has enough nonmover steps hitting all 4 values, FR is guaranteed.
"""
import sys, time
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

print("=" * 70)
print("DIRECT COUNTING: MOVER/NONMOVER (bL,bR) STRUCTURE PER PHASE")
print("=" * 70)

n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]

t0 = time.time()
words = enumerate_mover_words(ms, n, 24)

# PART 1: Post-mover step analysis
# After t fires (mover step), what fires next?
print("\nPART 1: POST-MOVER STEP ANALYSIS")

post_mover = Counter()  # what fires right after ternary mover step
pre_mover = Counter()   # what fires right before ternary mover step
first_nm_offset = Counter()  # (c[bL],c[bR]) at first NM relative to mover

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in tern:
        if fc[t] > ms[t]:
            continue  # skip multi-round
        bL = (t - 1) % n
        bR = (t + 1) % n

        for s in range(ell):
            if word[s] == t:
                v_m = (cycle[s][bL], cycle[s][bR])  # mover value

                # Post-mover step
                s_next = (s + 1) % ell
                post_mover[word[s_next]] += 1

                # First nonmover in same phase
                k = cycle[s][t]
                s_nm = (s + 1) % ell
                while word[s_nm] == t or cycle[s_nm][t] != k:
                    s_nm = (s_nm + 1) % ell
                    if s_nm == s:
                        break
                if s_nm != s and cycle[s_nm][t] == k:
                    v_nm = (cycle[s_nm][bL], cycle[s_nm][bR])
                    diff = ((v_nm[0] - v_m[0]) % 2, (v_nm[1] - v_m[1]) % 2)
                    first_nm_offset[diff] += 1

                # Pre-mover step
                s_prev = (s - 1) % ell
                pre_mover[word[s_prev]] += 1

print(f"  Post-mover step fires proc: {dict(sorted(post_mover.items()))}")
print(f"  Pre-mover step fires proc: {dict(sorted(pre_mover.items()))}")
print(f"\n  First nonmover (bL,bR) offset from mover value:")
for diff, cnt in sorted(first_nm_offset.items()):
    print(f"    Δ = {diff}: {cnt}")

# PART 2: For each phase, count nonmover (bL,bR) distinct values
print(f"\n{'='*60}")
print("PART 2: NONMOVER (bL,bR) COVERAGE PER PHASE")

nm_coverage = Counter()  # number of distinct (bL,bR) values at nonmover steps per phase
nm_has_mover = Counter()  # does nonmover set include the mover value?

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in tern:
        if fc[t] > ms[t]:
            continue
        bL = (t - 1) % n
        bR = (t + 1) % n

        for k in range(ms[t]):
            phase_steps = [s for s in range(ell) if cycle[s][t] == k]
            mover_steps = [s for s in phase_steps if word[s] == t]
            nm_steps = [s for s in phase_steps if word[s] != t]

            if not mover_steps or not nm_steps:
                continue

            v_mover = (cycle[mover_steps[0]][bL], cycle[mover_steps[0]][bR])
            nm_values = set((cycle[s][bL], cycle[s][bR]) for s in nm_steps)

            nm_coverage[len(nm_values)] += 1
            nm_has_mover[v_mover in nm_values] += 1

print(f"  Distinct (bL,bR) values at nonmover steps per phase:")
for cov, cnt in sorted(nm_coverage.items()):
    print(f"    {cov}/4 values: {cnt}")

print(f"\n  Mover value in nonmover set:")
for has, cnt in sorted(nm_has_mover.items()):
    print(f"    {has}: {cnt}")

# PART 3: When mover value NOT in nonmover set (FR fails at this phase),
# what's the relationship?
print(f"\n{'='*60}")
print("PART 3: ANATOMY OF FR-FAILING PHASES")

fail_anatomy = Counter()
nm_complement = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in tern:
        if fc[t] > ms[t]:
            continue
        bL = (t - 1) % n
        bR = (t + 1) % n

        for k in range(ms[t]):
            phase_steps = [s for s in range(ell) if cycle[s][t] == k]
            mover_steps = [s for s in phase_steps if word[s] == t]
            nm_steps = [s for s in phase_steps if word[s] != t]

            if not mover_steps or not nm_steps:
                continue

            v_mover = (cycle[mover_steps[0]][bL], cycle[mover_steps[0]][bR])
            nm_values = set((cycle[s][bL], cycle[s][bR]) for s in nm_steps)

            if v_mover not in nm_values:
                # FR fails at this phase
                # What values does NM cover?
                nm_complement[frozenset(nm_values)] += 1

                # What's the step-by-step trajectory?
                # Phase structure: mover at end, NM before
                nm_trajectory = [(cycle[s][bL], cycle[s][bR]) for s in nm_steps]
                fail_anatomy[(len(nm_steps), len(nm_values), v_mover)] += 1

print(f"  FR-failing phases by (num_nm_steps, nm_distinct, mover_value):")
for (ns, nd, vm), cnt in sorted(fail_anatomy.items(), key=lambda x: -x[1])[:20]:
    print(f"    nm_steps={ns}, nm_distinct={nd}, mover={vm}: {cnt}")

print(f"\n  NM value sets at failing phases:")
for nm_set, cnt in sorted(nm_complement.items(), key=lambda x: -x[1])[:10]:
    print(f"    {set(nm_set)}: {cnt}")

# PART 4: Phase duration (number of steps per phase)
print(f"\n{'='*60}")
print("PART 4: PHASE DURATION DISTRIBUTION")

phase_dur = Counter()
phase_dur_fail = Counter()  # duration when FR fails at this phase

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in tern:
        if fc[t] > ms[t]:
            continue
        bL = (t - 1) % n
        bR = (t + 1) % n

        fr_at_any = False
        for k in range(ms[t]):
            phase_steps = [s for s in range(ell) if cycle[s][t] == k]
            mover_steps = [s for s in phase_steps if word[s] == t]
            nm_steps = [s for s in phase_steps if word[s] != t]

            dur = len(phase_steps)
            phase_dur[dur] += 1

            if mover_steps and nm_steps:
                v_mover = (cycle[mover_steps[0]][bL], cycle[mover_steps[0]][bR])
                nm_values = set((cycle[s][bL], cycle[s][bR]) for s in nm_steps)
                if v_mover not in nm_values:
                    phase_dur_fail[dur] += 1

print(f"  Phase duration distribution:")
for d, cnt in sorted(phase_dur.items()):
    fail_cnt = phase_dur_fail.get(d, 0)
    fail_pct = 100 * fail_cnt / cnt if cnt > 0 else 0
    print(f"    duration={d}: {cnt} total, {fail_cnt} FR-fail ({fail_pct:.1f}%)")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
sys.stdout.flush()
