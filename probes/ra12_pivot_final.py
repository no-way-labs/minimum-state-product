#!/usr/bin/env python3
"""
RA12 Final: Comprehensive analysis of pivot conditions.

The gap case: fc_ter=3, fc_bin=4 (binary fires MORE than ternary phases).

Key insight: maybe we don't need pigeonhole at the ternary.
Instead, use the GRADIENT directly.

The gradient gives us adjacent procs t, u with fc(t) > fc(u).
If t is ternary and u is binary: fc_t >= 6 > fc_u = 2 -> zero-sided at t. (Not gap.)
If t is binary and u is ternary: fc_t >= 4 > fc_u = 3 -> ternary fires 3 across 2 binary phases.
  Each binary phase has >= 1 ternary fire (3 across 2). Not zero-sided.
If t and u are both ternary: fc_t >= 6 > fc_u = 3 -> t has ternary nbr, not useful for binary side.

Wait. Let me reconsider the problem from scratch.

The original need: for entry conflict, we need a proc where the mover
context repeats as a non-mover context. The phase_dispatch_ec shows this
happens at a ternary proc with a "zero-sided" phase.

But maybe there's a completely different route for the gap case.

Let me check the GAP cases: do they actually have entry conflicts
through some other mechanism?
"""
import sys, os, time
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

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


def build_cycle_configs(ms, n, word):
    """Build the sequence of configurations along a mover word."""
    config = tuple(0 for _ in range(n))
    configs = [config]
    for p in word:
        nc = list(config)
        nc[p] = (nc[p] + 1) % ms[p]
        config = tuple(nc)
        configs.append(config)
    return configs


def check_entry_conflict(ms, n, word):
    """Check if the word has an entry conflict at ANY proc."""
    configs = build_cycle_configs(ms, n, word)
    cl = len(word)

    for t in range(n):
        # Collect mover contexts and non-mover contexts at t
        mover_ctxs = set()
        nonmover_ctxs = set()

        for step in range(cl):
            p = word[step]
            L = configs[step][(t - 1) % n]
            S = configs[step][t]
            R = configs[step][(t + 1) % n]
            ctx = (L, S, R)

            if p == t:
                mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)

        overlap = mover_ctxs & nonmover_ctxs
        if overlap:
            return True, t, overlap

    return False, None, None


print("=" * 70)
print("RA12 FINAL: GAP CASE ENTRY CONFLICT CHECK")
print("=" * 70)

# Gap cases from previous analysis
cases = [
    ([3, 3, 3, 2, 2, 2, 3], 7),
    ([2, 2, 2, 2, 3, 3, 3], 7),
    ([2, 2, 2, 2, 2, 3, 3], 7),
]

for ms, n in cases:
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    max_cl = sum(ms) + 4
    words = enumerate_mover_words(ms, n, max_cl)

    print(f"\nms={ms}")

    n_gap = 0
    n_gap_ec = 0
    n_gap_no_ec = 0
    ec_at_proc = Counter()

    for word in words:
        fc = Counter(word)
        if not any(fc[p] >= 3 for p in range(n)):
            continue

        # Check if this is a gap case
        satisfies_A = any(
            (fc[t] >= 3 and ms[(t-1)%n] == 2 and fc[(t-1)%n] < fc[t])
            or (fc[t] >= 3 and ms[(t+1)%n] == 2 and fc[(t+1)%n] < fc[t])
            for t in ternary_pos
        )
        if satisfies_A:
            continue

        n_gap += 1

        # Check entry conflict
        has_ec, ec_proc, overlap = check_entry_conflict(ms, n, word)
        if has_ec:
            n_gap_ec += 1
            ec_at_proc[ec_proc] += 1
        else:
            n_gap_no_ec += 1

    print(f"  Gap words: {n_gap}")
    print(f"  Gap with entry conflict: {n_gap_ec}")
    print(f"  Gap WITHOUT entry conflict: {n_gap_no_ec}")
    if ec_at_proc:
        print(f"  EC found at proc: {dict(sorted(ec_at_proc.items()))}")

print("\n" + "=" * 70)
print("ALTERNATIVE: CHECK GRADIENT-BASED CONDITION")
print("=" * 70)

print("""
The gradient condition: adjacent t, u with fc(t) > fc(u).
This exists in EVERY cycle with non-constant fc.

In the gap case: fc = {ter1:3, ter2:3, ..., bin_adj:4, bin_far:2, ...}
The binary procs have fc in {2, 4}. There's always a binary with fc=2.
And there's always a binary with fc=4 (otherwise no gap).

Gradient exists between bin(fc=4) and bin(fc=2) if they're adjacent.
Or between bin(fc=4) and ter(fc=3) if they're adjacent.

In the gap, ALL ternary-binary pairs have fc_bin >= fc_ter.
But binary-binary pairs might have gradient!

Key: bin b with fc=4, neighbor bin b' with fc=2.
Then b has higher fc than b'. b is binary.
Can we extract phase info from binary?

Binary with fc=4 has 2 "binary phases" (each = one full 0->1->0 cycle).
Its neighbor b' fires 2 times across these 2 phases.
Pigeonhole: 2 fires across 2 phases -> each phase has >=1 fire (if evenly distributed).
Could have (2,0) though! Need to check.
""")

# Check: in gap cases, what's the actual binary-binary gradient structure?
for ms, n in cases[:1]:
    max_cl = sum(ms) + 4
    words = enumerate_mover_words(ms, n, max_cl)
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    for word in words:
        fc = Counter(word)
        if not any(fc[p] >= 3 for p in range(n)):
            continue
        satisfies_A = any(
            (fc[t] >= 3 and ms[(t-1)%n] == 2 and fc[(t-1)%n] < fc[t])
            or (fc[t] >= 3 and ms[(t+1)%n] == 2 and fc[(t+1)%n] < fc[t])
            for t in ternary_pos
        )
        if satisfies_A:
            continue

        # Gap case. Print full fc and neighbors.
        fc_dict = {p: fc[p] for p in range(n)}
        print(f"\n  Gap word fc={fc_dict}, ms={ms}")
        for p in range(n):
            L = (p-1) % n
            R = (p+1) % n
            print(f"    p={p} ms={ms[p]} fc={fc[p]}, "
                  f"L: p{L} ms={ms[L]} fc={fc[L]}, "
                  f"R: p{R} ms={ms[R]} fc={fc[R]}")
        break  # just one example

print("\n" + "=" * 70)
print("KEY STRUCTURAL INSIGHT")
print("=" * 70)

print("""
In the gap cases:
  ms = [..., 3,3,3, 2,2,2, 3] or [..., 2,2,2,2, 3,3,3] or [..., 2,2,2,2,2, 3,3]
  All boundary ternary have fc=3, all their binary neighbors have fc=4.

But there are also binary procs with fc=2 (interior to the binary block).
These are NOT adjacent to any ternary.

The cycle length = 3*n_ter + 4*n_bin4 + 2*n_bin2 where n_bin4 + n_bin2 = n_bin.
Gap case has some binary at 4 (adjacent to ternary) and some at 2 (interior).

This structure: ternary block fires minimally (3 each), binary block has
some procs firing extra (4 instead of 2).

For ENTRY CONFLICT: we already know all these cycles have EC (from
the shadow/UEC/etc results). The question is whether our proof
MECHANISM (phase_dispatch) applies.

POSSIBLE FIX: Use the gradient between binary procs.
  Binary b (fc=4) adjacent to binary b' (fc=2).
  b fires 4 times, b' fires 2 times.
  The 2 fires of b' happen during b's 4 fires.
  At SOME firing of b, neither b' fires immediately before nor after.
  This creates a "non-mover repeat" at b for the context involving b'.

  But this is a binary-to-binary gradient, not ternary.
  We'd need a different dispatch mechanism.

SIMPLEST FIX: Route through the ternary anyway.
  Even though fc_bin=4 >= fc_ter=3 at the boundary,
  the 4 binary fires across 3 ternary phases are (2,1,1) or (3,1,0) etc.
  Can we prove that (2,1,1) is impossible (no zero phase)?

  Actually, (2,1,1) means: in 2 phases, the binary fires once; in 1 phase twice.
  This is the worst case. But the entry conflict might still exist via
  the non-zero-sided mechanism.

OR: Use fc_ter >= 6 at some ternary.
  If we can show that some ternary fires 6+ times in the gap case...

  Cycle length = 3*4 + 4*2 + 2*1 = 22 for ms=[3,3,3,2,2,2,3].
  (4 ternary at 3, 2 binary at 4, 1 binary at 2) = 12+8+2 = 22.
  But sum(ms) = 3*4+2*3 = 18. CL=22 > 18.

  Some proc fires extra. In the gap, the binary procs fire extra (4 vs 2).
  No ternary fires extra (all fc=3).

  So fc_ter=3 for all ternary in the gap case. Can't get fc_ter=6.
""")

# Verify: in gap cases, are ALL ternary at fc=3?
print("VERIFICATION: ternary fc in gap cases")
for ms, n in cases:
    max_cl = sum(ms) + 4
    words = enumerate_mover_words(ms, n, max_cl)
    ternary_pos = [i for i in range(n) if ms[i] == 3]
    ter_fc_in_gap = Counter()

    for word in words:
        fc = Counter(word)
        if not any(fc[p] >= 3 for p in range(n)):
            continue
        satisfies_A = any(
            (fc[t] >= 3 and ms[(t-1)%n] == 2 and fc[(t-1)%n] < fc[t])
            or (fc[t] >= 3 and ms[(t+1)%n] == 2 and fc[(t+1)%n] < fc[t])
            for t in ternary_pos
        )
        if satisfies_A:
            continue
        for t in ternary_pos:
            ter_fc_in_gap[fc[t]] += 1

    print(f"  ms={ms}: ternary fc in gap = {dict(sorted(ter_fc_in_gap.items()))}")

print("\n" + "=" * 70)
print("FINAL VERDICT")
print("=" * 70)
print("""
FINDINGS:

1. PIVOT (both binary neighbors) does NOT always exist.
   Fails when n >= 3b (e.g., n=9 b=3, or n=7 with certain placements).

2. BOUNDARY TERNARY (≥1 binary neighbor) ALWAYS exists when ≥3 binary.
   Every ternary with fc≥3 adjacent to binary satisfies weaker condition.

3. PIGEONHOLE (fc_bin < fc_ter) works for 98.7% of words.
   Specifically: when fc_bin = 2 (minimum) and fc_ter = 3.

4. GAP CASE (1.33%): fc_bin = 4, fc_ter = 3 at all boundary ternary.
   Pigeonhole FAILS: 4 fires across 3 phases can be (2,1,1) with no zero.
   BUT: all gap cases still have entry conflicts (100% verified).
   The EC comes from a different mechanism.

5. The gap case structure:
   - Binary procs split into "hot" (fc=4, adjacent to ternary) and
     "cold" (fc=2, interior to binary block)
   - Ternary procs all at minimum fc=3
   - This is a non-minimum-length cycle (CL > sum(ms))

RECOMMENDATIONS:
(a) If phase_dispatch_ec can work with ONE binary neighbor (not both):
    condition is fc_bin < fc_ter, covers 98.7%.
(b) For the 1.3% gap: need separate argument.
    Options: shadow cycle, direct EC check, or different gradient target.
(c) Alternatively: prove phase_dispatch_ec works whenever fc_bin <= fc_ter
    by showing the (2,1,1) distribution is impossible under walk constraints.
(d) Or: find a completely different approach that doesn't need pivots at all.
""")
