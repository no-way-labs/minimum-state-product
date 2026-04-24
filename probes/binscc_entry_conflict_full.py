#!/usr/bin/env python3
"""Full entry conflict check at ALL processors, not just sandwiched ternary.

At n=7, sandwiched-ternary FR fails at 1,208 cycles.
Check if entry conflict still holds through other processors.

Entry conflict at processor p: exists (L,S,R) = (c[bL], c[p], c[bR])
that appears at both a mover step (word[s]=p) and nonmover step (word[s]!=p).
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

def has_entry_conflict_at(ms, n, word, cycle, p):
    """Check if processor p has entry conflict (same (L,S,R) as mover and nonmover)."""
    ell = len(word)
    bL = (p - 1) % n
    bR = (p + 1) % n
    mover_lsr = set()
    nonmover_lsr = set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p:
            mover_lsr.add(lsr)
        else:
            nonmover_lsr.add(lsr)
    return bool(mover_lsr & nonmover_lsr)

def has_fr_at_sandwiched(ms, n, word, cycle, t):
    """FR at ternary t sandwiched between binaries."""
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    if ms[bL] != 2 or ms[bR] != 2:
        return None  # not sandwiched
    for k in range(ms[t]):
        ps = [s for s in range(ell) if cycle[s][t] == k]
        if len(ps) <= 1:
            continue
        mlrs = set()
        nmlrs = set()
        for s in ps:
            lr = (cycle[s][bL], cycle[s][bR])
            if word[s] == t:
                mlrs.add(lr)
            else:
                nmlrs.add(lr)
        if mlrs & nmlrs:
            return True
    return False

print("=" * 70)
print("FULL ENTRY CONFLICT CHECK AT ALL PROCESSORS")
print("=" * 70)

# n=7 first (where sandwiched FR fails at 1.2%)
n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 28

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"n={n}, ms={ms}")
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

total = 0
any_conflict = 0
no_conflict = 0
conflict_by_proc = Counter()
sandwiched_fr_fail = 0
sandwiched_fr_fail_with_other_conflict = 0
no_conflict_examples = []

tern = [p for p in range(n) if ms[p] >= 3]
binn = [p for p in range(n) if ms[p] == 2]
sandwiched = [t for t in tern if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

print(f"Binary: {binn}, Ternary: {tern}, Sandwiched: {sandwiched}")

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)

    # Check sandwiched ternary FR
    sw_fr = any(has_fr_at_sandwiched(ms, n, word, cycle, t) for t in sandwiched)

    # Check entry conflict at ALL processors
    ec_procs = set()
    for p in range(n):
        if has_entry_conflict_at(ms, n, word, cycle, p):
            ec_procs.add(p)
            conflict_by_proc[p] += 1

    if ec_procs:
        any_conflict += 1
    else:
        no_conflict += 1
        if len(no_conflict_examples) < 5:
            no_conflict_examples.append(word[:15])

    if not sw_fr:
        sandwiched_fr_fail += 1
        if ec_procs:
            sandwiched_fr_fail_with_other_conflict += 1

    if total % 20000 == 0:
        print(f"  Progress: {total}...")
        sys.stdout.flush()

print(f"\nResults for n={n}:")
print(f"  Wrap-adjacent cycles: {total}")
print(f"  Entry conflict at ANY proc: {any_conflict}/{total} ({100*any_conflict/total:.1f}%)")
print(f"  No entry conflict: {no_conflict}")
print(f"  Sandwiched FR fail: {sandwiched_fr_fail}")
print(f"  Sandwiched FR fail BUT other conflict: "
      f"{sandwiched_fr_fail_with_other_conflict}/{sandwiched_fr_fail}")

print(f"\n  Entry conflict by processor:")
for p in range(n):
    rate = 100 * conflict_by_proc.get(p, 0) / total if total > 0 else 0
    label = f"ms={ms[p]}"
    if p in sandwiched:
        label += " (sandwiched)"
    print(f"    P{p} [{label}]: {conflict_by_proc.get(p, 0)}/{total} ({rate:.1f}%)")

if no_conflict_examples:
    print(f"\n  No-conflict cycle examples:")
    for ex in no_conflict_examples:
        print(f"    {list(ex)}...")

# Also check: for sandwiched-FR-fail cycles, WHERE does conflict come from?
if sandwiched_fr_fail > 0:
    print(f"\n  When sandwiched FR fails, conflict comes from:")
    conflict_source = Counter()
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        sw_fr = any(has_fr_at_sandwiched(ms, n, word, cycle, t) for t in sandwiched)
        if sw_fr:
            continue
        for p in range(n):
            if has_entry_conflict_at(ms, n, word, cycle, p):
                conflict_source[p] += 1
    for p in range(n):
        if conflict_source.get(p, 0) > 0:
            print(f"    P{p} [ms={ms[p]}]: {conflict_source[p]}/{sandwiched_fr_fail} "
                  f"({100*conflict_source[p]/sandwiched_fr_fail:.1f}%)")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
sys.stdout.flush()
