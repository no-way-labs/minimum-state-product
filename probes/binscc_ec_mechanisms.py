#!/usr/bin/env python3
"""What EC mechanisms apply to cycles WITHOUT (≥3,0)/(0,≥3)?

For n≥5, every cycle has EC at some ternary. When (≥3,0) doesn't apply,
what DOES? Candidates:
  1. (2,0)/(0,2) phase EC (not universal but ~90%)
  2. Both-Even (2,2) phase EC (not universal but ~90%)
  3. Walk-structure EC (anti-diagonal but walk forces overlap)

Classify every cycle by the weakest mechanism that gives EC.
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

def has_entry_conflict_at(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p: mover.add(lsr)
        else: nonmover.add(lsr)
    return bool(mover & nonmover)

def phase_jk(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    result = []
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        result.append((J, K))
    return result

# n=5 detailed analysis
print("=" * 70)
print("n=5: EC MECHANISM CLASSIFICATION")
print("=" * 70)

n, ms = 5, [2,3,2,3,2]
t0 = time.time()
words = enumerate_mover_words(ms, n, 16)
sandwiched = [1, 3]

total = 0
mechanism = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)

    # For each ternary, classify the EC mechanism
    cycle_mech = None
    for t in sandwiched:
        ec = has_entry_conflict_at(ms, n, word, cycle, t)
        if not ec:
            continue
        jk = phase_jk(ms, n, word, cycle, t)
        # Check which mechanism applies
        has_30 = any((J >= 3 and K == 0) or (J == 0 and K >= 3) for J, K in jk)
        has_20 = any((J >= 2 and K == 0) or (J == 0 and K >= 2) for J, K in jk)
        has_be = any(J % 2 == 0 and K % 2 == 0 and J + K > 0 for J, K in jk)

        if has_30:
            mech = "toggle≥3"
        elif has_20:
            mech = "toggle=2"
        elif has_be:
            mech = "both_even"
        else:
            mech = "walk_only"

        if cycle_mech is None or {"toggle≥3":0,"toggle=2":1,"both_even":2,"walk_only":3}[mech] > \
           {"toggle≥3":0,"toggle=2":1,"both_even":2,"walk_only":3}.get(cycle_mech, -1):
            cycle_mech = mech

    mechanism[cycle_mech] += 1

print(f"Total: {total} ({time.time()-t0:.1f}s)")
print(f"\nWeakest mechanism per cycle:")
for m, cnt in sorted(mechanism.items(), key=lambda x: -x[1]):
    print(f"  {m}: {cnt} ({100*cnt/total:.1f}%)")

# n=5: detailed phase (J,K) for walk_only cases
print(f"\n{'='*70}")
print("n=5: WALK-ONLY EC CASES (no toggle, no both-even)")
print("=" * 70)

walk_only_jk = Counter()
walk_only_count = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in sandwiched:
        ec = has_entry_conflict_at(ms, n, word, cycle, t)
        if not ec:
            continue
        jk = phase_jk(ms, n, word, cycle, t)
        has_20 = any((J >= 2 and K == 0) or (J == 0 and K >= 2) for J, K in jk)
        has_be = any(J % 2 == 0 and K % 2 == 0 and J + K > 0 for J, K in jk)
        if not has_20 and not has_be:
            walk_only_jk[tuple(jk)] += 1
            walk_only_count += 1

print(f"Walk-only phases: {walk_only_count}")
for jk, cnt in sorted(walk_only_jk.items(), key=lambda x: -x[1])[:20]:
    print(f"  {jk}: {cnt}")

# n=5: For cycles where NO ternary has (≥3,0), what gives EC?
print(f"\n{'='*70}")
print("n=5: CYCLES WITHOUT (≥3,0) — WHAT GIVES EC?")
print("=" * 70)

no_t3_mech = Counter()
no_t3_details = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    # Check if ANY ternary has (≥3,0)
    any_t3 = False
    for t in sandwiched:
        jk = phase_jk(ms, n, word, cycle, t)
        if any((J >= 3 and K == 0) or (J == 0 and K >= 3) for J, K in jk):
            any_t3 = True
    if any_t3:
        continue

    # No (≥3,0). What mechanism gives EC?
    for t in sandwiched:
        ec = has_entry_conflict_at(ms, n, word, cycle, t)
        if not ec:
            continue
        jk = phase_jk(ms, n, word, cycle, t)
        has_20 = any((J >= 2 and K == 0) or (J == 0 and K >= 2) for J, K in jk)
        has_be = any(J % 2 == 0 and K % 2 == 0 and J + K > 0 for J, K in jk)
        if has_20:
            no_t3_mech['toggle=2'] += 1
        elif has_be:
            no_t3_mech['both_even'] += 1
        else:
            no_t3_mech['walk_only'] += 1
            if len(no_t3_details) < 10:
                fc = Counter(word)
                no_t3_details.append((t, jk, [fc.get(p,0) for p in range(n)]))

print(f"EC mechanisms when no (≥3,0): {dict(no_t3_mech)}")
for t, jk, fc in no_t3_details[:5]:
    print(f"  P{t}: {jk} fc={fc}")

# KEY: What (J,K) patterns appear in walk-only EC?
# These are anti-diagonal with J,K≥1 at every phase.
# The walk structure must force overlap anyway.
print(f"\n{'='*70}")
print("WALK-ONLY EC: WHY DOES THE WALK FORCE OVERLAP?")
print("=" * 70)

# For each walk-only EC, show the actual mover/nonmover (L,R) sets per phase
walk_only_lr = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    for t in sandwiched:
        ec = has_entry_conflict_at(ms, n, word, cycle, t)
        if not ec:
            continue
        jk = phase_jk(ms, n, word, cycle, t)
        has_20 = any((J >= 2 and K == 0) or (J == 0 and K >= 2) for J, K in jk)
        has_be = any(J % 2 == 0 and K % 2 == 0 and J + K > 0 for J, K in jk)
        if has_20 or has_be:
            continue
        bL, bR = (t-1)%n, (t+1)%n
        phase_info = []
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            M = sum(1 for s in steps if word[s] == t)
            m_lr = set()
            nm_lr = set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    m_lr.add(lr)
                else:
                    nm_lr.add(lr)
            overlap = m_lr & nm_lr
            phase_info.append((J, K, M, len(steps), m_lr, nm_lr, overlap))
        if len(walk_only_lr) < 10:
            walk_only_lr.append((t, jk, phase_info))

print(f"Walk-only EC examples:")
for t, jk, phases in walk_only_lr[:5]:
    print(f"\n  P{t}: {jk}")
    for k, (J, K, M, d, mlr, nmlr, ov) in enumerate(phases):
        print(f"    Phase {k}: (J,K,M)=({J},{K},{M}) d={d}")
        print(f"      mover (L,R):    {mlr}")
        print(f"      nonmover (L,R): {nmlr}")
        print(f"      overlap:        {ov}")
