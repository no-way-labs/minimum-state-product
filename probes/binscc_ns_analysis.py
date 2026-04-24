#!/usr/bin/env python3
"""Non-sandwiched ternary phase analysis at n=7.
Focus: (J,K) patterns at P5, FR mechanism, walk structure constraints.
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

def phase_fr_detail(ms, n, word, cycle, p):
    """Per-phase FR analysis: returns list of dicts with J, K, dur, has_fr, ordering."""
    ell = len(word)
    bL = (p - 1) % n
    bR = (p + 1) % n
    results = []
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        dur = len(steps)

        # Check FR within this phase
        mover_lr = set()
        nonmover_lr = set()
        for s in steps:
            lr = (cycle[s][bL], cycle[s][bR])
            if word[s] == p:
                mover_lr.add(lr)
            else:
                nonmover_lr.add(lr)
        has_fr = bool(mover_lr & nonmover_lr)

        # Get ordering of bL/bR firings within phase
        ordering = []
        for s in steps:
            if word[s] == bL:
                ordering.append('T')  # toggle (bL fires)
            elif word[s] == bR:
                ordering.append('I')  # increment (bR fires)

        results.append({
            'k': k, 'J': J, 'K': K, 'dur': dur,
            'has_fr': has_fr, 'ordering': ''.join(ordering),
            'mover_lr': mover_lr, 'nonmover_lr': nonmover_lr
        })
    return results

print("=" * 70)
print("NON-SANDWICHED PHASE ANALYSIS (n=7)")
print("=" * 70)

n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"Words (max_len={max_len}): {len(words)} ({time.time()-t0:.1f}s)")

total = 0
ec_by_proc = Counter()

# P5 analysis
p5_jk_dist = Counter()  # (J,K) per phase
p5_jk_fr_fail = Counter()  # (J,K) that fail FR
p5_jk_fr_hold = Counter()  # (J,K) that have FR
p5_ordering_when_fr = Counter()  # ordering of T/I when FR holds
p5_ordering_when_fail = Counter()  # ordering when FR fails
p5_all_fail = 0  # cycles where ALL P5 phases fail
p5_any_fr = 0  # cycles where SOME P5 phase has FR

# Sandwiched P1 analysis for comparison
p1_jk_dist = Counter()
p1_all_fail = 0

# Coverage analysis
sand_covers = 0
nsand_covers = 0
both_cover = 0
neither = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1

    ec_procs = set()
    for p in range(n):
        if has_entry_conflict_at(ms, n, word, cycle, p):
            ec_procs.add(p)
            ec_by_proc[p] += 1

    sand_ec = bool(ec_procs & {1, 3})
    nsand_ec = bool(ec_procs & {5, 6})

    if sand_ec and nsand_ec: both_cover += 1
    elif sand_ec: sand_covers += 1
    elif nsand_ec: nsand_covers += 1
    else: neither += 1

    # P5 phase analysis
    phases5 = phase_fr_detail(ms, n, word, cycle, 5)
    p5_has_any_fr = False
    for ph in phases5:
        p5_jk_dist[(ph['J'], ph['K'])] += 1
        if ph['has_fr']:
            p5_jk_fr_hold[(ph['J'], ph['K'])] += 1
            p5_has_any_fr = True
            if ph['ordering']:
                p5_ordering_when_fr[ph['ordering']] += 1
        else:
            p5_jk_fr_fail[(ph['J'], ph['K'])] += 1
            if ph['ordering']:
                p5_ordering_when_fail[ph['ordering']] += 1

    if p5_has_any_fr:
        p5_any_fr += 1
    else:
        p5_all_fail += 1

    # P1 phase analysis (sandwiched)
    phases1 = phase_fr_detail(ms, n, word, cycle, 1)
    p1_has_any = False
    for ph in phases1:
        p1_jk_dist[(ph['J'], ph['K'])] += 1
        if ph['has_fr']:
            p1_has_any = True
    if not p1_has_any:
        p1_all_fail += 1

    if total % 5000 == 0:
        print(f"  Progress: {total}...")

print(f"\nTotal wrap-adjacent: {total}")
print(f"Entry conflict: {sum(1 for _ in range(total))}/{total}")

print(f"\nPer-proc entry conflict:")
for p in range(n):
    ptype = "bin" if ms[p] == 2 else ("sand" if p in [1,3] else "nsand")
    rate = 100*ec_by_proc.get(p,0)/total if total > 0 else 0
    print(f"  P{p} [{ptype}]: {ec_by_proc.get(p,0)}/{total} ({rate:.1f}%)")

print(f"\nCoverage: sand_only={sand_covers}, nsand_only={nsand_covers}, both={both_cover}, neither={neither}")
print(f"Sandwiched covers: {sand_covers+both_cover}/{total} ({100*(sand_covers+both_cover)/total:.1f}%)")
print(f"Non-sandwiched covers: {nsand_covers+both_cover}/{total}")

print(f"\n{'='*60}")
print(f"P5 PHASE (J,K) DISTRIBUTION")
print(f"{'='*60}")
print(f"{'J':>3} {'K':>3} | {'Total':>6} {'FR':>6} {'Fail':>6} | {'FR%':>6} | Note")
print("-" * 60)
for (J, K), cnt in sorted(p5_jk_dist.items()):
    fr = p5_jk_fr_hold.get((J,K), 0)
    fail = p5_jk_fr_fail.get((J,K), 0)
    rate = 100*fr/cnt if cnt > 0 else 0
    note = ""
    if J % 2 == 0 and K % 3 == 0:
        note = "RETURN"
    elif rate == 0:
        note = "ANTI-DIAG"
    print(f"{J:>3} {K:>3} | {cnt:>6} {fr:>6} {fail:>6} | {rate:>5.1f}% | {note}")

print(f"\nP5 cycles: any_FR={p5_any_fr}, all_fail={p5_all_fail}")
print(f"P5 entry conflict: {ec_by_proc.get(5,0)}/{total}")
print(f"  → all_fail should equal {total} - {ec_by_proc.get(5,0)} = {total - ec_by_proc.get(5,0)}")

print(f"\n{'='*60}")
print(f"P5 FR-HOLDING ORDERINGS (top 15)")
for ordering, cnt in sorted(p5_ordering_when_fr.items(), key=lambda x: -x[1])[:15]:
    print(f"  {ordering}: {cnt}")

print(f"\nP5 FR-FAILING ORDERINGS (top 15)")
for ordering, cnt in sorted(p5_ordering_when_fail.items(), key=lambda x: -x[1])[:15]:
    J = ordering.count('T')
    K = ordering.count('I')
    print(f"  {ordering} (J={J},K={K}): {cnt}")

print(f"\n{'='*60}")
print(f"P1 SANDWICHED COMPARISON")
print(f"P1 phase (J,K) distribution:")
for (J, K), cnt in sorted(p1_jk_dist.items()):
    print(f"  J={J}, K={K}: {cnt}")
print(f"P1 all fail: {p1_all_fail}/{total}")

# KEY: When P5 all-fails, which procs rescue?
print(f"\n{'='*60}")
print(f"WHEN P5 ALL-FAILS: WHO RESCUES?")

p5_fail_rescue = Counter()
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    phases5 = phase_fr_detail(ms, n, word, cycle, 5)
    if any(ph['has_fr'] for ph in phases5):
        continue
    # P5 fails. Who rescues?
    for p in range(n):
        if has_entry_conflict_at(ms, n, word, cycle, p):
            p5_fail_rescue[p] += 1

total_p5_fail = total - ec_by_proc.get(5, 0)
print(f"P5 all-fail cycles: {total_p5_fail}")
for p in range(n):
    cnt = p5_fail_rescue.get(p, 0)
    rate = 100*cnt/total_p5_fail if total_p5_fail > 0 else 0
    print(f"  P{p}: {cnt}/{total_p5_fail} ({rate:.1f}%)")

print(f"\nTotal: {time.time()-t0:.1f}s")
