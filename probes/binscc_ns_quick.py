#!/usr/bin/env python3
"""Quick non-sandwiched ternary analysis at n=7 with reduced max_len."""
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

def get_phase_jk(ms, n, word, cycle, p):
    """Get (J, K) = (bL firings, bR firings) per phase of p."""
    ell = len(word)
    bL = (p - 1) % n
    bR = (p + 1) % n
    result = []
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        dur = len(steps)
        result.append((J, K, dur))
    return result

print("=" * 70)
print("NON-SANDWICHED ANALYSIS (n=7, quick)")
print("=" * 70)

n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 21  # reduced for speed

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"Words (max_len={max_len}): {len(words)} ({time.time()-t0:.1f}s)")

total = 0
ec_any = 0
ec_by_proc = Counter()
p5_union_p6 = 0
p5_and_p6 = 0
sandwiched_only = 0
nonsand_only = 0
both_types = 0
neither_type = 0

p5_jk_all = Counter()  # (J,K) at P5 across all phases
p5_jk_failing = Counter()  # (J,K) at P5 when P5's FR fails at that phase
p5_all_phases_fail = 0  # cycles where ALL P5 phases fail FR

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

    if ec_procs:
        ec_any += 1

    # Sandwiched vs non-sandwiched
    sand_ec = bool(ec_procs & {1, 3})
    nsand_ec = bool(ec_procs & {5, 6})
    p5_ec = 5 in ec_procs
    p6_ec = 6 in ec_procs

    if p5_ec or p6_ec:
        p5_union_p6 += 1
    if p5_ec and p6_ec:
        p5_and_p6 += 1
    if sand_ec and not nsand_ec:
        sandwiched_only += 1
    elif nsand_ec and not sand_ec:
        nonsand_only += 1
    elif sand_ec and nsand_ec:
        both_types += 1
    else:
        neither_type += 1

    # Phase (J,K) analysis at P5
    phases = get_phase_jk(ms, n, word, cycle, 5)
    all_fail = True
    for J, K, dur in phases:
        p5_jk_all[(J, K)] += 1
        # Check FR at this specific phase
        bL, bR = 4, 6
        phase_k = phases.index((J, K, dur))  # not exactly right but close
        # Actually check entry conflict WITHIN this phase
        ell = len(word)
        for k in range(ms[5]):
            steps = [s for s in range(ell) if cycle[s][5] == k]
            mover_lr = set()
            nonmover_lr = set()
            for s in steps:
                lr = (cycle[s][4], cycle[s][6])
                if word[s] == 5:
                    mover_lr.add(lr)
                else:
                    nonmover_lr.add(lr)
            if mover_lr & nonmover_lr:
                all_fail = False
            else:
                Jk = sum(1 for s in steps if word[s] == 4)
                Kk = sum(1 for s in steps if word[s] == 6)
                p5_jk_failing[(Jk, Kk)] += 1
        break  # only do this once per cycle

    if all_fail:
        p5_all_phases_fail += 1

print(f"\nTotal wrap-adjacent cycles: {total}")
print(f"Entry conflict at ANY proc: {ec_any}/{total}")

print(f"\nPer-processor:")
for p in range(n):
    ptype = "bin" if ms[p] == 2 else ("sand" if p in [1,3] else "nsand")
    rate = 100*ec_by_proc.get(p,0)/total if total > 0 else 0
    print(f"  P{p} [{ptype}]: {ec_by_proc.get(p,0)}/{total} ({rate:.1f}%)")

print(f"\nCoverage decomposition:")
print(f"  Sand only: {sandwiched_only}, NSand only: {nonsand_only}")
print(f"  Both: {both_types}, Neither: {neither_type}")
print(f"  P5∪P6: {p5_union_p6}/{total}")
print(f"  P5∩P6: {p5_and_p6}/{total}")

print(f"\nP5 phase (J,K) distribution (top 20):")
for (J, K), cnt in sorted(p5_jk_all.items(), key=lambda x: -x[1])[:20]:
    bL_mod = "even" if J % 2 == 0 else "odd"
    bR_mod = f"≡{K%3}mod3"
    note = "RETURN" if J % 2 == 0 and K % 3 == 0 else ""
    print(f"  J={J}, K={K} [{bL_mod},{bR_mod}]: {cnt}  {note}")

print(f"\nP5 phase (J,K) at FR-failing phases:")
for (J, K), cnt in sorted(p5_jk_failing.items(), key=lambda x: -x[1])[:15]:
    print(f"  J={J}, K={K}: {cnt}")

print(f"\nP5 ALL phases fail FR: {p5_all_phases_fail}/{total}")
print(f"  → P5 entry conflict: {ec_by_proc.get(5,0)}/{total}")

print(f"\nElapsed: {time.time()-t0:.1f}s")
