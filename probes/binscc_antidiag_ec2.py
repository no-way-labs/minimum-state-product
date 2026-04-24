#!/usr/bin/env python3
"""Fixed: anti-diagonal = no both-even phase. (1,1) is anti-diagonal.
For n=8 cycles where ALL ternary have ALL phases anti-diagonal (768 cycles):
What mechanism gives EC?
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

n, ms = 8, [2,3,2,3,2,3,2,3]
words = enumerate_mover_words(ms, n, 24)
sandwiched = [1, 3, 5, 7]

antidiag_cycles = []
total = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)
    fc = Counter(word)

    all_antidiag = True
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if J % 2 == 0 and K % 2 == 0:  # both-even → not anti-diagonal
                all_antidiag = False
                break
        if not all_antidiag:
            break

    if all_antidiag:
        antidiag_cycles.append((word, cycle))

print(f"Total: {total}, All-anti-diagonal: {len(antidiag_cycles)}")

# For each, find EC mechanism
ec_phase_jk = Counter()
# Also check: does EVERY ternary have EC, or just some?
ec_count_per_cycle = Counter()

for word, cycle in antidiag_cycles:
    ell = len(word)
    ec_procs = 0
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        mover, nonmover = set(), set()
        for s in range(ell):
            lsr = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t: mover.add(lsr)
            else: nonmover.add(lsr)
        if mover & nonmover:
            ec_procs += 1
            # Which phase?
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t: m_lr.add(lr)
                    else: nm_lr.add(lr)
                if m_lr & nm_lr:
                    ec_phase_jk[(J, K)] += 1
    ec_count_per_cycle[ec_procs] += 1

print(f"\nEC-giving phases (J,K) — anti-diagonal only:")
for (J, K), cnt in sorted(ec_phase_jk.items(), key=lambda x: -x[1]):
    print(f"  ({J},{K}): {cnt}")

print(f"\nNumber of ternary with EC per cycle:")
for ec_cnt, n_cycles in sorted(ec_count_per_cycle.items()):
    print(f"  {ec_cnt} ternary have EC: {n_cycles} cycles")

# Deep dive: (1,1) phase EC — how does it work?
print(f"\n{'='*70}")
print("(1,1) PHASE EC MECHANISM")
print("=" * 70)

examples = []
for word, cycle in antidiag_cycles:
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if J != 1 or K != 1:
                continue
            m_lr, nm_lr = set(), set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t: m_lr.add(lr)
                else: nm_lr.add(lr)
            if m_lr & nm_lr and len(examples) < 5:
                # Show detail
                mover_s = [s for s in steps if word[s] == t][0]
                prev_mover = word[(mover_s-1) % ell]
                first_neighbor = None
                for s in steps:
                    if word[s] == bL:
                        first_neighbor = 'bL'
                        break
                    elif word[s] == bR:
                        first_neighbor = 'bR'
                        break
                examples.append({
                    't': t, 'k': k, 'd': len(steps),
                    'm_lr': m_lr, 'nm_lr': nm_lr,
                    'overlap': m_lr & nm_lr,
                    'mover_from': f'P{prev_mover}',
                    'first_neighbor': first_neighbor,
                    'step_sequence': [(s, word[s], (cycle[s][bL], cycle[s][bR])) for s in steps],
                })

for ex in examples:
    print(f"\n  P{ex['t']} phase {ex['k']}: (J,K)=(1,1) d={ex['d']}")
    print(f"    mover from {ex['mover_from']}, first neighbor fire={ex['first_neighbor']}")
    print(f"    m_lr={ex['m_lr']} nm_lr={ex['nm_lr']} overlap={ex['overlap']}")
    print(f"    Steps:")
    for s, mover_proc, lr in ex['step_sequence']:
        role = "MOVER" if mover_proc == ex['t'] else f"nm(P{mover_proc})"
        print(f"      s={s:2d}: P{mover_proc} ({role:8s}) (L,R)={lr}")

# Also: for the (2,1)/(1,2) phases with EC
print(f"\n{'='*70}")
print("(2,1) PHASE EC EXAMPLES")
print("=" * 70)

examples2 = []
for word, cycle in antidiag_cycles:
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if (J, K) not in [(2, 1), (1, 2)]:
                continue
            m_lr, nm_lr = set(), set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t: m_lr.add(lr)
                else: nm_lr.add(lr)
            if m_lr & nm_lr and len(examples2) < 3:
                examples2.append({
                    't': t, 'k': k, 'J': J, 'K': K, 'd': len(steps),
                    'm_lr': m_lr, 'nm_lr': nm_lr,
                    'overlap': m_lr & nm_lr,
                    'step_sequence': [(s, word[s], (cycle[s][bL], cycle[s][bR])) for s in steps],
                })

for ex in examples2:
    print(f"\n  P{ex['t']} phase {ex['k']}: (J,K)=({ex['J']},{ex['K']}) d={ex['d']}")
    print(f"    m_lr={ex['m_lr']} nm_lr={ex['nm_lr']} overlap={ex['overlap']}")
    print(f"    Steps:")
    for s, mover_proc, lr in ex['step_sequence']:
        role = "MOVER" if mover_proc == ex['t'] else f"nm(P{mover_proc})"
        bL, bR = (ex['t']-1)%n, (ex['t']+1)%n
        fire_type = "T" if mover_proc == ex['t'] else ("bL" if mover_proc == bL else ("bR" if mover_proc == bR else "far"))
        print(f"      s={s:2d}: P{mover_proc} ({fire_type:3s}) (L,R)={lr}")
