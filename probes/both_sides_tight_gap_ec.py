#!/usr/bin/env python3
"""
Critical check: at each step of the chain, does the GAP case always
eventually occur? Or does the chain always go tight to the end?

If there's always a gap at some intermediate step, the proof is simpler:
the recursive chain lemma terminates at the gap, producing EC at that proc.

If the chain sometimes goes tight all the way to depth n-2, we need the
full-sweep EC argument.

Let me check the chain termination precisely: for each sorry case,
trace the chain and record whether it terminates via gap or via no-fire.
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
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


def trace_chain_detailed(word, interior, n, start_proc, direction):
    """
    Trace the chain from start_proc. The chain works by finding first fires
    of successive procs going in 'direction', and checking if the next-outward
    proc fires (tight) or not.

    The chain here is the Lean-style chain:
    For each proc p, find LAST fire of next-outward before p's FIRST fire.
    If no fire: chain terminates. If fire but not tight: gap -> EC.
    If tight: extend chain to next-outward.

    Returns list of (proc, first_fire_idx, termination_type)
    """
    int_len = len(interior)
    chain = []

    current_proc = start_proc
    # Find first fire of start_proc
    current_first = None
    for i in range(int_len):
        if word[interior[i]] == current_proc:
            current_first = i
            break
    if current_first is None:
        return chain, 'start_not_found'

    for depth in range(n):
        next_proc = (current_proc + direction) % n

        # Find last fire of next_proc in [0, current_first)
        last_next = None
        for i in range(current_first - 1, -1, -1):
            if word[interior[i]] == next_proc:
                last_next = i
                break

        if last_next is None:
            chain.append({
                'proc': current_proc,
                'first_fire': current_first,
                'term': 'no_fire',
                'next': next_proc,
                'depth': depth,
            })
            return chain, 'no_fire'

        if last_next < current_first - 1:
            chain.append({
                'proc': current_proc,
                'first_fire': current_first,
                'term': 'gap',
                'next': next_proc,
                'last_next': last_next,
                'depth': depth,
            })
            return chain, 'gap'

        # Tight: last_next = current_first - 1
        chain.append({
            'proc': current_proc,
            'first_fire': current_first,
            'term': 'tight',
            'next': next_proc,
            'depth': depth,
        })

        # Move to first fire of next_proc
        next_first = None
        for i in range(int_len):
            if word[interior[i]] == next_proc:
                next_first = i
                break

        current_proc = next_proc
        current_first = next_first

    return chain, 'max_depth'


print("="*70)
print("CHAIN TERMINATION TYPE ANALYSIS")
print("="*70)
print()

for n, ms, max_len in [
    (5, [2, 3, 2, 3, 2], 18),
    (7, [2, 3, 2, 3, 2, 3, 3], 24),
    (7, [2, 3, 3, 2, 3, 2, 3], 24),
]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    words = enumerate_mover_words(ms, n, max_len)
    term_types = Counter()
    depth_at_term = Counter()
    sorry_count = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)

        for t in sandwiched:
            bL = (t-1) % n
            bR = (t+1) % n
            LL = (t-2) % n
            RR = (t+2) % n
            LLL = (t-3) % n
            RRR = (t+3) % n

            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if len(t_fires) < 2:
                continue

            for idx in range(len(t_fires)):
                s_step = t_fires[idx]
                a_step = t_fires[(idx-1) % len(t_fires)]
                if s_step > a_step:
                    interior = list(range(a_step+1, s_step))
                else:
                    interior = list(range(a_step+1, ell)) + list(range(0, s_step))
                if not interior:
                    continue

                J = sum(1 for st in interior if word[st] == bL)
                K = sum(1 for st in interior if word[st] == bR)
                if J < 1 or K < 1:
                    continue

                fL_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
                fR_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

                # Check sorry conditions
                sorry = False
                chain_start = None
                chain_dir = None

                if fR_idx == 0 and fL_idx > 0:
                    ll_pos = [i for i in range(fL_idx) if word[interior[i]] == LL]
                    if ll_pos and ll_pos[-1] == fL_idx - 1:
                        first_ll = ll_pos[0]
                        if any(word[interior[i]] == LLL for i in range(first_ll)):
                            sorry = True
                            # Chain goes LEFT from bL
                            chain_start = LL  # Start chain from LL (the proc with tight)
                            chain_dir = -1

                if fL_idx == 0 and fR_idx > 0:
                    rr_pos = [i for i in range(fR_idx) if word[interior[i]] == RR]
                    if rr_pos and rr_pos[-1] == fR_idx - 1:
                        first_rr = rr_pos[0]
                        if any(word[interior[i]] == RRR for i in range(first_rr)):
                            sorry = True
                            chain_start = RR
                            chain_dir = +1

                if not sorry:
                    continue

                sorry_count += 1
                chain, result = trace_chain_detailed(word, interior, n, chain_start, chain_dir)
                term_types[result] += 1
                if chain:
                    depth_at_term[chain[-1]['depth']] += 1

    print(f"n={n}, ms={ms}:")
    print(f"  Sorry count: {sorry_count}")
    print(f"  Termination types: {dict(term_types)}")
    print(f"  Depth at termination: {dict(sorted(depth_at_term.items()))}")

# The chain starts from LL (not bL). So it traces LL, LLL, left^4(t), ...
# If it terminates at 'gap': EC at LL (or the gap proc) via configVal_eq_of_noFire_between.
# If 'no_fire': either contradiction via walk constraint or need sweep argument.

print()
print("="*70)
print("KEY INSIGHT")
print("="*70)
print()
print("The chain starts from LL (the second neighbor), NOT from bL.")
print("The sorry is reached because LLL fires before first LL.")
print("So the chain starts at LL and checks: does left^3(t) fire?")
print("  Yes (we know this). Is it tight to LL's first fire?")
print("  If not: gap -> EC at LL.")
print("  If yes: chain extends to LLL.")
print("  Does left^4(t) fire before first LLL?")
print("  ...")
print()
print("When the chain terminates at no_fire:")
print("  The chain has gone LL -> LLL -> left^4 -> ... -> p")
print("  and left(p) doesn't fire before first(p) in interior.")
print("  Then: EC at p between first(p) and some nonmover step.")
print("  The nonmover: step interior[first(p)-1] or step a.")
print()
print("For the Lean proof: the recursive lemma handles this.")
print("At each step, either gap (EC) or tight (recurse).")
print("Termination: first_fire index decreases, bounded by interior length.")
print()
print("When the chain reaches first_fire = 0:")
print("  p fires at interior[0]. left(p) doesn't fire before it.")
print("  But interior[0] = phase.a. And moverAt(phase.a) = p.")
print("  The nonmover step: step a (= prev t-fire). moverAt(a) = t.")
print("  t is a ring-neighbor of phase.a's mover... or is it?")
print()
print("  Actually: the chain started from LL = left^2(t).")
print("  After d tight steps: p = left^(d+2)(t).")
print("  At d = n-4: p = left^(n-2)(t) = right^2(t) = RR.")
print("  At d = n-3: p = left^(n-1)(t) = right(t) = bR.")
print("  At d = n-2: p = left^n(t) = t. But t doesn't fire in interior!")
print()
print("  So the chain can go at most n-3 steps from LL before reaching bR.")
print("  At bR: first fire at interior[0] (if bR fires at phase.a = fR).")
print("  Actually fR = phase.a in sorry 1077. So yes, bR fires at interior[0].")
print("  left(bR) = t. Does t fire in [0, 0) = empty? No fire. Chain terminates.")
print()
print("  EC at bR: mover step interior[0] fires bR. Nonmover step: need step")
print("  with same triple at bR. Step a fires t = left(bR). Triple at bR")
print("  changes because left(bR) fires at step a. So step a doesn't work.")
print()
print("  BUT: there's a step AFTER the interior (step s) that fires t.")
print("  Step s = current t-fire. Between step s and some other step:")
print("  can we find a nonmover for bR with same triple?")
print()
print("  Actually, the chain first_fire index is 0 for the FIRST fire of bR.")
print("  But bR's first fire in the interval [phase.a, s) is at phase.a = interior[0].")
print("  The walk constraint says interior[0] fires bL or bR. It fires bR (since fR = phase.a).")
print("  So bR fires at the very start. Before it: only step a (fires t).")
print("  step a changes bR's triple. No good for EC between a and interior[0].")
print()
print("  HOWEVER: we don't need EC at bR. At the PREVIOUS chain step:")
print("  p = right^3(t) fires at some interior index > 0.")
print("  left(p) = right^2(t) = RR fires at index first(p) - 1 (tight).")
print("  The EC would be at p between first(p) and some nonmover step in (first(p)-1, first(p)).")
print("  But the gap is only 1 step... no room for a nonmover.")
print()
print("  This is why the chain is always tight: there's no gap for EC.")
print("  The chain goes all the way to bR, and the argument breaks down.")
print()
print("  CONCLUSION: The chain-extension approach alone CANNOT produce EC.")
print("  The proof needs a DIFFERENT mechanism at the full-sweep termination.")
