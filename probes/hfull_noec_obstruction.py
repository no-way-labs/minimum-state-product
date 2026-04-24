#!/usr/bin/env python3
"""
Investigate WHY hfull + ¬EC is impossible at n≥9 with sub-threshold
non-consecutive binary systems.

APPROACH:
1. Under ¬EC, gap1_ec forces the mover sequence to be a ring-adjacent walk.
2. For hfull, this walk must cover all n processors.
3. Each proc fires ≥2 (must return to start value), so CL ≥ 2n.
4. Binary proc with fc=2: fires exactly twice, seeing 2 distinct mover triples.
   Both mover triples must NOT appear at any non-mover step.
5. KEY: when a binary proc fires with context (L, v, R), the new value is 1-v.
   So the config changes at p. The "after" triple at p is (L, 1-v, R) — and
   this becomes a non-mover triple at p for the NEXT step (since someone else
   fires next, assuming the walk moves on).

STRUCTURAL ARGUMENT:
Under ¬EC at binary proc p (m_p=2):
- Mover triple (L, v, R): p fires, changing v → 1-v.
  The next step sees triple (L, 1-v, R) at p (since p's value changed).
  If the next mover is NOT p, this is a non-mover triple.
  So (L, 1-v, R) is a non-mover triple.
  For ¬EC: (L, 1-v, R) must NOT be a mover triple.

  So if (L, 0, R) is a mover triple, (L, 1, R) is a non-mover triple (and NOT mover).
  If (L, 1, R) is a mover triple, (L, 0, R) is a non-mover triple (and NOT mover).

  The two mover triples at p (fc=2) fire with values v₁ and v₂.
  Since p returns to start: v₁ and v₂ are 0 and 1 (in some order).
  So mover triples are (L₁, 0, R₁) and (L₂, 1, R₂).
  The "after" triples are (L₁, 1, R₁) and (L₂, 0, R₂) — both non-mover.

  ¬EC requires: {(L₁, 0, R₁), (L₂, 1, R₂)} ∩ non-mover triples = ∅.
  We know (L₁, 1, R₁) and (L₂, 0, R₂) ARE non-mover triples.
  So we need (L₁, 0, R₁) ≠ (L₂, 0, R₂) and (L₂, 1, R₂) ≠ (L₁, 1, R₁).
  i.e., (L₁, R₁) ≠ (L₂, R₂). The two firings must see DIFFERENT (L,R) contexts.
  This is necessary but not sufficient.

Let's also check:
- When p fires for the FIRST time (step k₁), what's the triple at p?
  Right BEFORE step k₁: triple is (L₁, v₁, R₁). Mover is p.
  Right AFTER step k₁: p's value changes. Triple becomes (L₁, 1-v₁, R₁).

  But wait: the NEXT step (k₁+1) has a different mover (walk moves on).
  But the context (L, R) at p could change if the mover at step k₁+1 is
  adjacent to p (which it must be, since walk is ring-adjacent).
  If mover at k₁+1 = left(p): L changes. New triple at p for step k₁+1
  is (L₁', 1-v₁, R₁) where L₁' is the new value of left(p).
  If mover at k₁+1 = p: p fires again (same position in walk).
  If mover at k₁+1 = right(p): R changes.

THIS IS GETTING COMPLEX. Let me just do EXHAUSTIVE COMPUTATION.
"""
import random
from itertools import product as iterproduct
from collections import Counter, defaultdict
import sys

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def has_entry_conflict_at(configs, movers, n, p):
    """Check EC at specific processor p."""
    CL = len(configs)
    mt = set()
    nmt = set()
    for k in range(CL):
        triple = (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n])
        if movers[k] == p:
            mt.add(triple)
        else:
            nmt.add(triple)
    return bool(mt & nmt)

def has_entry_conflict(configs, movers, n):
    for p in range(n):
        if has_entry_conflict_at(configs, movers, n, p):
            return True
    return False

def is_ring_adjacent_walk(movers, n):
    CL = len(movers)
    for k in range(CL):
        if ring_dist(movers[k], movers[(k+1)%CL], n) > 1:
            return False
    return True

def search_exhaustive_small(n, ms, max_CL=None):
    """For small n, exhaustively enumerate ALL good cycles via BFS on
    the full configuration graph, then check EC + hfull."""
    from itertools import product as iterproduct

    prod = 1
    for m in ms:
        prod *= m
    if prod > 5000:
        print(f"  Product {prod} too large for exhaustive search")
        return None

    if max_CL is None:
        max_CL = prod

    configs = list(iterproduct(*[range(m) for m in ms]))
    config_set = set(configs)

    # Build successor graph: from each config, find all privileged procs
    # and their successors. We need to try ALL possible transition functions.
    # That's way too many. Instead, for each config and each privileged proc,
    # we generate all possible next configs (by changing that proc to any other value).
    # A "good cycle" is: a cycle in the graph where each edge = one proc changes value.

    # Actually, good cycles come from a SPECIFIC transition function.
    # Let's enumerate transition functions... too many.
    # Random search is better.

    return None

def deep_random_search(n, ms, num_trials=1000000, max_steps=5000):
    """Deep random search specifically looking for ¬EC + hfull."""
    noec_cycles = []
    noec_hfull = []

    for trial in range(num_trials):
        if trial % 100000 == 0 and trial > 0:
            print(f"  trial {trial}, ¬EC found: {len(noec_cycles)}, hfull: {len(noec_hfull)}")

        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        history = [config]
        history_movers = []
        config_to_step = {config: 0}

        for step in range(max_steps):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break
            p = random.choice(privs)
            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)

            if config in config_to_step:
                cs = config_to_step[config]
                cycle_configs = history[cs:]
                cycle_movers = history_movers[cs:] + [p]
                CL = len(cycle_configs)

                ec = has_entry_conflict(cycle_configs, cycle_movers, n)
                if not ec:
                    fc = [0]*n
                    for m in cycle_movers:
                        fc[m] += 1
                    hfull = all(f > 0 for f in fc)
                    adj = is_ring_adjacent_walk(cycle_movers, n)

                    noec_cycles.append({
                        'CL': CL, 'fc': fc, 'adj': adj, 'hfull': hfull,
                        'movers': cycle_movers,
                        'active': [i for i in range(n) if fc[i] > 0],
                    })
                    if hfull:
                        noec_hfull.append(noec_cycles[-1])
                break

            config_to_step[config] = step + 1
            history.append(config)
            history_movers.append(p)

    return noec_cycles, noec_hfull

def analyze_arc_coverage(noec_cycles, n):
    """Analyze how much of the ring ¬EC cycles cover."""
    if not noec_cycles:
        print("  No ¬EC cycles found.")
        return

    arc_lengths = [len(c['active']) for c in noec_cycles]
    cl_dist = Counter(c['CL'] for c in noec_cycles)
    arc_dist = Counter(len(c['active']) for c in noec_cycles)

    print(f"  Total ¬EC cycles: {len(noec_cycles)}")
    print(f"  CL distribution: {dict(sorted(cl_dist.items())[:15])}")
    print(f"  Active proc count: {dict(sorted(arc_dist.items()))}")

    # Check: are active procs always contiguous?
    contiguous = 0
    for c in noec_cycles:
        active = sorted(c['active'])
        if len(active) <= 1:
            contiguous += 1
            continue
        # Check contiguity on ring
        is_cont = True
        for i in range(len(active)):
            if ring_dist(active[i], active[(i+1)%len(active)], n) > 1:
                is_cont = False
                break
        # Actually need to check if they form a contiguous ARC
        # Sort and check gaps
        gaps = [(active[(i+1)%len(active)] - active[i]) % n for i in range(len(active))]
        # Contiguous arc: at most one gap > 1
        big_gaps = sum(1 for g in gaps if g > 1)
        if big_gaps <= 1:
            contiguous += 1

    print(f"  Contiguous arc: {contiguous}/{len(noec_cycles)}")

    # Ring-adjacent check
    adj_count = sum(1 for c in noec_cycles if c['adj'])
    print(f"  Ring-adjacent walk: {adj_count}/{len(noec_cycles)} ({100*adj_count/len(noec_cycles):.1f}%)")

    # Max active procs
    max_active = max(arc_lengths)
    print(f"  Max active procs: {max_active} out of {n}")

    if max_active < n:
        print(f"  ** NEVER reaches all {n} procs — hfull IMPOSSIBLE under ¬EC **")

    # Show some examples
    print(f"  Examples (first 5):")
    for c in noec_cycles[:5]:
        print(f"    CL={c['CL']}, fc={c['fc']}, active={c['active']}, adj={c['adj']}")

def main():
    print("INVESTIGATION: hfull + ¬EC impossibility")
    print("="*70)

    for n in [5, 7, 9, 11]:
        if n == 5:
            ms_candidates = [
                [2, 3, 2, 3, 2],
            ]
            trials = 500000
        elif n == 7:
            ms_candidates = [
                [2, 3, 2, 3, 2, 3, 3],
                [2, 3, 3, 2, 3, 2, 3],
            ]
            trials = 500000
        elif n == 9:
            ms_candidates = [
                [2, 3, 2, 3, 2, 3, 3, 3, 3],
                [2, 3, 3, 2, 3, 3, 2, 3, 3],
            ]
            trials = 500000
        else:  # n=11
            ms_candidates = [
                [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3],
            ]
            trials = 300000

        for ms in ms_candidates:
            prod = 1
            for m in ms:
                prod *= m
            thresh = 4 * 3**(n-2)
            binary_pos = [i for i in range(n) if ms[i] == 2]

            print(f"\n{'='*70}")
            print(f"n={n}, ms={ms}")
            print(f"Product={prod}, threshold={thresh}, sub={prod < thresh}")
            print(f"Binary at: {binary_pos}")
            print(f"Non-consecutive: {all(ring_dist(binary_pos[i], binary_pos[j], n) > 1 for i in range(len(binary_pos)) for j in range(i+1, len(binary_pos)))}")
            print(f"{'='*70}")

            noec, hfull_cycles = deep_random_search(n, ms, num_trials=trials)
            analyze_arc_coverage(noec, n)

            if hfull_cycles:
                print(f"\n  *** FOUND hfull + ¬EC cycle! ***")
                for c in hfull_cycles[:3]:
                    print(f"    CL={c['CL']}, fc={c['fc']}")
            else:
                print(f"\n  NO hfull + ¬EC cycle found in {trials} trials.")

if __name__ == '__main__':
    main()
