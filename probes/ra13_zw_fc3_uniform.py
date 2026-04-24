#!/usr/bin/env python3
"""
RA13: Focus on uniform fc case (all procs same fc).

When all fc = k (same value), pigeonhole by fc comparison fails.
BUT: binary procs have even fc. If k is odd: no binary can have fc = k.
Contradiction with ≥3 binary having fc ≥ 3.

If k is even (≥4): binary fc = k, ternary fc = k.
CL = n*k. Each neighbor fires k times over k phases.
Could be (1,1,...,1) for each → all phases (1,1) → NOT dispatchable.

But: is this ACTUALLY realizable? Let me check.

Also: the key question is whether EVEN-EVEN phases exist.
With J summing to k and K summing to k, over k phases:
If all (J_i, K_i) = (1,1): non-dispatchable.
But the MOVER WALK constrains which phases are possible!

ZW: cw = ccw. This constrains the walk structure.
The mover walk determines the phase structure.

Let me check: for uniform fc cycles, what phase patterns occur?
"""

from itertools import product as iterproduct
from collections import defaultdict
import random

random.seed(42)


def classify_step(prev, curr, n):
    d = (curr - prev) % n
    if d == 1: return 'cw'
    elif d == n-1: return 'ccw'
    else: return 'other'


def build_adj(ms):
    n = len(ms)
    all_c = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_c:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c); c2[p] = v
                    adj[c].append((tuple(c2), p))
    return all_c, adj


def find_zw_cycles(ms, all_c, adj, num=500000, maxs=100):
    n = len(ms)
    unique = {}
    for _ in range(num):
        c = random.choice(all_c)
        vis = {c: 0}; path = [c]; mov = []
        for step in range(1, maxs):
            nb = adj[c]
            if not nb: break
            c, p = random.choice(nb)
            mov.append(p)
            if c in vis:
                s = vis[c]; cc = path[s:]; cm = mov[s:]; L = len(cm)
                if L < 2*n: break
                fc = defaultdict(int)
                for m in cm: fc[m] += 1
                if len(fc) < n or min(fc.values()) < 2: break
                cw = ccw = 0
                for i in range(L):
                    t = classify_step(cm[i-1], cm[i], n)
                    if t == 'cw': cw += 1
                    elif t == 'ccw': ccw += 1
                if cw != ccw or cw == 0: break
                if max(fc.values()) < 3: break
                key = (cc[0], tuple(cm))
                unique[key] = {'configs': cc, 'movers': cm, 'fc': dict(fc), 'length': L}
                break
            vis[c] = step; path.append(c)
    return list(unique.values())


def get_phases(movers, q, n):
    L = len(movers)
    fire_pos = [i for i, m in enumerate(movers) if m == q]
    if not fire_pos: return []
    lq = (q-1)%n; rq = (q+1)%n
    phases = []
    for pi in range(len(fire_pos)):
        s = fire_pos[pi]; e = fire_pos[(pi+1)%len(fire_pos)]
        J = K = 0; pos = (s+1)%L
        while pos != e:
            if movers[pos] == lq: J += 1
            if movers[pos] == rq: K += 1
            pos = (pos+1)%L
        phases.append((J, K))
    return phases


def main():
    print("=" * 70)
    print("RA13: Uniform fc analysis (all procs same fc)")
    print("=" * 70)

    # Test all-binary at n=5
    for n in [5, 7, 9]:
        print(f"\n{'='*60}")
        print(f"n = {n}")

        # All binary
        ms = tuple([2]*n)
        P = 2**n
        threshold = 4 * 3**(n-2)
        print(f"ms={ms}, P={P}, threshold={threshold}, sub-threshold={P < threshold}")

        if P >= threshold:
            print("  NOT sub-threshold, skip")
            continue

        all_c, adj = build_adj(ms)
        cycles = find_zw_cycles(ms, all_c, adj, num=500000, maxs=100)
        print(f"  ZW fc≥3 cycles: {len(cycles)}")

        uniform_count = 0
        non_uniform_count = 0
        uniform_dispatchable = 0
        uniform_not_dispatchable = 0

        for cyc in cycles:
            fc = cyc['fc']
            fc_vals = [fc[q] for q in range(n)]

            if len(set(fc_vals)) == 1:
                uniform_count += 1
                k = fc_vals[0]

                # Check dispatchable
                movers = cyc['movers']
                found = False
                for q in range(n):
                    phases = get_phases(movers, q, n)
                    for J, K in phases:
                        if J == 0 or K == 0 or (J%2==0 and K%2==0):
                            found = True; break
                    if found: break

                if found:
                    uniform_dispatchable += 1
                else:
                    uniform_not_dispatchable += 1
                    # Show details
                    if uniform_not_dispatchable <= 3:
                        print(f"\n    UNIFORM fc={k}, NOT dispatchable!")
                        for q in range(n):
                            phases = get_phases(movers, q, n)
                            print(f"      q={q}: phases={phases}")
                        print(f"      movers={list(movers[:30])}")
            else:
                non_uniform_count += 1

        print(f"  Uniform fc: {uniform_count}, non-uniform: {non_uniform_count}")
        if uniform_count > 0:
            print(f"  Uniform dispatchable: {uniform_dispatchable}/{uniform_count}")
            print(f"  Uniform NOT dispatchable: {uniform_not_dispatchable}/{uniform_count}")

    # Also test: 3 binary + ternary rest at small n
    print("\n\n--- Mixed ms, uniform fc ---")
    for ms in [(2,2,2,3,3), (2,2,3,2,3), (2,3,2,3,2)]:
        n = len(ms)
        P = 1
        for m in ms: P *= m
        threshold = 4 * 3**(n-2)
        if P >= threshold: continue

        all_c, adj = build_adj(ms)
        cycles = find_zw_cycles(ms, all_c, adj, num=500000)

        uniform = 0
        for cyc in cycles:
            fc = cyc['fc']
            if len(set(fc[q] for q in range(n))) == 1:
                uniform += 1
                # But: ternary fc = binary fc. Binary fc is even.
                # So fc must be even. For ternary, fc can be any value.
                # If uniform even: fc(ternary) = even, fc(binary) = even.
                k = fc[0]
                print(f"  ms={ms}: uniform fc={k}, CL={cyc['length']}")

                # Check: is ternary fc = even possible?
                # Ternary fires k times. Must cycle back: k % 3 = 0.
                # No: ternary fires k times, each fire changes state.
                # Start and end at same state. So: k * delta ≡ 0 (mod 3).
                # If delta = +1 each time: k ≡ 0 (mod 3).
                # But delta can vary! So no constraint.

        print(f"  ms={ms}: {uniform} uniform-fc cycles out of {len(cycles)}")

    # KEY REALIZATION
    print("\n" + "=" * 60)
    print("KEY THEORETICAL ARGUMENT")
    print("=" * 60)
    print("""
For S=all (every fc ≥ 3), the GENERALIZED gradient works:

CLAIM: In any ring graph, if fc: Z_n → Z with fc(q) ≥ 3 for all q,
then there exists q such that fc(q) > min(fc(left(q)), fc(right(q))).

Proof: Consider q* = argmax fc. Then fc(q*) ≥ fc(p) for all p.
If fc is not constant: fc(q*) > fc(p) for some neighbor p. Done.
If fc IS constant: fc(q) = k for all q. Binary have even fc.
  If k odd: binary can't have fc = k. Contradiction with ≥3 binary.
  If k even: all binary fire k ≥ 4 times. CL = nk.

  For k even, k ≥ 4: consider binary proc b.
  fc(b) = k phases. Left neighbor fires k times over k phases.
  k fires over k phases: exactly 1 fire per phase → all (1,...).
  But this means the mover walk has a very specific pattern:
  between consecutive firings of b, exactly one left-fire and one right-fire.

  This means: at each phase of b, exactly 2 "other" fires happen
  (one left, one right). So each phase has total fires = 1+1+... = k/k = uh...

  Wait. In each phase of b, there are (CL/k) - 1 = n-1 other steps.
  Those n-1 steps are distributed among n-1 other procs.
  Each of the n-1 other procs fires k times total, over k phases of b.
  If uniform: each fires exactly 1 time per phase.

  This means: in each phase of b, EVERY other proc fires exactly once.
  Each phase has n-1 other-firings + 1 b-firing (at start) = n steps.
  CL = kn. Check: CL = kn, k phases, each n steps. Consistent.

  So: uniform fc with k fires per phase means EACH phase of b looks like:
  b fires, then each other proc fires exactly once (in some order).
  The ZW constraint then forces specific orderings.

  But the PHASE ANALYSIS says: J = 1, K = 1 in every phase.
  All phases (1,1). This IS non-dispatchable.

  HOWEVER: can this actually be a valid good cycle?
  Each phase: b fires, then n-1 other procs fire once each.
  The order within each phase matters.
  The config must be distinct at each step.
  And the cycle must close.

  Is this achievable? Let me check computationally.
""")

    # Check: do uniform-fc all-binary ZW cycles with all phases (1,1) exist?
    ms = (2,2,2,2,2)
    n = 5
    all_c, adj = build_adj(ms)
    cycles = find_zw_cycles(ms, all_c, adj, num=1000000, maxs=60)
    print(f"\nms={ms}: {len(cycles)} ZW fc≥3 cycles")

    all_11 = 0
    for cyc in cycles:
        fc = cyc['fc']
        if len(set(fc[q] for q in range(n))) != 1:
            continue
        movers = cyc['movers']
        all_phases_11 = True
        for q in range(n):
            phases = get_phases(movers, q, n)
            if not all(J == 1 and K == 1 for J, K in phases):
                all_phases_11 = False
                break
        if all_phases_11:
            all_11 += 1
            k = fc[0]
            print(f"  ALL phases (1,1)! fc={k}, CL={cyc['length']}")
            # Show mover sequence
            print(f"    movers={list(movers)}")

    print(f"\n  Total uniform-fc with all phases (1,1): {all_11}")


if __name__ == '__main__':
    main()
