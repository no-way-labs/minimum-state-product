#!/usr/bin/env python3
"""
BREAKTHROUGH APPROACH: Extend the shadow/flip construction to handle both axioms.

The existing PROVED theorems in CaseObstructions.lean use a "flipConfig" shadow
construction that works when there exists a "far" processor q such that flipping
q's value doesn't affect any mover's privilege.

For the TWO REMAINING AXIOMS, this fails because no "safe" processor exists
(every processor is within distance 1 of some mover).

NEW IDEA: Instead of flipping a SINGLE processor, flip a SUBSET of processors
whose values don't affect any mover's privilege. Even if no single processor
is "safe" (far from all movers), there may exist a processor q that is far from
all SIMULTANEOUS movers at each step.

More precisely: at each step k, the mover is moverAt(k) = p_k. Processor q
is "locally safe at step k" if q ≠ p_k, q ≠ left(p_k), q ≠ right(p_k).

The safe processor condition requires q to be locally safe at ALL steps.
But for the flip to work, we only need:
  1. Shadow configs differ from good configs (flip changes q's value)
  2. At each step k, the mover p_k is still privileged in the shadow
  3. At each step k, the move produces the correct next shadow config

For (2) and (3): we need q to be locally safe at step k (so the flip at q
doesn't affect p_k's context (L,S,R)).

BUT: we can use a STEP-DEPENDENT flip! Instead of flipping q to the SAME
value v₁ at every step, we can define:

  shadow(k) = flipConfig(configs[k], q, v(k))

where v(k) changes across steps. This works if:
  - v(k) ≠ configs[k](q) for all k (so shadow ∉ good)
  - At each step k where q IS NOT in {p_k, left(p_k), right(p_k)}:
    the flip is invisible, so privilege and move are preserved
  - At each step k where q IS in {p_k, left(p_k), right(p_k)}:
    we need v(k) to be chosen so privilege is preserved

The question: can we always choose v(k) at the "problematic" steps?

KEY INSIGHT: A processor q with m_q >= 3 has at least 3 values.
At step k, configs[k](q) is one value. The mover p_k might need q
to have a specific value for privilege. But there are m_q - 1 >= 2
alternative values for q. If the privilege condition only constrains
q to avoid ONE specific value, we can always find a valid v(k).

Hmm, this doesn't quite work because the shadow must be a CYCLE
(shadow(k) -> shadow(k+1) via the same move). The step-dependent
flip breaks the cycle structure.

ALTERNATIVE APPROACH: "Binary Processor Flip"

If q is a BINARY processor (m_q = 2), flipping q means changing
0 <-> 1. The shadow value is always 1 - configs[k](q).

For binary q: at steps where q is far from the mover, the flip
is invisible. At steps where q IS near the mover, flipping q
changes the mover's context by toggling one of L, S, or R.

Sub-threshold => >=3 binary. Pick one binary processor q.
The mover word visits q's neighborhood at some steps. At other
steps, q is far.

For the flip to work: we need the mover to remain privileged when
q is flipped. This means: at steps where q is in the mover's
neighborhood, f_p(L', S, R') ≠ S' must still hold (where primes
indicate the flipped values).

ACTUALLY: The existing proof uses the crucial fact that
  shadow(k) ∉ gc.configs

This requires q's value to be DIFFERENT from its value in every
config that matches the rest. The existing proof shows:
  - If q never fires: q has constant value v₀ throughout the cycle
  - Flipping to v₁ ≠ v₀ ensures shadow ∉ good

For a non-safe processor q: q might fire (moverAt = q at some step).
When q fires, q's value changes. So q doesn't have a constant value.

But we can still argue: if we flip q to 1-q's_value at each step,
the shadow configs are ALL different from the good configs at position q.
But the shadow configs might COINCIDE with OTHER good configs (where
q happens to have value 1-v).

Hmm, this is the "shadow ∉ good" condition failing.

WAIT: The existing proof's "shadow ∉ good" argument relies on:
  - q has constant value v₀ in ALL good configs
  - Shadow has q = v₁ ≠ v₀
  - So shadow ≠ any good config

For a non-safe processor q that fires: q's value varies across configs.
Flipping q at config k gives q-value 1-configs[k](q). This might equal
configs[j](q) for some other j. So the shadow at step k could equal
the good config at step j (if all other positions match).

But good configs are DISTINCT. If shadow(k) = good(j), then:
  - All non-q positions of shadow(k) = configs[k] (same)
  - shadow(k)(q) = 1 - configs[k](q) = configs[j](q)

For this to hold, configs[k] and configs[j] must agree on ALL positions
except q, where configs[j](q) = 1 - configs[k](q).

This means: configs[k] and configs[j] are "q-neighbors" (differ only at q,
by a binary flip). If no two good configs are q-neighbors, then
shadow(k) ∉ good for all k.

LEMMA NEEDED: In a sub-threshold good cycle with >= 3 binary,
there exists a binary processor q such that no two configs in the
good cycle are q-neighbors.

Is this true? Let's check computationally.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict
import time


def build_cup2(n):
    """Build CUP-2 system."""
    T_bot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
             (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    T_low = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
             (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
             (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    T_mid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
             (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
             (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
             (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
             (2,2,0):0,(2,2,1):2,(2,2,2):2}
    T_high = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
              (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
              (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    T_top = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
             (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
             (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    ms = [2]+[3]*(n-2)+[2]
    def mf(t): return lambda L,S,R: t[(L,S,R)]
    if n==4: fs=[mf(T_bot),mf(T_low),mf(T_high),mf(T_top)]
    elif n==5: fs=[mf(T_bot),mf(T_low),mf(T_mid),mf(T_high),mf(T_top)]
    else: fs=[mf(T_bot),mf(T_low)]+[mf(T_mid)]*(n-4)+[mf(T_high),mf(T_top)]
    return ms, fs


def find_cycle(ms, fs, n):
    """Find the good cycle."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    sp = {}
    for c in all_configs:
        priv = [i for i in range(n) if fs[i](c[(i-1)%n],c[i],c[(i+1)%n]) != c[i]]
        if len(priv) == 1:
            sp[c] = priv[0]
    succ = {}
    for c, m in sp.items():
        lst=list(c); lst[m]=fs[m](c[(m-1)%n],c[m],c[(m+1)%n])
        succ[c]=(tuple(lst),m)
    closed=set(sp.keys()); changed=True
    while changed:
        changed=False
        rm={c for c in closed if succ[c][0] not in closed}
        if rm: closed-=rm; changed=True
    vis=set()
    for c in closed:
        if c in vis: continue
        path=[]; node=c; ps=set()
        while node not in vis and node not in ps:
            path.append(node); ps.add(node); node=succ[node][0]
        if node in ps:
            idx=path.index(node); return path[idx:], succ
        vis.update(path)
    return None, None


def check_q_neighbors(cycle, n, q):
    """Check if any two configs in the cycle are q-neighbors
    (differ only at position q, by exactly a binary flip)."""
    cycle_set = set(cycle)
    for c in cycle:
        # Flip q
        lst = list(c)
        lst[q] = 1 - lst[q]
        flipped = tuple(lst)
        if flipped in cycle_set:
            return True, c, flipped
    return False, None, None


def check_privilege_preserved(cycle, succ, ms, fs, n, q):
    """Check if flipping q preserves privilege at every step."""
    L = len(cycle)
    for i in range(L):
        c = cycle[i]
        mover = succ[c][1]
        p = mover

        # Is q in mover's neighborhood?
        near = (q == p or q == (p-1)%n or q == (p+1)%n)

        if near:
            # Flip q in config c
            shadow_c = list(c)
            shadow_c[q] = 1 - shadow_c[q]  # binary flip

            # Check if mover is still privileged in shadow
            L_val = shadow_c[(p-1)%n]
            S_val = shadow_c[p]
            R_val = shadow_c[(p+1)%n]

            if fs[p](L_val, S_val, R_val) == S_val:
                return False, i, p, q  # privilege lost

            # Check if the move produces the right next shadow config
            next_c = cycle[(i+1) % L]
            shadow_next = list(next_c)
            shadow_next[q] = 1 - shadow_next[q]

            # Apply move to shadow_c
            moved = list(shadow_c)
            moved[p] = fs[p](L_val, S_val, R_val)

            if tuple(moved) != tuple(shadow_next):
                return False, i, p, q  # move doesn't match

    return True, None, None, None


def check_non_good_shadow(cycle, succ, ms, fs, n, q):
    """Check if shadow configs are not in the good set."""
    # The good set includes the cycle + tails
    # For simplicity, check against cycle configs + all single-priv configs
    all_configs = list(cartesian(*(range(m) for m in ms)))
    sp = set()
    for c in all_configs:
        priv = [i for i in range(n) if fs[i](c[(i-1)%n],c[i],c[(i+1)%n]) != c[i]]
        if len(priv) == 1:
            sp.add(c)

    # Build good set (closed under successor)
    succ_map = {}
    for c in sp:
        p = [i for i in range(n) if fs[i](c[(i-1)%n],c[i],c[(i+1)%n]) != c[i]][0]
        lst=list(c); lst[p]=fs[p](c[(p-1)%n],c[p],c[(p+1)%n])
        succ_map[c]=tuple(lst)

    good = set(sp)
    changed = True
    while changed:
        changed = False
        rm = {c for c in good if succ_map.get(c) not in good}
        if rm: good -= rm; changed = True

    # Check shadow configs
    for c in cycle:
        shadow = list(c)
        shadow[q] = 1 - shadow[q]
        if tuple(shadow) in good:
            return False, c, tuple(shadow)

    return True, None, None


def main():
    print("=" * 80)
    print("SHADOW EXTENSION: Flipping binary processors in non-safe cases")
    print("=" * 80)

    for n in range(5, 12):
        ms, fs = build_cup2(n)
        product = 1
        for m in ms: product *= m
        threshold = 4 * 3**(n-2)

        cycle, succ = find_cycle(ms, fs, n)
        if not cycle:
            print(f"n={n}: no cycle found")
            continue

        L = len(cycle)
        movers = [succ[c][1] for c in cycle]

        # Binary processors
        binary_procs = [p for p in range(n) if ms[p] == 2]

        print(f"\nn={n}: L={L}, binary_procs={binary_procs}")

        for q in binary_procs:
            # Check q-neighbor condition
            has_qn, c1, c2 = check_q_neighbors(cycle, n, q)

            # Check if q is near any mover
            near_steps = [i for i in range(L)
                         if q == movers[i] or q == (movers[i]-1)%n or q == (movers[i]+1)%n]

            # Check privilege preservation
            priv_ok, fail_step, fail_mover, fail_q = check_privilege_preserved(
                cycle, succ, ms, fs, n, q)

            # Check non-good shadow
            nongood_ok, fail_c, fail_shadow = check_non_good_shadow(
                cycle, succ, ms, fs, n, q)

            print(f"  q={q}: q-neighbors={has_qn}, near_steps={len(near_steps)}/{L}, "
                  f"priv_preserved={priv_ok}, shadow_nongood={nongood_ok}")

            if not has_qn and priv_ok and nongood_ok:
                print(f"    *** SHADOW WORKS for q={q}! ***")
            elif has_qn:
                print(f"    q-neighbor found: {c1} <-> {c2}")
            elif not priv_ok:
                print(f"    Privilege fails at step {fail_step}, mover={fail_mover}")
            elif not nongood_ok:
                print(f"    Shadow in good: {fail_c} -> {fail_shadow}")

    # Now let's try something different: for each step, find ALL processors
    # where flipping preserves privilege AND the shadow stays non-good
    print("\n" + "=" * 80)
    print("PER-STEP ANALYSIS: Which processors can be flipped at each step?")
    print("=" * 80)

    for n in [5, 6, 7, 8]:
        ms, fs = build_cup2(n)
        cycle, succ = find_cycle(ms, fs, n)
        if not cycle: continue
        L = len(cycle)
        movers = [succ[c][1] for c in cycle]

        print(f"\nn={n}: L={L}")
        for i in range(L):
            c = cycle[i]
            p = movers[i]
            safe_at_step = []
            for q in range(n):
                if q == p or q == (p-1)%n or q == (p+1)%n:
                    continue
                safe_at_step.append(q)
            print(f"  Step {i:2d}: mover={p}, safe_procs={safe_at_step}")

        # Find intersection of safe sets
        all_safe = set(range(n))
        for i in range(L):
            p = movers[i]
            step_safe = {q for q in range(n)
                        if q != p and q != (p-1)%n and q != (p+1)%n}
            all_safe &= step_safe

        print(f"  Globally safe: {all_safe}")
        if not all_safe:
            print(f"  => No globally safe processor (expected for large-arc)")

        # For the non-safe case: check if there exists q that is safe
        # at all CRITICAL steps (where the flip would change something)
        # Key insight: the flip only matters when q is in the mover's
        # neighborhood. At those steps, we need privilege to be preserved.
        # At other steps, the flip is invisible.

        # For binary q: flip means q -> 1-q. The mover's context changes.
        # The mover may or may not remain privileged.

        # Count how many steps each processor is "near" a mover
        binary_procs = [p for p in range(n) if ms[p] == 2]
        print(f"\n  Near-mover step counts for binary processors:")
        for q in binary_procs:
            near = sum(1 for i in range(L)
                      if q == movers[i] or q == (movers[i]-1)%n or q == (movers[i]+1)%n)
            print(f"    q={q}: near {near}/{L} steps")


if __name__ == "__main__":
    main()
