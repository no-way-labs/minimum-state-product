#!/usr/bin/env python3
"""
RA12 Part 2: CL ≤ 2n via local state projection at binary processors.

KEY IDEA: Consider the "projection" of the config sequence onto a single binary
processor p (m_p = 2). The value at p forms a sequence v_0, v_1, ..., v_{CL-1}.
Between consecutive firings of p, the value is constant.

For binary p with fc(p) = k (even ≥ 2):
  The value alternates: v, v', v, v', ... (k toggles, returning to v).
  There are k "phases": blocks of consecutive configs where p has the same value.
  The k phases alternate between value v and value v'.
  k/2 phases have value v, k/2 have value v'.

In each phase, p doesn't fire. Only other procs fire. The configs within a phase
differ only at non-p positions. The number of distinct configs in a phase equals
the phase length.

Now: the total configs in all v-phases = CL/2 (approximately, if phases have
uniform length). Actually total configs = CL, and exactly CL/2 configs have p=v,
CL/2 have p=v'. Wait, that's not quite right either.

Let me think about this more carefully.

Phase lengths: let L_1, L_2, ..., L_k be the lengths of the k phases.
sum L_i = CL.
In phase i, the mover fires L_i times at positions other than p (plus 0 or 1 times at p).

Wait, the phases are BETWEEN firings of p. So:
- Phase 1: from firing 0 of p to firing 1 of p (exclusive). Length = # steps between.
  This includes the step where p fires at the start.
  Actually, let me define phases carefully.

Let the step indices where p fires be a_0, a_1, ..., a_{k-1} (ordered cyclically).
Phase j: steps a_j, a_j+1, ..., a_{j+1}-1 (mod CL).
Phase j has length a_{j+1} - a_j (mod CL).
In phase j, p fires at step a_j and doesn't fire at steps a_j+1, ..., a_{j+1}-1.

So phase j has length L_j = (a_{j+1} - a_j) mod CL ≥ 1.
sum L_j = CL.

After p fires at step a_j, its value changes.
So in phase j, p has value v_j at steps a_j+1, ..., a_{j+1}-1 (the non-firing steps).
Wait, at step a_j, p fires: its value changes from old to new.
The config AFTER step a_j (= config a_j + 1) has p = new value.
The config AT step a_j has p = old value.
The config AT step a_j+1, a_j+2, ..., a_{j+1}-1 all have p = new value (p doesn't fire).
And at step a_{j+1}, p fires again, changing from new value.

So the value of p:
  Config a_j: p = old
  Config a_j+1: p = new (just fired at step a_j)
  Config a_j+2: p = new (didn't fire at step a_j+1)
  ...
  Config a_{j+1}: p = new (about to fire at step a_{j+1})
  Config a_{j+1}+1: p = toggled from new

Wait, I need to be more careful.

In the good cycle, config[k+1] = fire mover at config[k].
So config[k] is the state BEFORE the mover fires at step k.
The mover at step k is moverAt(k).
config[k+1] differs from config[k] only at moverAt(k).

So if p fires at step a_j (moverAt(a_j) = p):
  config[a_j][p] = some value v
  config[a_j+1][p] = v' ≠ v (p just fired)

For binary (m=2): v' = 1-v.

Between firings of p (steps a_j+1 to a_{j+1}-1, none of which have mover = p):
  config[a_j+1][p] = v'
  config[a_j+2][p] = v' (mover at step a_j+1 is not p, so p unchanged)
  ...
  config[a_{j+1}][p] = v' (mover at step a_{j+1}-1 is not p, so p unchanged)

Then at step a_{j+1}: mover = p, config[a_{j+1}][p] = v', config[a_{j+1}+1][p] = v.

So binary p alternates: v, v', v, v', ...
Phases in terms of p's value:
  Phase j (from config a_j to config a_{j+1}-1): config a_j has p = v_j (before firing)
  But config a_j+1 to config a_{j+1} have p = v_{j+1} = 1-v_j.

Actually, let me define it as: configs where p has value 0 vs value 1.
The v-configs are not contiguous! Let me re-index.

Config a_j has p = v_j.
Config a_j + 1 has p = 1 - v_j.
...
Config a_{j+1} has p = 1 - v_j.
Config a_{j+1} + 1 has p = v_j (after next firing).

Wait no: config a_{j+1} has p = 1 - v_j (same as since last firing of p).
At step a_{j+1}, p fires: config a_{j+1}+1 has p = v_j.

So: configs with p = v_j: {a_j} ∪ {a_{j+1}+1, ..., a_{j+2}} ∪ ...
This gets complicated. Let me just track values directly.

For k = fc(p) (binary, even), the configs split into two groups:
- Group A: configs where p = 0
- Group B: configs where p = 1
|Group A| + |Group B| = CL.

The transition from Group A to Group B happens at each firing of p (value changes).
With fc(p) = k firings, there are k transitions, alternating A→B and B→A.
So |Group A| = |Group B| = CL/2. (Because k is even, equal transitions both ways.)

Wait, that's not exactly right. Let me count more carefully.

Starting at some config where p = 0:
- p = 0 for some steps (non-firing steps + the firing step itself)
- Then p fires: next config has p = 1.
- p = 1 for some steps.
- Then p fires: next config has p = 0.
- etc.

With k firings (k even), there are k/2 blocks where p = 0 and k/2 blocks where p = 1.
The total configs in the p=0 blocks and p=1 blocks need not be equal!

Example: fc(p) = 2. 1 block of p=0, 1 block of p=1.
Block 0 length: L₀ steps (configs with p=0 from just-fired-to-0 until fires-to-1).
Block 1 length: L₁ steps (configs with p=1 from just-fired-to-1 until fires-to-0).
L₀ + L₁ = CL.

For fc(p) = 4: 2 blocks of p=0, 2 blocks of p=1.
L_A + L_B + L_C + L_D = CL where A, C are p=0 blocks, B, D are p=1 blocks.
|Group A| = L_A + L_C, |Group B| = L_B + L_D.

These need not be equal.

OK so this projection approach doesn't immediately give a clean bound.

Let me try a DIFFERENT approach.

KEY OBSERVATION: Sub-threshold product bounds the NUMBER OF DISTINCT CONFIGS.

CL ≤ product(ms) < 4·3^(n-2).

But 4·3^(n-2) >> 2n for n ≥ 9, so this doesn't help.

HOWEVER: we also have binary parity constraints (fc even at binary procs) and
the walk structure. Maybe there's a SHARPER bound on CL.

ACTUALLY, let me reconsider the problem. Maybe the proof DOESN'T need to prove
CL ≤ 2n in general. Maybe it only needs CL = 2n under ALL the hypotheses,
which include sub-threshold + ≥3 binary + n ≥ 9.

The thing is: the existing proof in CaseObstructionsCore.lean is trying to show
allFireCount_eq_2, which then feeds into the palindromic mover word result.

What if instead of proving CL ≤ 2n independently, we prove fc = 2 directly
using a different argument?

Alternative: Prove fc(p) = 2 for binary procs using binary parity + some
collision argument, then use that to get fc = 2 for all procs.

For a binary proc p, fc(p) is even and ≥ 2.
If fc(p) ≥ 4: p fires 4 times. Value toggles 4 times: 0→1→0→1→0.
There exist two firing steps a, b where p changes 0→1 (or 1→0).
At BOTH steps, p has the same value. But the CONTEXTS (L, R) may differ.

This doesn't give a collision without more info about the system.

Let me look at what arguments ARE available in the Lean codebase.
"""

import sys

# Let me look at what happens for ACTUAL valid systems.
# Specifically: does any valid system with sub-threshold product and ≥3 binary
# have a zero-winding good cycle with CL > 2n?

# To test this, I need to enumerate valid systems (or at least their good cycles).
# Let me use the approach from the verifier.

from itertools import product as cprod
from collections import defaultdict

def get_good_configs(n, ms, tables):
    """Get all good configs for a system."""
    ranges = [range(m) for m in ms]
    good = {}
    for c in cprod(*ranges):
        priv = []
        for p in range(n):
            l = c[(p-1) % n]
            s = c[p]
            r = c[(p+1) % n]
            new_s = tables[p][(l, s, r)]
            if new_s != s:
                priv.append(p)
        if len(priv) == 1:
            good[c] = priv[0]
    return good

def find_good_cycle(n, ms, tables):
    """Find the good cycle (if deterministic: follow trajectory from each good config)."""
    good = get_good_configs(n, ms, tables)
    if not good:
        return None

    visited_global = set()
    cycles = []

    for start in good:
        if start in visited_global:
            continue

        path = []
        movers = []
        c = start
        visited = set()

        while True:
            if c not in good:
                break
            if c in visited:
                if c == start:
                    cycles.append((path, movers))
                break
            visited.add(c)
            visited_global.add(c)
            path.append(c)
            p = good[c]
            movers.append(p)

            c_next = list(c)
            l = c[(p-1) % n]
            s = c[p]
            r = c[(p+1) % n]
            c_next[p] = tables[p][(l, s, r)]
            c = tuple(c_next)

    return cycles

def analyze_cycle_detailed(n, configs, movers):
    """Analyze a cycle."""
    L = len(configs)
    fc = [0] * n
    for m in movers:
        fc[m] += 1

    cw = 0
    ccw = 0
    stay = 0
    for i in range(L):
        p_curr = movers[i]
        p_next = movers[(i+1) % L]
        diff = (p_next - p_curr) % n
        if diff == 1:
            cw += 1
        elif diff == n - 1:
            ccw += 1
        elif diff == 0:
            stay += 1
        # else: jump (shouldn't happen with next_mover_is_local)

    zw = (cw == ccw)
    return {'L': L, 'fc': fc, 'cw': cw, 'ccw': ccw, 'stay': stay, 'zw': zw,
            'has_safe': any(f == 0 for f in fc)}

# Use the verifier to check M_5=96 witness and other known systems.
# ms=(2,2,2,3,4) at n=5.

# I'll build systems by trying all possible transition functions.
# For small state spaces only.

def enumerate_systems(n, ms, max_systems=1000):
    """Enumerate valid systems (those with at least one good cycle)."""
    from itertools import product as cprod
    import random

    total_tables = 1
    for p in range(n):
        m = ms[p]
        m_left = ms[(p-1) % n]
        m_right = ms[(p+1) % n]
        n_contexts = m_left * m * m_right
        # Each context maps to one of m values, but must differ from current for privilege
        # Actually the table maps every (l,s,r) to some value in range(m)
        total_tables *= m ** (m_left * m * m_right)

    print(f"  Total possible systems: ~{total_tables:.2e}")

    if total_tables > 1e8:
        print("  Too many to enumerate; sampling instead")
        return sample_systems(n, ms, max_systems)

    # Enumerate all systems... still too many for most cases.
    # Let me just sample.
    return sample_systems(n, ms, max_systems)

def sample_systems(n, ms, num_samples=10000):
    """Sample random systems and find their good cycles."""
    import random

    results = []
    for trial in range(num_samples):
        tables = []
        for p in range(n):
            m = ms[p]
            m_left = ms[(p-1) % n]
            m_right = ms[(p+1) % n]
            t = {}
            for l in range(m_left):
                for s in range(m):
                    for r in range(m_right):
                        t[(l, s, r)] = random.randint(0, m-1)
            tables.append(t)

        cycles = find_good_cycle(n, ms, tables)
        if cycles:
            for path, movers in cycles:
                info = analyze_cycle_detailed(n, path, movers)
                if info['zw'] and not info['has_safe'] and info['cw'] > 0:
                    results.append(info)

    return results

print("="*70)
print("SAMPLING SYSTEMS: n=5, ms=(2,2,2,3,3)")
print("="*70)

import random
random.seed(42)

zw_cycles = sample_systems(5, [2,2,2,3,3], num_samples=50000)
print(f"\nFound {len(zw_cycles)} ZW no-safe cycles with cw > 0")

if zw_cycles:
    from collections import Counter
    length_dist = Counter(c['L'] for c in zw_cycles)
    print(f"Length distribution: {dict(sorted(length_dist.items()))}")

    fc_dist = Counter(tuple(sorted(c['fc'])) for c in zw_cycles)
    print(f"FC distribution (top 10):")
    for fc, cnt in fc_dist.most_common(10):
        print(f"  fc={fc}: {cnt}")

    # Check CL ≤ 2n
    violations = [c for c in zw_cycles if c['L'] > 2*5]
    print(f"\nViolations of CL ≤ 2n: {len(violations)}")
    if violations:
        for v in violations[:5]:
            print(f"  L={v['L']}, fc={v['fc']}, cw={v['cw']}, ccw={v['ccw']}, stay={v['stay']}")

print()
print("="*70)
print("SAMPLING SYSTEMS: n=5, ms=(2,2,2,3,4)")
print("="*70)

zw_cycles2 = sample_systems(5, [2,2,2,3,4], num_samples=50000)
print(f"\nFound {len(zw_cycles2)} ZW no-safe cycles with cw > 0")

if zw_cycles2:
    length_dist = Counter(c['L'] for c in zw_cycles2)
    print(f"Length distribution: {dict(sorted(length_dist.items()))}")

    violations = [c for c in zw_cycles2 if c['L'] > 2*5]
    print(f"Violations of CL ≤ 2n: {len(violations)}")
    if violations:
        for v in violations[:5]:
            print(f"  L={v['L']}, fc={v['fc']}, cw={v['cw']}, ccw={v['ccw']}, stay={v['stay']}")

# Also try n=7
print()
print("="*70)
print("SAMPLING SYSTEMS: n=7, ms=(2,2,2,3,3,3,3)")
print("="*70)

zw_cycles3 = sample_systems(7, [2,2,2,3,3,3,3], num_samples=10000)
print(f"\nFound {len(zw_cycles3)} ZW no-safe cycles with cw > 0")

if zw_cycles3:
    length_dist = Counter(c['L'] for c in zw_cycles3)
    print(f"Length distribution: {dict(sorted(length_dist.items()))}")

    violations = [c for c in zw_cycles3 if c['L'] > 2*7]
    print(f"Violations of CL ≤ 2n: {len(violations)}")
    if violations:
        for v in violations[:5]:
            print(f"  L={v['L']}, fc={v['fc']}, cw={v['cw']}, ccw={v['ccw']}, stay={v['stay']}")

print()
print("="*70)
print("SAMPLING: n=9, ms=(2,2,2,3,3,3,3,3,3)")
print("="*70)

zw_cycles4 = sample_systems(9, [2,2,2,3,3,3,3,3,3], num_samples=5000)
print(f"\nFound {len(zw_cycles4)} ZW no-safe cycles with cw > 0")

if zw_cycles4:
    length_dist = Counter(c['L'] for c in zw_cycles4)
    print(f"Length distribution: {dict(sorted(length_dist.items()))}")

    violations = [c for c in zw_cycles4 if c['L'] > 2*9]
    print(f"Violations of CL ≤ 2n: {len(violations)}")
    if violations:
        for v in violations[:5]:
            print(f"  L={v['L']}, fc={v['fc']}, cw={v['cw']}, ccw={v['ccw']}, stay={v['stay']}")
