#!/usr/bin/env python3
"""
RA14 Part 5: The bridge between word-level and system-level shadow.

Critical finding from Part 4: Word-level shadows have free entries that the
system designer can set. So word-level shadow != system-level shadow.
But none of the 72 no-EC words at n=5 can form valid systems.

The question: WHY can't they form valid systems? Is it:
(a) The word-level shadow entries that ARE forced create conflicts?
(b) Some other mechanism (convergence failure not related to shadow)?
(c) The free entries can't all be set consistently?

Also: for the n=9 bounce-sweep (which HAS MNU), the system-level shadow
IS real because MNU means every non-good config has forced privilege.
So MNU is the bridge from word-level to system-level shadow.

Let's verify: do the 72 no-EC words have MNU?
"""

from collections import defaultdict, Counter
from itertools import product as iproduct
from math import prod
import time

def build_cycle(word, ms, n, trans=None):
    if trans is None:
        trans = [1]*n
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def check_ec(good, word, n):
    L = len(word)
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)
    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts


def check_mnu(good, word, n, ms):
    """Check MNU: every non-good config has at least one proc whose (L,S,R)
    appears as a mover triple in the good cycle."""
    L = len(word)
    mover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        triple = (c[(mover-1)%n], c[mover], c[(mover+1)%n])
        mover_triples[mover].add(triple)

    # Check all non-good configs
    good_set = set(good)
    n_covered = 0
    n_uncovered = 0
    uncovered_examples = []

    for cfg in iproduct(*(range(m) for m in ms)):
        if cfg in good_set:
            continue
        # Does some proc have a mover triple matching this config?
        covered = False
        for j in range(n):
            triple = (cfg[(j-1)%n], cfg[j], cfg[(j+1)%n])
            if triple in mover_triples[j]:
                covered = True
                break
        if covered:
            n_covered += 1
        else:
            n_uncovered += 1
            if len(uncovered_examples) < 3:
                uncovered_examples.append(cfg)

    return n_uncovered == 0, n_covered, n_uncovered, uncovered_examples


n = 5
ms = [2,2,2,3,3]
product_val = prod(ms)
CL = sum(ms)

# Reproduce the 72 no-EC words
base = []
for p in range(n):
    base.extend([p]*ms[p])

def unique_permutations(elements):
    if len(elements) <= 1:
        yield list(elements)
        return
    seen = set()
    for i, e in enumerate(elements):
        if e in seen:
            continue
        seen.add(e)
        rest = elements[:i] + elements[i+1:]
        for perm in unique_permutations(rest):
            yield [e] + perm

# Get canonical representatives (6 groups of 12 rotations)
no_ec_canons = [
    [0, 1, 2, 3, 3, 4, 0, 1, 2, 3, 4, 4],
    [0, 1, 2, 3, 3, 4, 4, 0, 1, 2, 3, 4],
    [0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 3, 4],
    [0, 4, 3, 2, 1, 0, 4, 3, 4, 3, 2, 1],
    [0, 4, 3, 2, 1, 0, 4, 4, 3, 3, 2, 1],
    [0, 4, 3, 3, 2, 1, 0, 4, 4, 3, 2, 1],
]

print("="*70)
print("MNU CHECK FOR NO-EC WORDS AT n=5")
print("="*70)

for wi, w in enumerate(no_ec_canons):
    cyc = build_cycle(w, ms, n)
    if cyc is None:
        print(f"Word {wi} doesn't close!")
        continue

    mnu_ok, n_cov, n_uncov, examples = check_mnu(cyc, w, n, ms)
    print(f"\nWord {wi}: {w}")
    print(f"  MNU: {mnu_ok} (covered={n_cov}, uncovered={n_uncov})")
    if not mnu_ok:
        print(f"  Uncovered examples: {examples[:3]}")

# ================================================================
# KEY TEST: System-level shadow via MNU at n=9
# ================================================================
print(f"\n{'='*70}")
print("SYSTEM-LEVEL SHADOW AT n=9 VIA MNU")
print("="*70)

n9 = 9
ms9 = [2, 3, 3, 2, 3, 3, 2, 3, 3]
product9 = prod(ms9)
word9 = [8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0]

good9 = build_cycle(word9, ms9, n9)
print(f"n=9: word len={len(word9)}, product={product9}")

# Check MNU
mnu_ok9, n_cov9, n_uncov9, ex9 = check_mnu(good9, word9, n9, ms9)
print(f"MNU: {mnu_ok9} (covered={n_cov9}/{product9 - len(good9)}, uncovered={n_uncov9})")

if mnu_ok9:
    print("""
MNU HOLDS for n=9 bounce-sweep!
This means: for EVERY non-good config, at least one proc has a (L,S,R) triple
that appears as a mover triple in the good cycle.
=> That proc is FORCED to be privileged (by the good cycle's entries).
=> Every non-good config has at least one forced privilege.
=> The daemon can always find a forced move.
=> Since forced moves preserve the mover word's pattern, they chain
   into a closed cycle disjoint from the good cycle.
=> This is a SYSTEM-LEVEL shadow (works for ANY transition function
   consistent with the good cycle).
""")

# ================================================================
# CRUCIAL: Does MNU imply convergence failure?
# ================================================================
print(f"{'='*70}")
print("MNU -> CONVERGENCE FAILURE?")
print("="*70)

print("""
MNU alone doesn't directly imply convergence failure. Here's the chain:

1. MNU: every non-good config c has some proc p where (L,S,R) appears
   as a mover triple of p in the good cycle.

2. Since there's no EC (mover triples and non-mover triples are disjoint),
   the entry f_p(L,S,R) at c MUST be a move (since it matches a mover triple,
   and the mover value f_p(L,S,R) != S for mover triples in the good cycle).

   Wait — is this true? The mover triple at the good cycle has f_p(L,S,R) = S'
   where S' != S (that's what makes it a privilege/mover entry). The same
   (L,S,R) at a non-good config c forces f_p(L,S,R) = S' != S.
   So p IS privileged at c.

3. The daemon at c fires SOME privileged proc (not necessarily p).
   The resulting config c' might be good or non-good.
   If good: convergence achieved.
   If non-good: repeat from step 1.

4. For convergence to fail: there must exist an INFINITE path through
   non-good configs. This requires a CYCLE in the non-good graph.

5. MNU doesn't by itself create a cycle. It only says forced privileges exist.
   The daemon might choose DIFFERENT forced moves at different visits to
   the same non-good config, but the transition function is deterministic:
   at each config, the set of privileged procs is fixed.

6. A bad-config cycle requires: some subset of non-good configs where,
   for each config c, there exists a privileged proc p such that firing p
   at c gives another config in the subset.

7. The word-level shadow provides such a cycle: each shadow config has
   the same mover word, so firing the mover gives the next shadow config.
   But the mover at a shadow config is privileged ONLY if the system's
   transition function at that (L,S,R) makes it privileged.

8. With MNU: the mover's (L,S,R) from the mover word IS a mover triple
   from the good cycle. So the system's entry DOES make it privileged.
   And the entry value matches the shadow needs (same S' as in good cycle,
   because the offset shifts both S and S' by the same amount).

   WAIT — does it? Let me check carefully.

   At good config g_t: proc p fires, triple is (L_g, S_g, R_g).
   Entry: f_p(L_g, S_g, R_g) = S'_g != S_g.

   At shadow config s_t = g_t + d (mod ms):
   The mover p has triple (L_g + d_{p-1}, S_g + d_p, R_g + d_{p+1}) mod ms.
   This is a DIFFERENT triple from (L_g, S_g, R_g)!

   So the shadow config's mover triple is NOT the same as the good cycle's.
   MNU says SOME proc at the shadow config matches a good-cycle mover triple,
   but it might not be the word's mover at that step.

   The constant-offset shadow needs the WORD'S mover to fire.
   MNU guarantees SOME proc is privileged, but not necessarily the right one.

   This is the gap between word-level and system-level shadow.
""")

# Let's verify: at n=9, for the shadow cycle, is the word's mover
# the SAME proc that MNU identifies as privileged?

good9_set = set(good9)

# Collect mover triples per proc
mover_triples9 = defaultdict(set)
for t in range(len(word9)):
    c = good9[t]
    mover = word9[t]
    triple = (c[(mover-1)%n9], c[mover], c[(mover+1)%n9])
    mover_triples9[mover].add(triple)

# Find first shadow offset
for d in iproduct(*(range(m) for m in ms9)):
    if all(x == 0 for x in d):
        continue
    shifted = [tuple((good9[t][j] + d[j]) % ms9[j] for j in range(n9)) for t in range(len(good9))]
    if not (set(shifted) & good9_set):
        shadow9 = shifted
        offset9 = d
        break

print(f"\nShadow offset: {offset9}")
print(f"Checking: is the word's mover always MNU-privileged in shadow?")

word_mover_is_mnu = 0
word_mover_not_mnu = 0
other_procs_mnu = []

for t in range(len(shadow9)):
    sc = shadow9[t]
    word_mover = word9[t]

    # Word mover's triple at shadow config
    wm_triple = (sc[(word_mover-1)%n9], sc[word_mover], sc[(word_mover+1)%n9])

    # Is this a mover triple for word_mover in the good cycle?
    if wm_triple in mover_triples9[word_mover]:
        word_mover_is_mnu += 1
    else:
        word_mover_not_mnu += 1
        # Which proc IS MNU-privileged?
        mnu_procs = []
        for j in range(n9):
            triple = (sc[(j-1)%n9], sc[j], sc[(j+1)%n9])
            if triple in mover_triples9[j]:
                mnu_procs.append(j)
        other_procs_mnu.append((t, word_mover, mnu_procs))

print(f"Word mover is MNU-privileged: {word_mover_is_mnu}/{len(shadow9)}")
print(f"Word mover is NOT MNU-privileged: {word_mover_not_mnu}/{len(shadow9)}")

if word_mover_not_mnu > 0:
    print(f"\nExamples where word mover differs from MNU:")
    for t, wm, mnu_ps in other_procs_mnu[:5]:
        print(f"  t={t}: word mover={wm}, MNU procs={mnu_ps}")


# ================================================================
# THE REAL SHADOW MECHANISM AT SYSTEM LEVEL
# ================================================================
print(f"\n{'='*70}")
print("THE REAL SYSTEM-LEVEL SHADOW MECHANISM")
print("="*70)

print("""
The word-level shadow (constant offset) does NOT directly give a system-level
shadow because the offset changes the (L,S,R) triples.

The system-level shadow works differently:
1. Start at any non-good config c.
2. By MNU, some proc p has a mover triple from the good cycle.
3. The system MUST fire p (it's privileged: f_p(L,S,R) = S' != S).
4. After firing p, get a new config c'.
5. c' might or might not be good.
6. If c' is non-good, repeat.

This creates a deterministic path through non-good configs
(deterministic because the daemon chooses p, and the system's f_p is fixed).

But actually: the daemon can choose ANY privileged proc, not just the MNU one.
Multiple procs might be privileged at a non-good config.
The daemon's choice determines the path.

For convergence failure: we need a cycle that the daemon CAN follow,
not that the daemon MUST follow.

Key insight: if there exists a non-good cycle where at each step,
SOME privileged proc fires and the next config is also in the cycle,
then convergence fails (the daemon can choose that proc).

The word-level shadow provides exactly such a cycle IF the word's movers
are privileged at the shadow configs. But we just showed they're NOT
always the MNU-privileged procs.

However, the word's mover might still be privileged via a DIFFERENT
mechanism: maybe the system has OTHER entries (free entries) that make
the word's mover privileged at the shadow config.

Or: the word-level shadow might not be the right cycle.
The system-level cycle might be DIFFERENT from the word-level offset orbit.
""")

# Let's build an actual system from the n=9 no-EC good cycle and
# check if convergence actually fails.
# The good cycle determines forced entries. Free entries are up to the designer.

import sys
sys.path.insert(0, './claude')
from verifier import verify_system

def build_n9_system(good, word, ms, n, free_policy='inc'):
    """Build system from good cycle + free entry policy."""
    entries = {}
    for t in range(len(word)):
        c = good[t]
        mover = word[t]
        c_next = good[(t+1) % len(word)]
        for j in range(n):
            L_val = c[(j-1)%n]
            S_val = c[j]
            R_val = c[(j+1)%n]
            key = (j, L_val, S_val, R_val)
            if j == mover:
                entries[key] = c_next[j]
            else:
                entries[key] = S_val

    fs = []
    for p in range(n):
        def make_f(proc, entries, ms, fp=free_policy):
            def f(L, S, R):
                key = (proc, L, S, R)
                if key in entries:
                    return entries[key]
                if fp == 'inc':
                    return (S + 1) % ms[proc]
                elif fp == 'dec':
                    return (S - 1) % ms[proc]
                else:
                    return S  # stay
            return f
        fs.append(make_f(p, entries, ms))
    return fs, entries

# Note: n=9 system is too large for verify_system (5832 configs, bad-graph cycle check)
# Let's just check the forced entries count and shadow entry overlap

print(f"\nn=9 system analysis:")
fs9, entries9 = build_n9_system(good9, word9, ms9, n9, 'inc')
print(f"Forced entries: {len(entries9)}")

# Total possible entries
total_entries = sum(ms9[(p-1)%n9] * ms9[p] * ms9[(p+1)%n9] for p in range(n9))
print(f"Total possible entries: {total_entries}")
print(f"Free entries: {total_entries - len(entries9)}")
print(f"Forced fraction: {len(entries9)/total_entries:.1%}")

# Now check: of the shadow configs, how many have the word mover's entry forced?
# And does the forced entry make the mover privileged?
print(f"\nShadow configs: word mover entry analysis")
n_forced_priv = 0  # word mover's entry is forced AND it's a privilege
n_forced_nopriv = 0  # forced but not privilege
n_free = 0

for t in range(len(shadow9)):
    sc = shadow9[t]
    wm = word9[t]
    L_val = sc[(wm-1)%n9]
    S_val = sc[wm]
    R_val = sc[(wm+1)%n9]
    key = (wm, L_val, S_val, R_val)

    if key in entries9:
        val = entries9[key]
        if val != S_val:
            n_forced_priv += 1
        else:
            n_forced_nopriv += 1
    else:
        n_free += 1

print(f"Word mover forced+privileged: {n_forced_priv}")
print(f"Word mover forced+unprivileged: {n_forced_nopriv}")
print(f"Word mover free: {n_free}")

# Even if word mover is unprivileged, some OTHER proc might be privileged
# Check: at shadow configs with unprivileged word mover, what's the total privilege count?
for t in range(len(shadow9)):
    sc = shadow9[t]
    wm = word9[t]
    L_val = sc[(wm-1)%n9]
    S_val = sc[wm]
    R_val = sc[(wm+1)%n9]
    key = (wm, L_val, S_val, R_val)

    if key in entries9 and entries9[key] == S_val:
        # Word mover is unprivileged. Count other privileged procs.
        priv_procs = []
        for j in range(n9):
            L_j = sc[(j-1)%n9]
            S_j = sc[j]
            R_j = sc[(j+1)%n9]
            key_j = (j, L_j, S_j, R_j)
            if key_j in entries9:
                if entries9[key_j] != S_j:
                    priv_procs.append(j)
            else:
                # Free entry: depends on free_policy
                if (S_j + 1) % ms9[j] != S_j:  # inc policy: always privileged
                    priv_procs.append(j)
        if t < 3:
            print(f"  t={t}: word mover {wm} unprivileged, other privileged: {priv_procs}")


# ================================================================
# SYNTHESIS: The real picture
# ================================================================
print(f"\n{'='*70}")
print("SYNTHESIS: THE COMPLETE PICTURE")
print("="*70)
print(f"""
WORD-LEVEL SHADOW (constant offset):
  - Works for inc/dec transitions (algebraic group structure)
  - ALL orbits are isomorphic (constant-offset copies)
  - Shadow exists iff |G-G| < product(ms)
  - For n >= 7 with min fire counts: CL^2 < product, so GUARANTEED
  - For n=5,6: can fail (but in practice always has shadow or EC)

SYSTEM-LEVEL SHADOW (MNU + forced privilege):
  - Works for GENERAL transition functions
  - Requires MNU: every non-good config has a mover-triple-matching proc
  - That proc is forced privileged (same entry as in good cycle)
  - Creates forced-privilege chains through non-good configs
  - These chains must close (finite config space) into cycles
  - But: the daemon chooses which privileged proc to fire
  - The forced-privilege chain is one POSSIBLE daemon path, not the only one

GAP BETWEEN THE TWO:
  - Word-level shadow identifies specific config cycles
  - System-level shadow guarantees some forced-privilege structure
  - They are DIFFERENT mechanisms!
  - Word-level shadow is about orbit structure (algebra)
  - System-level shadow is about entry forcing (combinatorics)

CAN SHADOW ALONE PROVE THE LB?
  For inc/dec systems: YES (for n >= 7, via counting)
  For general systems: REQUIRES MNU (which doesn't always hold)

  At n=5,6: EC covers essentially everything (99.99%+ of words)
  At n >= 7: Either approach works:
    (a) Word-level shadow via counting (CL^2 < product)
    (b) EC via the existing multi-mechanism proof

THE REAL SIMPLIFICATION OPPORTUNITY:
  The existing proof uses many specialized mechanisms:
  - Shadow Mirror Theorem (waterfall cycles)
  - Wiggle Shadow (single-wiggle words)
  - Palindromic EC (consecutive binary, non-sweep fc=2)
  - Universal EC (non-adjacent binary)
  - Various case analyses

  COULD be replaced by:
  For n >= 7: ONE theorem: "CL^2 < product => word-level shadow exists
    => no valid system with this good cycle"
  For n = 5, 6: Exhaustive verification (finite case check)

  BUT: the bridge lemma "word-level shadow => no valid system" needs proof.
  The complication: word-level shadow has free entries that the designer
  can set. Need to show that no free-entry assignment can simultaneously:
  (a) satisfy liveness (all configs have >= 1 privileged proc)
  (b) avoid bad-config cycles

  This bridge is the hard part. MNU provides one path (system-level forcing).
  But MNU doesn't always hold for general systems.

FINAL ANSWER:
  Shadow generalizes beyond WaterfallCycles: YES (constant-offset mechanism).
  Shadow alone proves the LB: PARTIALLY.
    - For n >= 7 with inc/dec: YES (pure counting)
    - For n = 5, 6: NO (need EC as backup)
    - For general transitions: NO (need MNU or EC)

  Practical simplification:
    - n >= 7: CL^2 < product gives word-level shadow for ALL mover words
    - n = 5, 6: can be handled as finite cases
    - The multi-mechanism machinery is only needed for the bridge lemma
      and the small-n cases
""")
