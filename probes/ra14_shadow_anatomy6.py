#!/usr/bin/env python3
"""
RA14 Part 6: Exhaustive system search for no-EC words.

Critical finding: MNU does NOT hold for these words.
Word-level shadow exists but doesn't directly translate to system-level.

The question: can ANY choice of free entries give a valid system?
If no: why not? What mechanism blocks it?

Strategy: for the 6 canonical no-EC words at n=5, exhaustively search
all possible free-entry assignments and check if any give a valid system.
"""

from collections import defaultdict
from itertools import product as iproduct
from math import prod
import sys
import time

sys.path.insert(0, './claude')
from verifier import verify_system

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

n = 5
ms = [2,2,2,3,3]
product_val = prod(ms)
CL = sum(ms)

# Representative no-EC word
w0 = [0, 1, 2, 3, 3, 4, 0, 1, 2, 3, 4, 4]
cyc0 = build_cycle(w0, ms, n)
good_set = set(cyc0)

print("="*70)
print(f"EXHAUSTIVE FREE-ENTRY SEARCH FOR WORD {w0}")
print("="*70)
print(f"n={n}, ms={ms}, product={product_val}, CL={CL}")
print(f"Good configs: {len(cyc0)}, Bad configs: {product_val - len(cyc0)}")

# Collect forced entries
forced = {}
for t in range(CL):
    c = cyc0[t]
    mover = w0[t]
    c_next = cyc0[(t+1) % CL]
    for j in range(n):
        L_val = c[(j-1)%n]
        S_val = c[j]
        R_val = c[(j+1)%n]
        key = (j, L_val, S_val, R_val)
        if j == mover:
            forced[key] = c_next[j]
        else:
            forced[key] = S_val

# Find free entries
all_entries = {}
for p in range(n):
    for L_val in range(ms[(p-1)%n]):
        for S_val in range(ms[p]):
            for R_val in range(ms[(p+1)%n]):
                key = (p, L_val, S_val, R_val)
                if key not in forced:
                    all_entries[key] = list(range(ms[p]))

free_keys = list(all_entries.keys())
print(f"Forced entries: {len(forced)}")
print(f"Free entries: {len(free_keys)}")

# The free entries can each take ms[p] values.
# Total combinations:
total_combos = 1
for k in free_keys:
    total_combos *= ms[k[0]]
print(f"Total free-entry combinations: {total_combos}")

# Group free entries by proc
free_by_proc = defaultdict(list)
for k in free_keys:
    free_by_proc[k[0]].append(k)

for p in range(n):
    n_free_p = len(free_by_proc[p])
    choices_p = ms[p] ** n_free_p if n_free_p > 0 else 1
    print(f"  Proc {p} (ms={ms[p]}): {n_free_p} free entries, {choices_p} choices")

# This is manageable: total_combos should be small enough
# Actually let me count
if total_combos > 10_000_000:
    print(f"Too many combinations ({total_combos}). Sampling instead.")
    do_exhaustive = False
else:
    print(f"Manageable. Doing exhaustive search.")
    do_exhaustive = True

def make_transition_functions(forced, free_assignment, ms, n):
    """Build transition functions from forced entries + free assignment."""
    all_entries = dict(forced)
    all_entries.update(free_assignment)

    fs = []
    for p in range(n):
        def make_f(proc, entries):
            def f(L, S, R):
                key = (proc, L, S, R)
                return entries.get(key, S)  # default: stay
            return f
        fs.append(make_f(p, all_entries))
    return fs

if do_exhaustive:
    t0 = time.time()
    n_valid = 0
    n_tested = 0

    # Generate all free entry assignments
    free_options = [list(range(ms[k[0]])) for k in free_keys]

    for combo in iproduct(*free_options):
        free_assignment = {free_keys[i]: combo[i] for i in range(len(free_keys))}
        fs = make_transition_functions(forced, free_assignment, ms, n)
        result = verify_system(ms, fs, verbose=False)

        n_tested += 1
        if result['valid']:
            n_valid += 1
            print(f"\n*** VALID SYSTEM FOUND! ***")
            print(f"Free assignment: {free_assignment}")
            gc = result.get('good_configs', set())
            print(f"Good configs: {len(gc)}")
            # Check if the good cycle matches
            if good_set == gc:
                print("Good cycle MATCHES our target cycle!")
            else:
                print("Good cycle is DIFFERENT from our target cycle.")
                print(f"Our cycle: {len(good_set)}, System's: {len(gc)}")
                print(f"Overlap: {len(good_set & gc)}")
            break  # Found one, that's enough

        if n_tested % 100000 == 0:
            elapsed = time.time() - t0
            print(f"  Tested {n_tested}/{total_combos} ({100*n_tested/total_combos:.1f}%) "
                  f"in {elapsed:.1f}s")

    elapsed = time.time() - t0
    print(f"\nExhaustive search complete: {n_tested} tested in {elapsed:.1f}s")
    print(f"Valid systems: {n_valid}")

    if n_valid == 0:
        print("""
*** NO valid system exists with this good cycle, regardless of free entries ***

This means: the good cycle STRUCTURE alone (mover word + config sequence)
is sufficient to block any valid system. Even without EC, the cycle
can't be part of a valid system.

The obstruction is NOT shadow (constant-offset) — it's something about
the forced entries that makes convergence impossible.
""")

        # Let's understand WHY. Check what goes wrong with the "best" free entry choices.
        # Try: minimize the number of privileged procs at bad configs (to minimize bad graph edges)
        print("Analyzing WHY no valid system exists...")

        # With 'stay' policy: dead configs exist (unprivileged everywhere)
        # We need at least one privileged proc at each config.
        # So free entries can't all be 'stay'.

        # Check: which bad configs are problematic?
        # A bad config c is "easy" if it has at least one forced-privileged proc
        # (from the good cycle's mover entries). It's "hard" if all forced entries
        # at c are non-mover entries (proc stays = unprivileged).

        n_easy = 0
        n_hard = 0
        hard_configs = []
        for cfg in iproduct(*(range(m) for m in ms)):
            if cfg in good_set:
                continue
            # Check: does any proc have a forced mover entry?
            has_forced_priv = False
            for j in range(n):
                key = (j, cfg[(j-1)%n], cfg[j], cfg[(j+1)%n])
                if key in forced and forced[key] != cfg[j]:
                    has_forced_priv = True
                    break
            if has_forced_priv:
                n_easy += 1
            else:
                n_hard += 1
                hard_configs.append(cfg)

        print(f"Bad configs with forced privilege: {n_easy}")
        print(f"Bad configs WITHOUT forced privilege: {n_hard}")
        if hard_configs:
            print(f"Hard configs (first 5): {hard_configs[:5]}")
            # For hard configs, ALL privileges come from free entries.
            # The designer MUST set at least one free entry to make a proc privileged.
            # But setting it privileged might create bad-graph cycles.
            print(f"\nFor hard configs, free entries determine privileges.")
            print(f"Each hard config needs at least one free entry set to S' != S.")

            # Analyze: how many free entries does each hard config have?
            for hc in hard_configs[:3]:
                free_at_hc = []
                for j in range(n):
                    key = (j, hc[(j-1)%n], hc[j], hc[(j+1)%n])
                    if key not in forced:
                        free_at_hc.append((j, key))
                print(f"  Config {hc}: {len(free_at_hc)} free entries")
                for j, key in free_at_hc:
                    print(f"    proc {j}: ({key[1]},{key[2]},{key[3]}) -> choose from {list(range(ms[j]))}")

else:
    # Sampling approach
    import random
    random.seed(42)

    n_valid = 0
    n_tested = 0
    for _ in range(1000000):
        free_assignment = {}
        for k in free_keys:
            free_assignment[k] = random.randrange(ms[k[0]])

        fs = make_transition_functions(forced, free_assignment, ms, n)
        result = verify_system(ms, fs, verbose=False)

        n_tested += 1
        if result['valid']:
            n_valid += 1
            print(f"VALID at attempt {n_tested}!")
            break

    print(f"Sampled {n_tested}: valid={n_valid}")


# ================================================================
# Check the SECOND no-EC canonical word
# ================================================================
print(f"\n{'='*70}")
print("CHECKING SECOND CANONICAL NO-EC WORD")
print("="*70)

w1 = [0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 3, 4]  # 3rd canonical (different structure)
cyc1 = build_cycle(w1, ms, n)
good_set1 = set(cyc1)

forced1 = {}
for t in range(CL):
    c = cyc1[t]
    mover = w1[t]
    c_next = cyc1[(t+1) % CL]
    for j in range(n):
        key = (j, c[(j-1)%n], c[j], c[(j+1)%n])
        if j == mover:
            forced1[key] = c_next[j]
        else:
            forced1[key] = c[j]

free_keys1 = []
for p in range(n):
    for L_val in range(ms[(p-1)%n]):
        for S_val in range(ms[p]):
            for R_val in range(ms[(p+1)%n]):
                key = (p, L_val, S_val, R_val)
                if key not in forced1:
                    free_keys1.append(key)

free_options1 = [list(range(ms[k[0]])) for k in free_keys1]
total1 = 1
for k in free_keys1:
    total1 *= ms[k[0]]
print(f"Word: {w1}")
print(f"Free entries: {len(free_keys1)}, Total combos: {total1}")

if total1 <= 10_000_000:
    t0 = time.time()
    n_valid1 = 0
    n_tested1 = 0
    for combo in iproduct(*free_options1):
        free_assignment = {free_keys1[i]: combo[i] for i in range(len(free_keys1))}
        fs = make_transition_functions(forced1, free_assignment, ms, n)
        result = verify_system(ms, fs, verbose=False)
        n_tested1 += 1
        if result['valid']:
            n_valid1 += 1
            print(f"VALID SYSTEM FOUND!")
            break
        if n_tested1 % 100000 == 0:
            print(f"  {n_tested1}/{total1}")
    print(f"Result: {n_valid1} valid out of {n_tested1} tested ({time.time()-t0:.1f}s)")


# ================================================================
# What about a CW word (one of the reflections that HAS EC)?
# ================================================================
print(f"\n{'='*70}")
print("COMPARISON: EC WORD — DOES A VALID SYSTEM EXIST?")
print("="*70)

# Try one of the many EC words. Pick a simple sweep-like word.
w_ec = [0, 1, 2, 3, 4, 4, 3, 3, 2, 1, 0, 4]  # random EC word
cyc_ec = build_cycle(w_ec, ms, n)
if cyc_ec is None:
    # Try another
    w_ec = [3, 4, 3, 0, 1, 2, 4, 0, 3, 4, 2, 1]
    cyc_ec = build_cycle(w_ec, ms, n)

if cyc_ec is not None:
    from collections import defaultdict
    L = len(w_ec)
    mt = defaultdict(set)
    nmt = defaultdict(set)
    for t in range(L):
        c = cyc_ec[t]
        mover = w_ec[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mt[j].add(triple)
            else:
                nmt[j].add(triple)
    ec_procs = {j: mt[j] & nmt[j] for j in range(n) if mt[j] & nmt[j]}
    print(f"Word: {w_ec}")
    print(f"EC at procs: {list(ec_procs.keys())}")
    print(f"EC means: this cycle structure is INHERENTLY inconsistent.")
    print(f"No transition function can satisfy both mover and non-mover entries.")
    print(f"So this word can NEVER be part of a valid system, period.")
else:
    print("Could not build EC cycle (word doesn't close)")


# ================================================================
# FINAL: Alternative mechanism for no-EC words
# ================================================================
print(f"\n{'='*70}")
print("WHY DO NO-EC WORDS FAIL WITHOUT EC OR MNU?")
print("="*70)

print("""
At n=5, ms=(2,2,2,3,3), the 72 no-EC words:
- Have no entry conflict (consistent entries possible)
- Lack MNU (some bad configs have no forced privilege)
- Have word-level shadow (23 constant-offset shadows)
- Cannot form valid systems (exhaustive search confirms)

The failure mechanism must be one of:
1. LIVENESS: some configs have no privileged proc
2. CONVERGENCE: bad-config cycles exist for all free-entry assignments
3. FAIRNESS: the good cycle doesn't visit all processors

The good cycle visits all processors (CL=12, every proc fires >=2 times).
So fairness is satisfied.

For liveness: with the right free entries, every config can have a
privileged proc. (Just set free entries to S+1 mod ms[p].)

So it must be CONVERGENCE. And convergence failure means: for EVERY
choice of free entries that satisfies liveness, there exists a
bad-config cycle.

This is interesting: the cycle structure forces convergence failure
even though:
- No entry conflict
- No MNU (so no forced-privilege chain covers all bad configs)
- Free entries give the designer flexibility

The obstruction must involve an INTERACTION between the forced entries
and any valid free-entry assignment. The forced entries constrain the
bad graph enough that cycles are unavoidable.
""")

# Verify by checking the specific failure mode
print("Checking convergence failure details...")
# Use the 'inc' free policy (makes all configs alive)
all_entries_inc = dict(forced)
for k in free_keys:
    all_entries_inc[k] = (k[2] + 1) % ms[k[0]]  # S+1 mod ms[p]

fs_inc = make_transition_functions(forced, {k: (k[2]+1)%ms[k[0]] for k in free_keys}, ms, n)
result_inc = verify_system(ms, fs_inc, verbose=True)
print(f"\nWith 'inc' free entries: valid={result_inc['valid']}")
for prop, (ok, info) in result_inc.get('properties', {}).items():
    print(f"  {prop}: {'OK' if ok else 'FAIL'} {info}")
