#!/usr/bin/env python3
"""
RA14: Anatomy of non-waterfall shadow cycles.

Investigates whether shadow cycle construction generalizes beyond WaterfallCycles.

Part 1: Anatomy of bounce-sweep shadows at n=9
Part 2: Shadow cycle statistics (lengths, structure)
Part 3: Test at smaller n (valid systems, M_5=96 witness)
Part 4: Generalization analysis
Part 5: Minimal EC assessment
"""

from collections import defaultdict, Counter
from itertools import product as iproduct
from math import prod
import time

# ================================================================
# CORE INFRASTRUCTURE
# ================================================================

def check_ec(good, word, n):
    """Check entry conflict: mover triple == nonmover triple at some proc."""
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


def check_mnu(good, word, n):
    """Check MNU: no mover triple appears as nonmover triple at same proc.
    Returns (has_mnu: bool, details)."""
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
    # MNU: for each proc, mover triples and nonmover triples are disjoint
    violations = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            violations[j] = overlap
    return len(violations) == 0, violations


def build_cycle_from_word(word, ms, n, trans_mode=None):
    """Build cycle from mover word, starting at all-zeros.
    trans_mode[p] = increment amount for proc p (default all +1)."""
    if trans_mode is None:
        trans_mode = [1]*n
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_mode[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def find_all_cycles(word, ms, n, trans_mode=None):
    """Find ALL cycles of a given word under given transitions.
    Returns list of (cycle_configs_list, is_good_set)."""
    if trans_mode is None:
        trans_mode = [1]*n
    L = len(word)
    visited = set()
    cycles = []
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in visited:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + trans_mode[p]) % ms[p]
            configs.append(c)
        if tuple(configs[-1]) != tuple(configs[0]):
            continue
        cycle_configs = [tuple(c) for c in configs[:L]]
        cycle_set = set(cycle_configs)
        if len(cycle_set) == L:
            cycles.append(cycle_configs)
            visited |= cycle_set
    return cycles


def find_shadow_cycles(good_cycle, all_cycles):
    """Find cycles disjoint from good_cycle among all_cycles."""
    good_set = set(good_cycle)
    return [c for c in all_cycles if not (set(c) & good_set)]


def config_diff(c1, c2, n):
    """Return positions where configs differ."""
    return [j for j in range(n) if c1[j] != c2[j]]


def describe_transformation(good_cycle, shadow_cycle, n, ms):
    """Try to describe the transformation from good to shadow configs."""
    L = len(good_cycle)
    if len(shadow_cycle) != L:
        return f"Different lengths: good={L}, shadow={len(shadow_cycle)}"

    # Try: is shadow = good + constant offset (mod ms)?
    for offset_candidate in iproduct(*(range(m) for m in ms)):
        if all(offset_candidate[j] == 0 for j in range(n)):
            continue
        match = True
        for i in range(L):
            expected = tuple((good_cycle[i][j] + offset_candidate[j]) % ms[j] for j in range(n))
            if expected != shadow_cycle[i]:
                match = False
                break
        if match:
            return f"Constant offset: {offset_candidate}"

    # Try: is shadow a PERMUTATION of good + offset?
    shadow_set = set(shadow_cycle)
    for offset_candidate in iproduct(*(range(m) for m in ms)):
        if all(offset_candidate[j] == 0 for j in range(n)):
            continue
        shifted_good = set(tuple((g[j] + offset_candidate[j]) % ms[j] for j in range(n)) for g in good_cycle)
        if shifted_good == shadow_set:
            return f"Set-level constant offset: {offset_candidate}"

    return "No simple constant offset found"


# ================================================================
# PART 1: ANATOMY OF BOUNCE-SWEEP SHADOWS AT n=9
# ================================================================
print("="*70)
print("PART 1: ANATOMY OF NON-WATERFALL SHADOWS AT n=9")
print("="*70)

n = 9
ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
product_val = prod(ms)
threshold = 4 * 3**(n-2)
print(f"n={n}, ms={ms}, product={product_val}, threshold={threshold}")
print(f"Sub-threshold: {product_val < threshold}")

# Build the bounce-sweep word (from ra13)
def find_balanced_segment_words(seg_len, target=2):
    total = seg_len * target
    results = []
    def dfs(word, fc):
        if len(word) == total:
            if all(fc[i] == target for i in range(seg_len)):
                results.append(list(word))
            return
        last = word[-1]
        for nxt in [last-1, last+1]:
            if 0 <= nxt < seg_len and fc[nxt] < target:
                word.append(nxt)
                fc[nxt] += 1
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(seg_len):
        fc = [0]*seg_len
        fc[start] = 1
        dfs([start], fc)
    return results

k = 3
seg_words = find_balanced_segment_words(k-1, target=2)
seg_A = list(range(n-1, 2*k, -1))
seg_B = list(range(2*k-1, k, -1))
seg_C = list(range(k-1, 0, -1))

sw = seg_words[0]
bounce_A = [seg_A[i] for i in sw]
bounce_B = [seg_B[i] for i in sw]
bounce_C = [seg_C[i] for i in sw]

word = []
word.extend(bounce_A)
word.append(2*k)
word.extend(bounce_B)
word.append(k)
word.extend(bounce_C)
word.append(0)
word.extend(list(range(n-1, -1, -1)))
CL = len(word)

print(f"Bounce-sweep word: {word}")
print(f"Cycle length: {CL}")

# Fire counts
fc = Counter(word)
print(f"Fire counts: {dict(sorted(fc.items()))}")
print(f"Binary procs (ms=2) fire: {[fc[i] for i in range(n) if ms[i]==2]}")
print(f"Ternary procs (ms=3) fire: {[fc[i] for i in range(n) if ms[i]==3]}")

# Build good cycle with all-incrementing
trans_inc = [1]*n
good = build_cycle_from_word(word, ms, n, trans_inc)
if good is None:
    print("ERROR: word does not produce valid cycle with all-inc")
else:
    print(f"\nGood cycle built, {len(good)} configs")
    ec = check_ec(good, word, n)
    print(f"Entry conflict: {bool(ec)}")
    has_mnu, mnu_violations = check_mnu(good, word, n)
    print(f"MNU: {has_mnu}")
    if not has_mnu:
        print(f"  MNU violations at procs: {list(mnu_violations.keys())}")
        for p, overlaps in mnu_violations.items():
            print(f"    proc {p} (ms={ms[p]}): {len(overlaps)} overlapping triples")

    # Find ALL cycles
    print(f"\nFinding all cycles under word + incrementing...")
    t0 = time.time()
    all_cyc = find_all_cycles(word, ms, n, trans_inc)
    t1 = time.time()
    print(f"Found {len(all_cyc)} total cycles in {t1-t0:.1f}s")

    shadows = find_shadow_cycles(good, all_cyc)
    print(f"Shadow cycles (disjoint from good): {len(shadows)}")

    if shadows:
        # Analyze first few shadows
        print(f"\n--- Detailed shadow analysis ---")

        # Shadow lengths
        shadow_lens = Counter(len(s) for s in shadows)
        print(f"Shadow lengths: {dict(shadow_lens)}")

        # How many configs are covered?
        all_shadow_configs = set()
        for s in shadows:
            all_shadow_configs |= set(s)
        print(f"Total shadow configs: {len(all_shadow_configs)}")
        print(f"Good + shadow: {len(good) + len(all_shadow_configs)} / {product_val}")

        # Look at first shadow in detail
        s0 = shadows[0]
        print(f"\n--- First shadow cycle (len={len(s0)}) ---")
        print(f"Good cycle configs (first 5):")
        for i in range(min(5, len(good))):
            print(f"  g[{i}]: {good[i]}")
        print(f"Shadow cycle configs (first 5):")
        for i in range(min(5, len(s0))):
            print(f"  s[{i}]: {s0[i]}")

        # Try to find transformation
        print(f"\nTransformation analysis:")
        result = describe_transformation(good, s0, n, ms)
        print(f"  {result}")

        # Check: are shadows related to each other?
        if len(shadows) >= 2:
            print(f"\nInter-shadow relationships:")
            result2 = describe_transformation(shadows[0], shadows[1], n, ms)
            print(f"  Shadow 0 -> Shadow 1: {result2}")
            if len(shadows) >= 3:
                result3 = describe_transformation(shadows[0], shadows[2], n, ms)
                print(f"  Shadow 0 -> Shadow 2: {result3}")

        # Check: per-position differences between good and each shadow
        print(f"\n--- Position-wise analysis ---")
        # For each shadow, compute diff at each position from nearest good config
        s0_set = set(s0)
        # Simple: for each shadow config, find the good config that differs minimally
        min_diffs = []
        for sc in s0[:5]:
            best_diff = n+1
            best_gc = None
            for gc in good:
                d = sum(1 for j in range(n) if gc[j] != sc[j])
                if d < best_diff:
                    best_diff = d
                    best_gc = gc
            min_diffs.append((sc, best_gc, best_diff))
            print(f"  Shadow {sc} closest to good {best_gc} (diff={best_diff})")

        # Check: movers in shadow cycle
        print(f"\n--- Shadow cycle movers ---")
        for si, shadow in enumerate(shadows[:3]):
            movers = []
            for t in range(len(shadow)):
                c1 = shadow[t]
                c2 = shadow[(t+1) % len(shadow)]
                diffs = config_diff(c1, c2, n)
                if len(diffs) == 1:
                    movers.append(diffs[0])
                else:
                    movers.append(f"MULTI:{diffs}")
            print(f"  Shadow {si} movers: {movers}")
            if all(isinstance(m, int) for m in movers):
                print(f"    Same mover word as good? {movers == word}")


# ================================================================
# PART 2: SHADOW STRUCTURE STATISTICS
# ================================================================
print(f"\n{'='*70}")
print("PART 2: SHADOW STRUCTURE STATISTICS")
print("="*70)

if good and shadows:
    # Are shadows all the same length?
    all_lens = [len(s) for s in shadows]
    print(f"Number of shadows: {len(shadows)}")
    print(f"Lengths: min={min(all_lens)}, max={max(all_lens)}, unique={len(set(all_lens))}")
    print(f"Length distribution: {Counter(all_lens)}")

    # Do shadows use the same mover word?
    same_word_count = 0
    diff_word_count = 0
    for shadow in shadows:
        movers = []
        valid = True
        for t in range(len(shadow)):
            c1 = shadow[t]
            c2 = shadow[(t+1) % len(shadow)]
            diffs = config_diff(c1, c2, n)
            if len(diffs) == 1:
                movers.append(diffs[0])
            else:
                valid = False
                break
        if valid and movers == word:
            same_word_count += 1
        else:
            diff_word_count += 1
    print(f"Shadows with same mover word: {same_word_count}")
    print(f"Shadows with different mover word: {diff_word_count}")

    # Are all shadows just constant-offset versions of each other?
    print(f"\nChecking if all shadows are constant-offset related...")
    offsets_from_s0 = []
    for si, shadow in enumerate(shadows[:20]):
        res = describe_transformation(shadows[0], shadow, n, ms)
        offsets_from_s0.append(res)
    offset_types = Counter(offsets_from_s0)
    for otype, cnt in offset_types.most_common(5):
        print(f"  {otype}: {cnt}")

    # Check: are shadows related to good by set-level offset?
    print(f"\nChecking set-level offsets from good to each shadow...")
    good_set = set(good)
    offset_found = 0
    offset_not_found = 0
    for shadow in shadows[:50]:
        shadow_set = set(shadow)
        found = False
        for offset in iproduct(*(range(m) for m in ms)):
            if all(o == 0 for o in offset):
                continue
            shifted = set(tuple((g[j] + offset[j]) % ms[j] for j in range(n)) for g in good)
            if shifted == shadow_set:
                found = True
                break
        if found:
            offset_found += 1
        else:
            offset_not_found += 1
    print(f"  Set-level offset from good: found={offset_found}, not found={offset_not_found} (of {min(50, len(shadows))} checked)")


# ================================================================
# PART 3: TEST AT SMALLER n
# ================================================================
print(f"\n{'='*70}")
print("PART 3: SMALLER n TESTS")
print("="*70)

# --- n=5, ms=(2,2,2,3,3): uniform sweep ---
print("\n--- n=5, ms=(2,2,2,3,3): uniform sweep cycles ---")
n5 = 5
ms5 = [2,2,2,3,3]

# Uniform sweep word: 0,1,2,3,4,4,3,2,1,0
sweep_word_5 = list(range(n5)) + list(range(n5-1, -1, -1))
print(f"Sweep word: {sweep_word_5}, CL={len(sweep_word_5)}")

good5 = build_cycle_from_word(sweep_word_5, ms5, n5)
if good5:
    print(f"Good cycle: {len(good5)} configs")
    ec5 = check_ec(good5, sweep_word_5, n5)
    has_mnu5, _ = check_mnu(good5, sweep_word_5, n5)
    print(f"EC: {bool(ec5)}, MNU: {has_mnu5}")

    all5 = find_all_cycles(sweep_word_5, ms5, n5)
    shadows5 = find_shadow_cycles(good5, all5)
    print(f"All cycles: {len(all5)}, Shadows: {len(shadows5)}")

# --- n=5, ms=(2,2,2,3,4): M_5=96 witness ---
print("\n--- n=5, ms=(2,2,2,3,4): M_5=96 witness system ---")
ms5b = [2,2,2,3,4]
product5b = prod(ms5b)
print(f"Product: {product5b}")

# Build valid system for M_5=96
# From the CLB construction (endpoint binary)
# Actually, let's find the good cycle from a valid system
# The M_5=96 witness uses ms=(2,2,2,3,4) with specific transition functions
# Let's enumerate good cycles

# Try sweep word first
sweep5b = list(range(n5)) + list(range(n5-1, -1, -1))
good5b = build_cycle_from_word(sweep5b, ms5b, n5)
if good5b:
    print(f"Sweep cycle: {len(good5b)} configs")
    ec5b = check_ec(good5b, sweep5b, n5)
    has_mnu5b, _ = check_mnu(good5b, sweep5b, n5)
    print(f"EC: {bool(ec5b)}, MNU: {has_mnu5b}")

    all5b = find_all_cycles(sweep5b, ms5b, n5)
    shadows5b = find_shadow_cycles(good5b, all5b)
    print(f"All cycles: {len(all5b)}, Shadows: {len(shadows5b)}")
else:
    print("Sweep word doesn't close with all-inc for ms=(2,2,2,3,4)")

# Try all transition modes for sweep
print("\nSearching for valid sweep cycles over all transition modes...")
ternary_procs_5b = [i for i in range(n5) if ms5b[i] > 2]
binary_procs_5b = [i for i in range(n5) if ms5b[i] == 2]
print(f"Ternary+ procs: {ternary_procs_5b}, Binary procs: {binary_procs_5b}")

# For procs with ms > 2, try inc/dec
valid_sweep_count = 0
for combo in iproduct(*[[1, -1] if ms5b[p] > 2 else [1] for p in range(n5)]):
    trans = list(combo)
    cyc = build_cycle_from_word(sweep5b, ms5b, n5, list(trans))
    if cyc:
        ec = check_ec(cyc, sweep5b, n5)
        has_mnu_val, _ = check_mnu(cyc, sweep5b, n5)
        all_c = find_all_cycles(sweep5b, ms5b, n5, list(trans))
        sh = find_shadow_cycles(cyc, all_c)
        valid_sweep_count += 1
        if valid_sweep_count <= 5:
            print(f"  trans={trans}: CL={len(cyc)}, EC={bool(ec)}, MNU={has_mnu_val}, shadows={len(sh)}")

print(f"Total valid sweep cycles: {valid_sweep_count}")

# --- n=5, ms=(2,2,2,3,3): NON-sweep cycles ---
print("\n--- n=5, ms=(2,2,2,3,3): non-sweep good cycles ---")
# Try some non-sweep words
# A non-sweep word where procs don't go in order
# Wiggle word: 0,1,0,2,1,2,3,4,3,4
# or bounce: various patterns

# Actually, let's systematically find ALL valid mover words for n=5
# that produce closed cycles with CL=10 (minimum for this ms)
# This is expensive, so just try a few known patterns

# Non-sweep: try 0,1,2,3,4,3,2,1,0,4 (move proc 4 at end instead of start)
test_words = [
    [0,1,2,3,4,3,4,2,1,0],  # modified sweep
    [4,3,2,1,0,1,2,3,4,0],  # reverse + pivot
    [0,1,0,2,3,4,3,2,1,4],  # wiggle
]

for tw in test_words:
    fc_tw = Counter(tw)
    # Check fire counts match ms requirements
    valid_fc = all(fc_tw.get(p, 0) == ms5[p] for p in range(n5))
    if not valid_fc:
        continue
    cyc_tw = build_cycle_from_word(tw, ms5, n5)
    if cyc_tw:
        ec_tw = check_ec(cyc_tw, tw, n5)
        mnu_tw, _ = check_mnu(cyc_tw, tw, n5)
        all_tw = find_all_cycles(tw, ms5, n5)
        sh_tw = find_shadow_cycles(cyc_tw, all_tw)
        print(f"Word {tw}: CL={len(cyc_tw)}, EC={bool(ec_tw)}, MNU={mnu_tw}, shadows={len(sh_tw)}")


# ================================================================
# PART 3b: EXHAUSTIVE non-sweep cycle search at n=5
# ================================================================
print(f"\n--- Exhaustive non-sweep word search at n=5, ms=(2,2,2,3,3) ---")
# Generate all mover words where each proc fires exactly ms[p] times
# n=5, ms=(2,2,2,3,3) => CL = 2+2+2+3+3 = 12... wait
# Actually for sweep: CL = 2*n = 10 (each proc fires exactly once in each direction)
# But fire count: sweep has each proc fire 2 times, total = 10
# With ms=(2,2,2,3,3), binary fire 2x, ternary fire 3x => CL = 2*3 + 3*2 = 12
# Hmm, for sweep cycles specifically, each proc fires exactly once per sweep direction
# Let me recheck

print(f"Sweep word {sweep_word_5}: fire counts = {Counter(sweep_word_5)}")
print(f"Expected for return to start: binary needs even fires, ternary needs mult of 3")

# For a cycle starting at all-zeros with incrementing:
# proc p fires f_p times, each time incrementing by 1 mod ms[p]
# To return to 0: f_p must be multiple of ms[p]
# Minimum: f_p = ms[p]
# So minimum CL = sum(ms) = 2+2+2+3+3 = 12

min_CL_5 = sum(ms5)
print(f"Minimum cycle length for ms={ms5}: {min_CL_5}")
print(f"But sweep word has CL={len(sweep_word_5)} with fire counts {Counter(sweep_word_5)}")
# The sweep word fires each proc exactly 2 times regardless of ms
# For ternary procs, 2 fires of +1 gives value 2, not 0
# So sweep word doesn't have minimum fire counts for ternary!
# It works because the ternary fires 2 times, ending at value 2, which equals 2 mod 3 != 0
# Wait, but the cycle closes? Let me check...

if good5:
    print(f"\nVerifying sweep cycle closure:")
    print(f"  Start: {good5[0]}")
    print(f"  End+1: should equal start")
    last = list(good5[-1])
    p = sweep_word_5[-1]
    last[p] = (last[p] + 1) % ms5[p]
    print(f"  After last move: {tuple(last)} == start? {tuple(last) == good5[0]}")

# OK so sweep fires each proc 2 times for CL=10
# For ternary proc firing 2 times: 0 -> 1 -> 2. Doesn't return to 0.
# But the word might use different directions (CW then CCW)
# In the sweep CW+CCW: proc fires +1 then +1... that gives 2 mod 3.
# Hmm, this shouldn't close. Let me just check what the actual configs are.

if good5:
    print(f"\nFull sweep cycle:")
    for i in range(len(good5)):
        mover = sweep_word_5[i]
        print(f"  t={i}: {good5[i]} -> move proc {mover}")

# OK I think the sweep word at n=5 with ms=(2,2,2,3,3) may NOT produce a valid cycle
# Let's try the minimum-fire-count word instead
print(f"\n--- Minimum fire count words at n=5, ms=(2,2,2,3,3) ---")
# Each proc p fires ms[p] times. Total CL = 12.
# Generate words where proc p appears exactly ms[p] times

from itertools import permutations
import random

def generate_valid_words_small(n, ms, max_words=200):
    """Generate valid mover words: each proc p fires ms[p] times, forms closed cycle."""
    CL = sum(ms)
    # Build base multiset
    base = []
    for p in range(n):
        base.extend([p]*ms[p])

    valid = []
    seen = set()

    # Try random permutations
    random.seed(42)
    for _ in range(50000):
        w = list(base)
        random.shuffle(w)
        wt = tuple(w)
        if wt in seen:
            continue
        seen.add(wt)

        # Check: does this word produce a valid cycle with all-inc?
        cyc = build_cycle_from_word(w, ms, n)
        if cyc and len(cyc) == CL:
            valid.append(w)
            if len(valid) >= max_words:
                break

    return valid

print("Searching for minimum-CL words (random sample)...")
valid_words_5 = generate_valid_words_small(n5, ms5)
print(f"Found {len(valid_words_5)} valid words")

if valid_words_5:
    # Classify: sweep-like vs non-sweep
    sweep_set = set(tuple(sweep_word_5))

    n_with_ec = 0
    n_with_shadow = 0
    n_with_mnu = 0
    n_neither = 0

    for w in valid_words_5[:100]:
        cyc = build_cycle_from_word(w, ms5, n5)
        ec = check_ec(cyc, w, n5)
        mnu_ok, _ = check_mnu(cyc, w, n5)
        all_c = find_all_cycles(w, ms5, n5)
        sh = find_shadow_cycles(cyc, all_c)

        has_ec = bool(ec)
        has_sh = len(sh) > 0

        if has_ec:
            n_with_ec += 1
        if has_sh:
            n_with_shadow += 1
        if mnu_ok:
            n_with_mnu += 1
        if not has_ec and not has_sh:
            n_neither += 1
            print(f"  NEITHER: word={w}, MNU={mnu_ok}")

    total_checked = min(100, len(valid_words_5))
    print(f"\nOf {total_checked} valid words at n=5, ms=(2,2,2,3,3):")
    print(f"  Has EC: {n_with_ec}")
    print(f"  Has shadow: {n_with_shadow}")
    print(f"  Has MNU: {n_with_mnu}")
    print(f"  Neither EC nor shadow: {n_neither}")


# ================================================================
# PART 4: DOES THE SYSTEM MATTER? (n=5)
# ================================================================
print(f"\n{'='*70}")
print("PART 4: SYSTEM vs CYCLE — DOES TRANSITION FUNCTION MATTER?")
print("="*70)

# Key question: shadow formation depends on the WORD (mover sequence),
# not the transition function. The word determines which proc fires at
# each step, and the transition function determines the VALUES.
# But the shadow cycles are found by applying the SAME word to OTHER
# starting configurations.

# For a given word, the word partitions configuration space into orbits.
# The good cycle is one orbit. Shadow cycles are other orbits.
# With incrementing transitions, every orbit that closes is a cycle.
# The number of shadow cycles depends on the orbit structure.

# With non-incrementing transitions, different orbits may or may not close.

# Test: for the same word, different transition functions give different shadow counts
if valid_words_5:
    w_test = valid_words_5[0]
    print(f"\nTest word: {w_test}")
    print(f"Testing different transition modes:")

    ternary_5 = [i for i in range(n5) if ms5[i] == 3]
    for combo in iproduct([1, -1], repeat=len(ternary_5)):
        trans = [1]*n5
        for idx, tp in enumerate(ternary_5):
            trans[tp] = combo[idx]

        cyc = build_cycle_from_word(w_test, ms5, n5, trans)
        if cyc:
            all_c = find_all_cycles(w_test, ms5, n5, trans)
            sh = find_shadow_cycles(cyc, all_c)
            ec = check_ec(cyc, w_test, n5)
            mnu_ok, _ = check_mnu(cyc, w_test, n5)
            print(f"  trans={trans}: cycles={len(all_c)}, shadows={len(sh)}, EC={bool(ec)}, MNU={mnu_ok}")


# ================================================================
# PART 5: MNU AND SHADOW CORRELATION
# ================================================================
print(f"\n{'='*70}")
print("PART 5: MNU AND SHADOW CORRELATION")
print("="*70)

# Key hypothesis: MNU is sufficient (but not necessary?) for shadow.
# Check correlation between MNU and shadow existence.

if valid_words_5:
    mnu_shadow = 0
    mnu_noshadow = 0
    nomnu_shadow = 0
    nomnu_noshadow = 0

    for w in valid_words_5[:100]:
        cyc = build_cycle_from_word(w, ms5, n5)
        if cyc is None:
            continue
        mnu_ok, _ = check_mnu(cyc, w, n5)
        all_c = find_all_cycles(w, ms5, n5)
        sh = find_shadow_cycles(cyc, all_c)
        has_sh = len(sh) > 0

        if mnu_ok and has_sh:
            mnu_shadow += 1
        elif mnu_ok and not has_sh:
            mnu_noshadow += 1
        elif not mnu_ok and has_sh:
            nomnu_shadow += 1
        else:
            nomnu_noshadow += 1

    print(f"MNU+Shadow: {mnu_shadow}")
    print(f"MNU+NoShadow: {mnu_noshadow}")
    print(f"NoMNU+Shadow: {nomnu_shadow}")
    print(f"NoMNU+NoShadow: {nomnu_noshadow}")

    print(f"\nKey: MNU implies shadow? {mnu_noshadow == 0}")
    print(f"Key: Shadow implies MNU? {nomnu_shadow == 0}")


# ================================================================
# SUMMARY
# ================================================================
print(f"\n{'='*70}")
print("SUMMARY AND ASSESSMENT")
print("="*70)
print("""
This script investigates whether shadow cycles generalize beyond WaterfallCycles.
Key questions answered above:
1. What do non-waterfall shadows look like?
2. Is there a simple transformation (constant offset)?
3. Does MNU correlate with shadow?
4. Does the transition function matter?
5. Can shadow alone cover the entire lower bound?
""")
