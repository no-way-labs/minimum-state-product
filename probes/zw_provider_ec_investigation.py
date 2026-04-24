"""
Investigation: zw_provider_ec — Under ZW + cw > 0 + fc >= 2 for all + some fc >= 3,
does entry conflict always hold?

And: is fc >= 3 even possible under ZW + cw > 0 + sub-threshold + >=3 binary?
"""

import itertools
from collections import Counter

def enumerate_good_cycles(n, ms, max_cl=None):
    """Enumerate all good cycles for a ring system with state vector ms.
    A good cycle is a sequence of (config, mover, direction) that returns to start,
    visiting distinct configs, where each proc fires at least once, no proc fires exactly once."""
    if max_cl is None:
        max_cl = 4 * n  # reasonable upper bound
    
    # We'll do BFS/DFS on mover words and check good cycle properties
    # For efficiency, enumerate mover words (sequence of proc indices) and check validity
    
    # Actually, let's enumerate all valid good cycles by building them step by step
    # Config = tuple of proc states
    # At each step, a mover proc p fires: config[p] changes, then we check
    
    # This is expensive. Let's focus on small n.
    # For n=5, ms=(2,2,2,3,3), product=36 (sub-threshold = 4*3^3 = 108, so 36 < 108 yes)
    # Wait, sub-threshold means product < 4*3^(n-2). For n=5: 4*27 = 108.
    
    results = []
    
    # Generate all possible starting configs
    all_configs = list(itertools.product(*[range(m) for m in ms]))
    
    # For each starting config, do DFS to find good cycles
    # This is too expensive for large state spaces. Let's use the verifier approach instead.
    
    return results

def winding_number(mover_word, n):
    """Compute winding number of a mover word on ring of size n.
    CW step: mover[i+1] = (mover[i] + 1) % n
    CCW step: mover[i+1] = (mover[i] - 1) % n
    Winding = (CW - CCW) / n"""
    cw = 0
    ccw = 0
    for i in range(len(mover_word) - 1):
        curr = mover_word[i]
        nxt = mover_word[i + 1]
        if nxt == (curr + 1) % n:
            cw += 1
        elif nxt == (curr - 1) % n:
            ccw += 1
        else:
            return None  # not a valid walk (jump)
    # Last step wraps around
    curr = mover_word[-1]
    nxt = mover_word[0]
    if nxt == (curr + 1) % n:
        cw += 1
    elif nxt == (curr - 1) % n:
        ccw += 1
    else:
        return None
    
    if (cw - ccw) % n != 0:
        return None
    return (cw - ccw) // n

def fire_counts(mover_word, n):
    """Count how many times each proc fires."""
    fc = [0] * n
    for p in mover_word:
        fc[p] += 1
    return fc

def cw_count(mover_word, n):
    """Count CW steps."""
    cw = 0
    L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n:
            cw += 1
    return cw

def has_entry_conflict(mover_word, n, ms, config, transition_tables):
    """Check if a good cycle has entry conflict.
    
    A good cycle visits configs c_0, c_1, ..., c_{L-1}, c_L = c_0.
    At step k, mover_word[k] fires: config changes at that proc.
    Entry conflict: exists k1, k2, proc i such that:
      - moverAt(k1) = i, moverAt(k2) != i
      - (L, S, R) context matches at k1 and k2
    
    We need to build the full config sequence first.
    """
    L = len(mover_word)
    configs = [list(config)]
    
    for k in range(L):
        p = mover_word[k]
        prev_config = configs[-1][:]
        # Apply transition
        new_val = transition_tables[p][tuple(prev_config[q] for q in [(p-1) % n, p, (p+1) % n])]
        new_config = prev_config[:]
        new_config[p] = new_val
        configs.append(new_config)
    
    # Check cycle: configs[L] should equal configs[0]
    if configs[L] != configs[0]:
        return None  # not a cycle
    
    # Check distinct configs
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None  # not all distinct
    
    # Check fire counts: no proc fires exactly once
    fc = fire_counts(mover_word, n)
    for f in fc:
        if f == 1:
            return None  # invalid good cycle
    
    # Check entry conflict
    # For each proc i, collect (L,S,R) contexts at mover steps and non-mover steps
    for i in range(n):
        mover_contexts = set()
        nonmover_contexts = set()
        for k in range(L):
            c = configs[k]
            ctx = (c[(i-1) % n], c[i], c[(i+1) % n])
            if mover_word[k] == i:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)
        overlap = mover_contexts & nonmover_contexts
        if overlap:
            return True
    
    return False

def enumerate_zw_mover_words(n, cl):
    """Enumerate mover words of length cl on ring of size n with zero winding and cw > 0.
    A mover word is a cyclic walk on the ring."""
    # Generate all walks of length cl starting at 0 (WLOG by rotation)
    # This is exponential but feasible for small cl
    
    if cl > 20:
        return  # too expensive
    
    def dfs(word, pos):
        if len(word) == cl:
            # Check: closes back to start?
            last = word[-1]
            first = word[0]
            if (first - last) % n == 1 or (last - first) % n == 1:
                w = winding_number(word, n)
                if w == 0:
                    cw = cw_count(word, n)
                    if cw > 0:
                        yield tuple(word)
            return
        
        # Next position: CW or CCW
        for nxt in [(pos + 1) % n, (pos - 1) % n]:
            word.append(nxt)
            yield from dfs(word, nxt)
            word.pop()
    
    # Start at each proc (but really we only need distinct mover words up to cyclic rotation)
    seen = set()
    for start in range(n):
        for word in dfs([start], start):
            # Canonical form: smallest cyclic rotation
            rotations = [word[i:] + word[:i] for i in range(cl)]
            canonical = min(rotations)
            if canonical not in seen:
                seen.add(canonical)
                yield canonical

def check_zw_fc3_ec(n, ms):
    """For a given n and ms, enumerate ZW mover words with cw > 0 and fc >= 2 for all,
    and check if any has fc >= 3 at some proc. If so, verify EC."""
    
    print(f"\n=== n={n}, ms={ms} ===")
    print(f"Product = {prod(ms)}, sub-threshold = {4 * 3**(n-2)}")
    
    # Count binary procs
    n_binary = sum(1 for m in ms if m == 2)
    print(f"Binary procs: {n_binary}")
    
    if prod(ms) >= 4 * 3**(n-2):
        print("NOT sub-threshold, skipping")
        return
    
    if n_binary < 3:
        print("< 3 binary, skipping")
        return
    
    # Enumerate ZW mover words
    # CL ranges from 2n (minimum with fc>=2) up to some bound
    total_zw = 0
    zw_fc3 = 0
    zw_fc3_ec = 0
    zw_fc3_no_ec = 0
    
    for cl in range(2*n, 3*n + 1):
        print(f"  CL={cl}...")
        count = 0
        for word in enumerate_zw_mover_words(n, cl):
            fc = fire_counts(word, n)
            
            # Check fc >= 2 for all
            if any(f < 2 for f in fc):
                continue
            
            total_zw += 1
            count += 1
            
            # Check if any fc >= 3
            if max(fc) >= 3:
                zw_fc3 += 1
                # For this word, check EC across all possible systems
                # Actually we need to check ALL valid transition tables
                # That's expensive. Let's just record the word.
                print(f"    FOUND fc>=3: word={word}, fc={fc}")
        
        if count > 0:
            print(f"    {count} ZW words with fc>=2 at CL={cl}")
    
    print(f"\nTotal ZW+cw>0+fc>=2: {total_zw}")
    print(f"Of which fc>=3 at some proc: {zw_fc3}")

def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r

# Start with n=5
# Sub-threshold multisets with >= 3 binary:
# ms=(2,2,2,3,3): product=36 < 108 ✓, 3 binary ✓
print("="*60)
print("QUESTION 1: Under ZW+cw>0+fc>=2, can fc>=3 occur?")
print("="*60)

check_zw_fc3_ec(5, (2,2,2,3,3))

