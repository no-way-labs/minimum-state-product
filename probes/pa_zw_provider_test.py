"""
Test the provider EC argument for zero-winding cycles with fc >= 3.

Setup: ring of n procs, >=3 binary (modulus 2), rest ternary (modulus 3).
Good cycle with zero winding, cw > 0, all fc >= 2, some fc >= 3.

We need to find proc i with consecutive fires (a1, a2) and a non-mover step k2
in [a1+1, a2) such that:
  - left(i) fires 0 times in [k2, a2), OR is binary with even fires in [k2, a2)
  - right(i) fires 0 times in [k2, a2), OR is binary with even fires in [k2, a2)
  - i fires 0 times in [k2, a2) [automatic between consecutive fires]

This gives matching (L,S,R) context at step a2 (where i is mover) and k2 (where i is not mover).
"""

import itertools
from collections import defaultdict

def left(p, n):
    return (p - 1) % n

def right(p, n):
    return (p + 1) % n

def check_provider_ec(mover_word, moduli, n):
    """
    Given a mover word (list of proc indices) and moduli,
    check if the provider EC mechanism works.
    Returns (True, details) or (False, details).
    """
    CL = len(mover_word)
    
    # Compute fire counts
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1
    
    # Check prerequisites
    if not all(f >= 2 for f in fc):
        return None  # skip
    if not any(f >= 3 for f in fc):
        return None  # skip
    
    # Check zero winding
    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0:
        return None  # not ZW with cw > 0
    
    # Check next_mover_is_local
    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None  # not local
    
    # Try all procs, all consecutive fire pairs
    for i in range(n):
        if fc[i] < 2:
            continue
        
        # Find fire steps for proc i
        fire_steps = [k for k in range(CL) if mover_word[k] == i]
        
        # Try consecutive pairs
        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2 = fire_steps[(idx + 1) % len(fire_steps)]
            
            # Handle wrap-around
            if a2 <= a1:
                continue  # skip wrap for simplicity
            
            # Gap between a1 and a2
            gap = list(range(a1 + 1, a2))
            if not gap:
                continue
            
            # Try each non-mover step in the gap as k2
            for k2 in gap:
                if mover_word[k2] == i:
                    continue  # i fires here, not valid k2
                
                # Check: interval [k2, a2) — how many times do left(i), right(i) fire?
                li = left(i, n)
                ri = right(i, n)
                
                interval = list(range(k2, a2))
                
                li_fires = sum(1 for k in interval if mover_word[k] == li)
                ri_fires = sum(1 for k in interval if mover_word[k] == ri)
                i_fires = sum(1 for k in interval if mover_word[k] == i)
                
                assert i_fires == 0  # between consecutive fires
                
                li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
                ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)
                
                if li_ok and ri_ok:
                    return (True, f"proc={i}, a1={a1}, a2={a2}, k2={k2}, li_fires={li_fires}, ri_fires={ri_fires}")
    
    return (False, f"fc={fc}, word={mover_word}")

def generate_local_mover_words(n, max_len=30):
    """Generate mover words satisfying next_mover_is_local via DFS."""
    results = []
    
    def dfs(word, start_proc):
        CL = len(word)
        if CL < 2 * n:
            return
        if CL > max_len:
            return
        
        # Check if we can close the cycle
        last = word[-1]
        if start_proc == last or start_proc == left(last, n) or start_proc == right(last, n):
            # Check zero winding
            cw = sum(1 for k in range(CL) if word[(k+1) % CL] == right(word[k], n))
            ccw = sum(1 for k in range(CL) if word[(k+1) % CL] == left(word[k], n))
            stay = CL - cw - ccw
            
            if cw == ccw and cw > 0:
                fc = [0] * n
                for m in word:
                    fc[m] += 1
                if all(f >= 2 for f in fc) and any(f >= 3 for f in fc):
                    results.append(list(word))
                    if len(results) >= 5000:
                        return
        
        if CL >= max_len:
            return
        
        curr = word[-1]
        for nxt in [curr, left(curr, n), right(curr, n)]:
            word.append(nxt)
            dfs(word, start_proc)
            word.pop()
            if len(results) >= 5000:
                return
    
    for start in range(n):
        dfs([start], start)
        if len(results) >= 5000:
            break
    
    return results

# Test at n=5 with 3 binary
n = 5
moduli = [2, 2, 2, 3, 3]  # 3 binary procs

print(f"Generating zero-winding mover words for n={n}...")
words = generate_local_mover_words(n, max_len=16)
print(f"Found {len(words)} candidate words")

success = 0
fail = 0
skip = 0

for word in words:
    result = check_provider_ec(word, moduli, n)
    if result is None:
        skip += 1
    elif result[0]:
        success += 1
    else:
        fail += 1
        print(f"FAIL: {result[1]}")

print(f"\nResults: {success} success, {fail} fail, {skip} skip")
if fail == 0 and success > 0:
    print("ALL PASS!")
