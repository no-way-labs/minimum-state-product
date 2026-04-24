"""
Analyze WHY the provider EC mechanism always works.
Focus on: which proc i wins, why, and what structural property guarantees it.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def analyze_provider_ec(mover_word, moduli, n):
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1
    
    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None
    
    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None
    
    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None
    
    # Find ALL winning (i, interval_type) combos
    winners = []
    
    for i in range(n):
        if fc[i] < 2: continue
        fire_steps = [k for k in range(CL) if mover_word[k] == i]
        
        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1:
                a2_raw += CL
            
            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue
            
            # Find the FIRST non-mover step closest to a2
            # Actually, let's find k2 = a2 - 1 (the step just before a2)
            # By next_mover_is_local, mover at a2-1 is adjacent to i
            k2_raw = a2_raw - 1
            k2 = k2_raw % CL
            
            if mover_word[k2] == i:
                continue
            
            li = left(i, n)
            ri = right(i, n)
            
            # For k2 = a2 - 1, interval [k2, a2) has just one step: k2 itself
            # So li_fires = 1 if mover[k2] == li else 0
            # ri_fires = 1 if mover[k2] == ri else 0
            # i_fires = 0 (since mover[k2] != i)
            
            li_fires = 1 if mover_word[k2] == li else 0
            ri_fires = 1 if mover_word[k2] == ri else 0
            
            li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
            ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)
            
            if li_ok and ri_ok:
                # k2 = a2-1, only 1 step in interval
                # This means: mover[a2-1] is adjacent to i but NOT li and NOT ri
                # Wait, that can't be — adjacent to i IS li or ri
                # So mover[k2] is one of {li, ri, i}
                # If mover[k2] != i, then mover[k2] is li or ri
                # If mover[k2] == li, then li_fires=1 (odd, only ok if NOT binary or binary even)
                # li_fires=1 is odd → li_ok requires li_fires==0, contradiction
                # So this only works if mover[k2] == ri and li_fires==0
                # But then ri_fires=1, ri_ok requires ri_fires==0 → fail
                # So k2=a2-1 with single-step interval NEVER works (unless stay)
                pass
            
            # Let me check: what's the typical winning k2?
            for k2_raw2 in gap:
                k2_2 = k2_raw2 % CL
                if mover_word[k2_2] == i: continue
                
                interval = [t % CL for t in range(k2_raw2, a2_raw)]
                li_fires2 = sum(1 for k in interval if mover_word[k] == li)
                ri_fires2 = sum(1 for k in interval if mover_word[k] == ri)
                
                li_ok2 = (li_fires2 == 0) or (moduli[li] == 2 and li_fires2 % 2 == 0)
                ri_ok2 = (ri_fires2 == 0) or (moduli[ri] == 2 and ri_fires2 % 2 == 0)
                
                if li_ok2 and ri_ok2:
                    gap_len = a2_raw - a1
                    dist_to_a2 = a2_raw - k2_raw2
                    mover_at_k2 = mover_word[k2_2]
                    rel = "self" if mover_at_k2 == i else ("left" if mover_at_k2 == li else ("right" if mover_at_k2 == ri else "other"))
                    is_binary_i = moduli[i] == 2
                    is_binary_li = moduli[li] == 2
                    is_binary_ri = moduli[ri] == 2
                    winners.append({
                        'proc': i, 'fc': fc[i], 'gap': gap_len, 'dist': dist_to_a2,
                        'li_fires': li_fires2, 'ri_fires': ri_fires2,
                        'mover_at_k2': rel,
                        'bin_i': is_binary_i, 'bin_li': is_binary_li, 'bin_ri': is_binary_ri
                    })
                    break  # first winning k2 per (i, pair)
    
    if not winners:
        return (False, fc, mover_word)
    return (True, winners)

n = 5
moduli = [2, 2, 2, 3, 3]

# Analyze patterns
all_winners = []
n_valid = 0

for trial in range(100000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 4*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    
    result = analyze_provider_ec(word, moduli, n)
    if result is None: continue
    if result[0] == False:
        print(f"FAIL: fc={result[1]}, word={result[2]}")
        continue
    
    n_valid += 1
    _, winners = result
    all_winners.extend(winners)

print(f"Valid cycles: {n_valid}")
print(f"Total winning combos: {len(all_winners)}")

# Statistics
print("\n--- Winning proc binary? ---")
print(Counter(w['bin_i'] for w in all_winners))

print("\n--- Left neighbor binary? ---")
print(Counter(w['bin_li'] for w in all_winners))

print("\n--- Right neighbor binary? ---")
print(Counter(w['bin_ri'] for w in all_winners))

print("\n--- Mover at k2 relative to i ---")
print(Counter(w['mover_at_k2'] for w in all_winners))

print("\n--- li_fires in winning interval ---")
print(Counter(w['li_fires'] for w in all_winners).most_common(10))

print("\n--- ri_fires in winning interval ---")
print(Counter(w['ri_fires'] for w in all_winners).most_common(10))

print("\n--- Gap length (a2 - a1) ---")
print(Counter(w['gap'] for w in all_winners).most_common(10))

print("\n--- Distance from k2 to a2 ---")
print(Counter(w['dist'] for w in all_winners).most_common(10))

print("\n--- fc of winning proc ---")
print(Counter(w['fc'] for w in all_winners).most_common(10))

# Key question: is there always a proc with fc=2 that wins?
# Or do we need fc>=3 procs to win?
print("\n--- Does a fc=2 proc always win? ---")
# Check per cycle
fc2_wins = 0
fc3_only = 0
for trial in range(50000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 4*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    
    result = analyze_provider_ec(word, moduli, n)
    if result is None or result[0] == False: continue
    
    _, winners = result
    has_fc2_winner = any(w['fc'] == 2 for w in winners)
    if has_fc2_winner:
        fc2_wins += 1
    else:
        fc3_only += 1

print(f"fc=2 wins: {fc2_wins}, fc>=3 only wins: {fc3_only}")
