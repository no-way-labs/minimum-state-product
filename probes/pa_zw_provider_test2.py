"""
Test provider EC for zero-winding cycles.
Generate by random walk on the ring.
"""
import random
random.seed(42)

def left(p, n):
    return (p - 1) % n

def right(p, n):
    return (p + 1) % n

def check_provider_ec(mover_word, moduli, n):
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1
    
    if not all(f >= 2 for f in fc):
        return None
    if not any(f >= 3 for f in fc):
        return None
    
    # Check zero winding
    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0:
        return None
    
    # Check next_mover_is_local
    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None
    
    # Try all procs, all consecutive fire pairs
    for i in range(n):
        if fc[i] < 2:
            continue
        fire_steps = [k for k in range(CL) if mover_word[k] == i]
        
        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2 = fire_steps[(idx + 1) % len(fire_steps)]
            if a2 <= a1:
                a2 += CL  # wrap
            
            gap = list(range(a1 + 1, a2))
            if not gap:
                continue
            
            for k2_raw in gap:
                k2 = k2_raw % CL
                if mover_word[k2] == i:
                    continue
                
                # interval [k2_raw, a2) mod CL
                interval = [t % CL for t in range(k2_raw, a2)]
                
                li = left(i, n)
                ri = right(i, n)
                
                li_fires = sum(1 for k in interval if mover_word[k] == li)
                ri_fires = sum(1 for k in interval if mover_word[k] == ri)
                
                li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
                ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)
                
                if li_ok and ri_ok:
                    return (True, f"proc={i}, a1={a1}, a2={a2%CL}, k2={k2}")
    
    return (False, f"fc={fc}, CL={CL}, word={mover_word}")

def gen_random_zw_word(n, target_len=None):
    """Generate random local mover word, then check ZW."""
    if target_len is None:
        target_len = random.randint(2*n + 1, 4*n)
    
    word = [random.randint(0, n-1)]
    for _ in range(target_len - 1):
        curr = word[-1]
        choices = [curr, left(curr, n), right(curr, n)]
        word.append(random.choice(choices))
    return word

n = 5
moduli = [2, 2, 2, 3, 3]

print(f"Testing n={n}, moduli={moduli}")
success = 0
fail = 0
skip = 0
total_tried = 0

fail_examples = []

for trial in range(200000):
    word = gen_random_zw_word(n)
    total_tried += 1
    result = check_provider_ec(word, moduli, n)
    if result is None:
        skip += 1
    elif result[0]:
        success += 1
    else:
        fail += 1
        if len(fail_examples) < 5:
            fail_examples.append(result[1])

print(f"Tried: {total_tried}, Valid ZW: {success + fail}, Success: {success}, Fail: {fail}, Skip: {skip}")
if fail > 0:
    print("FAILURES:")
    for ex in fail_examples:
        print(f"  {ex}")
else:
    print("ALL PASS!" if success > 0 else "No valid cycles found")

# Also try n=9
n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]
print(f"\nTesting n={n}, moduli={moduli}")
success = 0
fail = 0
skip = 0

for trial in range(200000):
    word = gen_random_zw_word(n)
    result = check_provider_ec(word, moduli, n)
    if result is None:
        skip += 1
    elif result[0]:
        success += 1
    else:
        fail += 1
        if fail <= 3:
            print(f"FAIL: {result[1]}")

print(f"Valid ZW: {success + fail}, Success: {success}, Fail: {fail}")
