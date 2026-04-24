"""
Quaternary Necessity Check: Can ANY system with all m_i <= 3 work for n=5?

Tests:
1. Dijkstra's Solution 1 with K=2,3,4,5 for n=5
2. Dijkstra's Solution 3 for n=5
3. Random search for ms=(2,2,2,3,3)
4. Random search for ms=(3,3,3,3,3)
"""

import sys
sys.path.insert(0, '.')
from verifier import verify_system, verify_dijkstra_solution1, verify_dijkstra_solution3
import random
from itertools import product as iproduct

n = 5

# ============================================================
# PART 1: Dijkstra's known solutions
# ============================================================

print("="*70)
print("PART 1: DIJKSTRA'S SOLUTIONS FOR n=5")
print("="*70)

for K in range(2, 7):
    result = verify_dijkstra_solution1(n, K)
    status = "VALID" if result['valid'] else "INVALID"
    print(f"  Solution 1, K={K}: {status} (product={K**n})")
    if result['valid']:
        print(f"    Cycle length: {result['cycle_length']}")

result3 = verify_dijkstra_solution3(n)
status = "VALID" if result3['valid'] else "INVALID"
print(f"  Solution 3: {status} (product={3**n}=243)")

# ============================================================
# PART 2: Random search for ms=(2,2,2,3,3)
# ============================================================

print("\n" + "="*70)
print("PART 2: RANDOM SEARCH for ms=(2,2,2,3,3)")
print("="*70)

ms_test = [2, 2, 2, 3, 3]

def random_transition_functions(ms):
    """Generate random transition functions for given state vector."""
    n = len(ms)
    fs = []
    for i in range(n):
        m_L = ms[(i-1) % n]
        m_S = ms[i]
        m_R = ms[(i+1) % n]
        lookup = {}
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    lookup[(L,S,R)] = random.randint(0, m_S - 1)

        def make_f(table):
            def f(L, S, R):
                return table[(L, S, R)]
            return f

        fs.append(make_f(lookup))
    return fs

random.seed(42)
valid_count = 0
total = 5000

for trial in range(total):
    fs = random_transition_functions(ms_test)
    result = verify_system(ms_test, fs)
    if result['valid']:
        valid_count += 1
        print(f"  *** VALID SYSTEM FOUND at trial {trial}! ***")
        print(f"  Cycle length: {result['cycle_length']}")
        break

if valid_count == 0:
    print(f"  No valid system found in {total} random trials for ms=(2,2,2,3,3)")

# ============================================================
# PART 3: Random search for ms=(3,3,3,3,3)
# ============================================================

print("\n" + "="*70)
print("PART 3: RANDOM SEARCH for ms=(3,3,3,3,3)")
print("="*70)

ms_test2 = [3, 3, 3, 3, 3]
valid_count = 0
total = 5000

for trial in range(total):
    fs = random_transition_functions(ms_test2)
    result = verify_system(ms_test2, fs)
    if result['valid']:
        valid_count += 1
        print(f"  *** VALID SYSTEM FOUND at trial {trial}! ***")
        print(f"  Cycle length: {result['cycle_length']}")
        break

if valid_count == 0:
    print(f"  No valid system found in {total} random trials for ms=(3,3,3,3,3)")

# ============================================================
# PART 4: Dijkstra-like systems for ms=(2,2,2,3,3)
# ============================================================

print("\n" + "="*70)
print("PART 4: DIJKSTRA-LIKE SYSTEMS for ms=(2,2,2,3,3)")
print("="*70)

ms_d = [2, 2, 2, 3, 3]

# Try all possible "distinguished processor" positions
# and various rule sets

def copy_left(L, S, R, m_S):
    return L % m_S

def copy_right(L, S, R, m_S):
    return R % m_S

def complement_left(L, S, R, m_S):
    return (1 - L) % m_S if L < m_S else L % m_S

def increment_if_match(L, S, R, m_S):
    """Dijkstra's distinguished: increment if L=S"""
    if L % m_S == S:
        return (S + 1) % m_S
    return S

def decrement_if_match(L, S, R, m_S):
    if (S + 1) % m_S == R % m_S:
        return (S - 1) % m_S
    return S

rules = {
    'copy_L': copy_left,
    'copy_R': copy_right,
    'comp_L': complement_left,
    'inc_L': increment_if_match,
    'dec_R': decrement_if_match,
}

tested = 0
found = 0

for dist_pos in range(n):
    for dist_rule_name, dist_rule in rules.items():
        for other_rule_name, other_rule in rules.items():
            fs = []
            for i in range(n):
                m_S = ms_d[i]
                if i == dist_pos:
                    rule = dist_rule
                else:
                    rule = other_rule

                def make_f(rule_fn, m):
                    def f(L, S, R):
                        return rule_fn(L, S, R, m)
                    return f

                fs.append(make_f(rule, m_S))

            result = verify_system(ms_d, fs)
            tested += 1
            if result['valid']:
                found += 1
                print(f"  VALID: dist_pos=P{dist_pos}, "
                      f"dist_rule={dist_rule_name}, other_rule={other_rule_name}")
                print(f"    Cycle length: {result['cycle_length']}")

print(f"  Tested {tested} Dijkstra-like systems, found {found} valid")

# ============================================================
# PART 5: Check OTHER all-≤3 state vectors
# ============================================================

print("\n" + "="*70)
print("PART 5: ALL STATE VECTORS WITH max(m_i)=3 FOR n=5")
print("="*70)

# List all state vectors (up to rotation) with m_i ∈ {2,3}, max=3
# Must have ≤3 consecutive binary (RFC constraint)

all_vecs = set()
for combo in iproduct([2,3], repeat=5):
    if max(combo) < 3:
        continue  # all binary, not interesting
    # Check ≤3 consecutive binary
    ok = True
    for start in range(5):
        count = 0
        for offset in range(5):
            if combo[(start + offset) % 5] == 2:
                count += 1
            else:
                break
        if count >= 4:
            ok = False
            break
    if not ok:
        continue
    # Normalize by rotation
    rotations = [combo[i:] + combo[:i] for i in range(5)]
    canonical = min(rotations)
    all_vecs.add(canonical)

print(f"State vectors to check (up to rotation): {len(all_vecs)}")
for v in sorted(all_vecs, key=lambda x: (sum(x), x)):
    prod = 1
    for x in v:
        prod *= x
    print(f"  {v}  product={prod}")

# For each, run random search
print("\nRandom search (1000 trials each):")
for v in sorted(all_vecs, key=lambda x: (sum(x), x)):
    ms_v = list(v)
    prod = 1
    for x in v:
        prod *= x

    random.seed(42)
    found_valid = False
    for trial in range(1000):
        fs = random_transition_functions(ms_v)
        result = verify_system(ms_v, fs)
        if result['valid']:
            found_valid = True
            print(f"  {v} (product={prod}): VALID at trial {trial}!")
            break

    if not found_valid:
        print(f"  {v} (product={prod}): no valid system found (1000 trials)")

# ============================================================
# PART 6: Check Dijkstra's Solution 1 with K=3,4 for n=5
# (more detail)
# ============================================================

print("\n" + "="*70)
print("PART 6: DIJKSTRA SOLUTION 1 DETAILS")
print("="*70)

for K in [3, 4, 5]:
    result = verify_dijkstra_solution1(n, K)
    print(f"\n  K={K} (ms={[K]*n}, product={K**n}):")
    if result['valid']:
        print(f"    VALID! Cycle length: {result['cycle_length']}")
    else:
        for prop, (ok, info) in result['properties'].items():
            print(f"    {prop}: {'✓' if ok else '✗'} {info}")
