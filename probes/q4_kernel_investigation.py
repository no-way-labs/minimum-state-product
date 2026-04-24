"""
Investigate WHY all 128 conflict-free 8-cycles on Q4 (all-binary n=4 ring)
have inescapable complements.
"""
from itertools import product as iproduct

N = 4
NCONFIGS = 16

def bit(c, j):
    return (c >> j) & 1

def flip(c, j):
    return c ^ (1 << j)

def context(c, j):
    """TF context for proc j at config c: (L, S, R) = (c[(j-1)%4], c[j], c[(j+1)%4])"""
    return (bit(c, (j-1)%N), bit(c, j), bit(c, (j+1)%N))

def partner(c, m):
    """Partner: flip the antipodal proc (m+2)%4"""
    return c ^ (1 << ((m+2) % N))

def forced_succ(c, m):
    """Forced successor of partner: partner fires proc m"""
    p = partner(c, m)
    return flip(p, m)

# Enumerate all directed Hamiltonian cycles on Q4
# Config space: {0,...,15}, edges: c -> flip(c,j) for j in {0,...,3}
# A directed Hamiltonian cycle visits all 16 configs exactly once

def find_all_ham_cycles():
    """Find all directed Hamiltonian cycles on Q4."""
    cycles = []
    # Fix start = 0 to avoid rotational duplicates of the same path
    # But we want ALL directed cycles (not up to rotation), so we'll normalize later

    def dfs(path, visited, movers):
        c = path[-1]
        if len(path) == NCONFIGS:
            # Check if we can return to start
            for j in range(N):
                if flip(c, j) == path[0]:
                    cycles.append((tuple(path), tuple(movers + [j])))
                    return
            return
        for j in range(N):
            nxt = flip(c, j)
            if nxt not in visited:
                visited.add(nxt)
                path.append(nxt)
                movers.append(j)
                dfs(path, visited, movers)
                movers.pop()
                path.pop()
                visited.discard(nxt)

    visited = {0}
    dfs([0], visited, [])
    return cycles

print("Finding all directed Hamiltonian cycles on Q4...")
raw_cycles = find_all_ham_cycles()
print(f"Found {len(raw_cycles)} directed cycles (starting from 0)")

# Each cycle found starts from 0. A directed cycle has 16 rotations.
# To get unique directed cycles, we normalize: the canonical form is the
# lexicographically smallest rotation.
def normalize_cycle(path):
    """Return canonical rotation (lex-smallest)."""
    best = path
    for i in range(1, len(path)):
        rotated = path[i:] + path[:i]
        if rotated < best:
            best = rotated
    return best

unique_cycles = {}
for path, movers in raw_cycles:
    canon = normalize_cycle(path)
    if canon not in unique_cycles:
        # Store with the rotation that starts at 0 for convenience
        unique_cycles[canon] = (path, movers)

print(f"Unique directed cycles: {len(unique_cycles)}")

# Now check TF conflicts
def has_tf_conflict(path, movers):
    """Check if a cycle has TF entry conflict."""
    # For each proc j, collect all (context, is_mover) pairs
    # Conflict: same context appears with mover=True and mover=False
    for j in range(N):
        ctx_as_mover = set()
        ctx_as_nonmover = set()
        for step in range(NCONFIGS):
            c = path[step]
            m = movers[step]
            ctx = context(c, j)
            if m == j:
                ctx_as_mover.add(ctx)
            else:
                ctx_as_nonmover.add(ctx)
        if ctx_as_mover & ctx_as_nonmover:
            return True
    return False

conflict_free = []
conflict_cycles = []
for canon, (path, movers) in unique_cycles.items():
    if has_tf_conflict(path, movers):
        conflict_cycles.append((path, movers))
    else:
        conflict_free.append((path, movers))

print(f"Conflict-free cycles: {len(conflict_free)}")
print(f"Cycles with TF conflict: {len(conflict_cycles)}")

# ============================================================
# INVESTIGATION 1: Partner structure
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 1: Partner structure")
print("="*60)

for idx, (path, movers) in enumerate(conflict_free[:3]):  # Show first 3
    print(f"\nCycle {idx}: movers = {movers}")
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set

    print(f"  Cycle configs: {sorted(cycle_set)}")
    print(f"  Complement:    {sorted(complement)}")

    partners_in_complement = 0
    for step in range(NCONFIGS):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        in_comp = p in complement
        if in_comp:
            partners_in_complement += 1
        if step < 4:  # Show first 4
            print(f"  Step {step}: config={c:04b}, mover={m}, partner={p:04b}, in_complement={in_comp}")

    print(f"  Partners in complement: {partners_in_complement}/{NCONFIGS}")

# Verify for ALL conflict-free cycles
print("\nVerifying partner-in-complement for ALL conflict-free cycles...")
all_partners_in_comp = True
for path, movers in conflict_free:
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set
    for step in range(NCONFIGS):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        if p not in complement:
            all_partners_in_comp = False
            print(f"  FAIL: config={c:04b}, mover={m}, partner={p:04b} NOT in complement")
            break
print(f"All partners in complement: {all_partners_in_comp}")

# ============================================================
# INVESTIGATION 2: Forced successor structure
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 2: Forced successor structure")
print("="*60)

all_forced_in_comp = True
for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set

    for step in range(NCONFIGS):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        fs = forced_succ(c, m)  # = partner XOR (1 << m)
        if fs not in complement:
            all_forced_in_comp = False
            print(f"  Cycle {idx}: config={c:04b}, mover={m}, partner={p:04b}, forced_succ={fs:04b} NOT in complement")

print(f"All forced successors in complement: {all_forced_in_comp}")

# ============================================================
# INVESTIGATION 3: Complement cycle structure
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 3: Complement cycle structure")
print("="*60)

for idx, (path, movers) in enumerate(conflict_free[:5]):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set

    # Build the forced transition map on complement
    # For each cycle config c with mover m:
    #   partner(c,m) is in complement, and it's forced to fire proc m
    #   result: forced_succ(c,m) = partner(c,m) XOR (1<<m)
    # This gives a map: partner -> forced_succ with mover m

    forced_map = {}  # complement config -> (next complement config, mover)
    for step in range(NCONFIGS):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        fs = flip(p, m)
        forced_map[p] = (fs, m)

    # Trace the forced cycle
    if not forced_map:
        continue

    start = min(forced_map.keys())
    forced_path = [start]
    forced_movers = []
    cur = start
    while True:
        nxt, m = forced_map[cur]
        forced_movers.append(m)
        if nxt == start:
            break
        forced_path.append(nxt)
        cur = nxt
        if len(forced_path) > 20:
            print(f"  Cycle {idx}: forced path too long, breaking")
            break

    print(f"\nCycle {idx}:")
    print(f"  Good cycle movers:    {movers}")
    print(f"  Forced cycle movers:  {tuple(forced_movers)}")
    print(f"  Forced cycle length:  {len(forced_path)}")
    print(f"  Forced cycle configs: {forced_path}")
    print(f"  Covers all complement: {set(forced_path) == complement}")

# Check ALL conflict-free cycles
print("\nChecking forced cycle structure for ALL conflict-free cycles...")
forced_lengths = {}
all_single_cycle = True
all_cover_complement = True

for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set

    forced_map = {}
    for step in range(NCONFIGS):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        fs = flip(p, m)
        forced_map[p] = (fs, m)

    # Check: does forced_map cover all complement configs?
    if set(forced_map.keys()) != complement:
        print(f"  Cycle {idx}: forced_map keys != complement!")
        print(f"    Keys: {sorted(forced_map.keys())}")
        print(f"    Comp: {sorted(complement)}")

    # Trace forced cycle(s)
    visited = set()
    num_cycles = 0
    cycle_lengths = []
    for start in sorted(complement):
        if start in visited:
            continue
        num_cycles += 1
        cur = start
        length = 0
        while cur not in visited:
            visited.add(cur)
            length += 1
            cur, _ = forced_map[cur]
        cycle_lengths.append(length)

    if num_cycles != 1:
        all_single_cycle = False
    if visited != complement:
        all_cover_complement = False

    key = tuple(sorted(cycle_lengths))
    forced_lengths[key] = forced_lengths.get(key, 0) + 1

print(f"Always single forced cycle: {all_single_cycle}")
print(f"Always covers complement: {all_cover_complement}")
print(f"Forced cycle length distribution: {forced_lengths}")

# ============================================================
# INVESTIGATION 3b: Mover sequence relationship
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 3b: Mover sequence relationship")
print("="*60)

mover_relationships = []
for idx, (path, movers) in enumerate(conflict_free[:10]):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set

    forced_map = {}
    for step in range(NCONFIGS):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        fs = flip(p, m)
        forced_map[p] = (fs, m)

    # Get forced mover sequence
    start = min(forced_map.keys())
    cur = start
    forced_mover_seq = []
    for _ in range(len(complement)):
        nxt, m = forced_map[cur]
        forced_mover_seq.append(m)
        cur = nxt

    # Check: are movers the same sequence (possibly shifted/reversed)?
    good_movers = list(movers)
    forced_movers = forced_mover_seq

    # Check if forced_movers is a rotation of good_movers
    doubled = good_movers + good_movers
    is_rotation = False
    rotation_offset = None
    for off in range(16):
        if doubled[off:off+16] == forced_movers:
            is_rotation = True
            rotation_offset = off
            break

    # Check antipodal relationship: m -> (m+2)%4
    antipodal_movers = [(m+2)%4 for m in good_movers]
    is_antipodal_rot = False
    doubled_anti = antipodal_movers + antipodal_movers
    for off in range(16):
        if doubled_anti[off:off+16] == forced_movers:
            is_antipodal_rot = True
            rotation_offset = off
            break

    print(f"Cycle {idx}: same_rotation={is_rotation}, antipodal_rotation={is_antipodal_rot}")
    if is_rotation:
        print(f"  offset={rotation_offset}")
    print(f"  good:   {good_movers}")
    print(f"  forced: {forced_movers}")

# ============================================================
# INVESTIGATION 4: The invariant — WHY partners stay in complement
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 4: Finding the invariant")
print("="*60)

# Hypothesis 1: Parity / Hamming weight
print("\nHypothesis 1: Hamming weight parity")
for idx, (path, movers) in enumerate(conflict_free[:5]):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set
    cycle_weights = sorted([bin(c).count('1') for c in cycle_set])
    comp_weights = sorted([bin(c).count('1') for c in complement])
    print(f"  Cycle {idx}: cycle weights={cycle_weights}, comp weights={comp_weights}")

# Hypothesis 2: XOR structure
print("\nHypothesis 2: XOR between config and partner")
for idx, (path, movers) in enumerate(conflict_free[:3]):
    print(f"\nCycle {idx}:")
    for step in range(NCONFIGS):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        xor = c ^ p
        print(f"  c={c:04b}, m={m}, p={p:04b}, c^p={xor:04b} (bit {(m+2)%4})")

# Hypothesis 3: The partner operation is an involution that swaps cycle/complement
print("\nHypothesis 3: partner as involution")
# For mover m at config c, partner flips bit (m+2)%4
# Key insight: if c is in cycle with mover m, then partner(c,m) is NOT in cycle
# This means: for every cycle step, the antipodal-flip neighbor is NOT in the cycle

# Let's check: what IS the relationship between the 8 cycle configs?
# Are they a coset of some subgroup of Z_2^4?
print("\nHypothesis 4: Coset structure")
from itertools import combinations
for idx, (path, movers) in enumerate(conflict_free[:5]):
    cycle_set = set(path)
    # Check if cycle_set is a coset of a subgroup
    # A subgroup of Z_2^4 of order 8 is generated by 3 elements
    # Check: is {c XOR c' : c, c' in cycle_set} a subgroup?
    xor_closure = set()
    configs = list(cycle_set)
    for a in configs:
        for b in configs:
            xor_closure.add(a ^ b)
    print(f"  Cycle {idx}: |XOR closure| = {len(xor_closure)}, is subgroup = {len(xor_closure) == 8}")
    if len(xor_closure) <= 16:
        print(f"    XOR closure: {sorted([f'{x:04b}' for x in xor_closure])}")

# Hypothesis 5: What bits get flipped in the cycle?
print("\nHypothesis 5: Mover frequency")
from collections import Counter
for idx, (path, movers) in enumerate(conflict_free[:5]):
    freq = Counter(movers)
    print(f"  Cycle {idx}: mover freq = {dict(sorted(freq.items()))}")

# Hypothesis 6: antipodal bit relationship
# partner(c, m) = c ^ (1 << (m+2)%4)
# If c is in cycle with mover m, and partner is NOT in cycle,
# then c and c^(1<<(m+2)%4) are separated by the cycle boundary.
#
# Key: the XOR between c and its successor c' = c ^ (1<<m) is bit m.
# The XOR between c and partner is bit (m+2)%4.
# These are DIFFERENT bits (since (m+2)%4 != m for all m in {0,1,2,3}).
#
# So the cycle edge goes along dimension m, while the partner is along dimension (m+2)%4.
print("\nHypothesis 6: Edge vs partner dimensions")
for idx, (path, movers) in enumerate(conflict_free[:3]):
    cycle_set = set(path)
    # For each config, which Q4 neighbors are in cycle vs complement?
    print(f"\nCycle {idx}:")
    for step in range(min(8, NCONFIGS)):
        c = path[step]
        m = movers[step]
        succ = path[(step+1) % NCONFIGS]
        pred = path[(step-1) % NCONFIGS]
        nbrs = {j: flip(c, j) for j in range(4)}
        in_cycle = {j: nbrs[j] in cycle_set for j in range(4)}
        anti = (m+2) % 4
        print(f"  c={c:04b} m={m} anti={anti}: neighbors in cycle: {in_cycle}, pred_dim={(step>0 and [j for j in range(4) if flip(c,j)==pred]) or '?'}")

print("\n\nDone with initial investigation.")
