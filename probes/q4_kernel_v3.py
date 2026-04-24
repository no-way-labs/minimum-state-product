"""
Deep investigation of the 16 (canonical) conflict-free fair 8-cycles on Q4.
128 = 16 × 8 rotations.
"""
from collections import Counter, defaultdict

N = 4
NCONFIGS = 16

def bit(c, j):
    return (c >> j) & 1

def flip(c, j):
    return c ^ (1 << j)

def context(c, j):
    return (bit(c, (j-1)%N), bit(c, j), bit(c, (j+1)%N))

def partner(c, m):
    return c ^ (1 << ((m+2) % N))

def canonical(path, movers):
    n = len(path)
    best = None
    for i in range(n):
        rot_path = path[i:] + path[:i]
        rot_movers = movers[i:] + movers[:i]
        candidate = (rot_path, rot_movers)
        if best is None or candidate < best:
            best = candidate
    return best

# Find all fair 8-cycles
all_cycles_set = set()
all_cycles_list = []

for start in range(NCONFIGS):
    def dfs(path, visited, movers, fire_count, start_config):
        if len(path) == 8:
            c = path[-1]
            for j in range(N):
                if flip(c, j) == start_config and fire_count[j] + 1 == 2:
                    new_fc = list(fire_count)
                    new_fc[j] += 1
                    if all(f == 2 for f in new_fc):
                        cm = canonical(tuple(path), tuple(movers + [j]))
                        if cm not in all_cycles_set:
                            all_cycles_set.add(cm)
                            all_cycles_list.append((cm[0], cm[1]))
            return
        c = path[-1]
        for j in range(N):
            if fire_count[j] >= 2:
                continue
            nxt = flip(c, j)
            if nxt in visited:
                continue
            visited.add(nxt)
            path.append(nxt)
            movers.append(j)
            fire_count[j] += 1
            dfs(path, visited, movers, fire_count, start_config)
            fire_count[j] -= 1
            movers.pop()
            path.pop()
            visited.discard(nxt)

    visited = {start}
    dfs([start], visited, [], [0,0,0,0], start)

print(f"Total unique fair 8-cycles: {len(all_cycles_list)}")

def has_tf_conflict(path, movers):
    for j in range(N):
        ctx_as_mover = set()
        ctx_as_nonmover = set()
        for step in range(8):
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
for path, movers in all_cycles_list:
    if not has_tf_conflict(path, movers):
        conflict_free.append((path, movers))

print(f"Conflict-free: {len(conflict_free)} (× 8 rotations = {len(conflict_free)*8})")

# ============================================================
# INVESTIGATION 1: Partner structure
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 1: Partner structure")
print("="*60)

all_partners_ok = True
for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set
    for step in range(8):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        if p not in complement:
            all_partners_ok = False
            print(f"  FAIL cycle {idx} step {step}: c={c:04b} m={m} partner={p:04b}")
            # Check if partner is in cycle — and if so, what's its mover status
            if p in cycle_set:
                p_step = list(path).index(p)
                p_mover = movers[p_step]
                print(f"    Partner is in cycle at step {p_step}, mover={p_mover}")

print(f"All partners in complement: {all_partners_ok}")

# Show detailed partner map for first few cycles
for idx, (path, movers) in enumerate(conflict_free[:3]):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set
    print(f"\nCycle {idx}: configs={[f'{c:04b}' for c in path]}")
    print(f"  movers={movers}")
    partner_map = {}
    for step in range(8):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        partner_map[c] = (p, m)
        print(f"  step {step}: c={c:04b} m={m} anti={(m+2)%4} -> partner={p:04b}")
    print(f"  Partner set = {sorted([f'{p:04b}' for p, _ in partner_map.values()])}")
    print(f"  Complement  = {sorted([f'{c:04b}' for c in complement])}")
    # Check if partner set = complement
    print(f"  Partner set == complement: {set(p for p,_ in partner_map.values()) == complement}")

# ============================================================
# INVESTIGATION 2: Forced successor
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 2: Forced successor structure")
print("="*60)

all_fs_ok = True
for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set
    for step in range(8):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        fs = flip(p, m)
        if fs not in complement:
            all_fs_ok = False
            print(f"  FAIL cycle {idx}: c={c:04b} m={m} p={p:04b} fs={fs:04b}")
print(f"All forced successors in complement: {all_fs_ok}")

# ============================================================
# INVESTIGATION 3: Complement cycle structure
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 3: Complement forced cycle")
print("="*60)

all_single = True
mover_pairs = []

for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set

    # Build forced map: partner -> (forced_succ, mover)
    forced_map = {}
    for step in range(8):
        c = path[step]
        m = movers[step]
        p = partner(c, m)
        fs = flip(p, m)
        forced_map[p] = (fs, m)

    # Check coverage
    partner_set = set(forced_map.keys())
    if partner_set != complement:
        print(f"  Cycle {idx}: partner set != complement!")
        print(f"    Missing from partners: {complement - partner_set}")
        print(f"    Extra in partners: {partner_set - complement}")
        # This means the partner map is not a bijection on complement
        # Some complement configs are hit by multiple partners?
        target_counts = Counter(fs for fs, _ in forced_map.values())
        print(f"    Target counts: {target_counts}")

    # Trace forced cycle(s) on complement
    visited = set()
    num_comp_cycles = 0
    cycle_lengths = []
    comp_mover_seqs = []

    for s in sorted(complement):
        if s in visited or s not in forced_map:
            continue
        num_comp_cycles += 1
        cur = s
        length = 0
        mseq = []
        while cur not in visited:
            visited.add(cur)
            length += 1
            nxt, m = forced_map[cur]
            mseq.append(m)
            cur = nxt
        cycle_lengths.append(length)
        comp_mover_seqs.append(tuple(mseq))

    if num_comp_cycles != 1 or cycle_lengths != [8]:
        all_single = False

    if idx < 5:
        print(f"\nCycle {idx}:")
        print(f"  Good movers:   {movers}")
        print(f"  Forced movers: {comp_mover_seqs}")
        print(f"  Forced #cycles: {num_comp_cycles}, lengths: {cycle_lengths}")

    mover_pairs.append((movers, comp_mover_seqs[0] if len(comp_mover_seqs) == 1 else None))

print(f"\nAll single 8-cycle on complement: {all_single}")

# ============================================================
# INVESTIGATION 3b: Mover sequence relationship
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 3b: Mover sequence relationship")
print("="*60)

for idx, (good_m, forced_m) in enumerate(mover_pairs):
    if forced_m is None:
        continue
    # Check same sequence
    same = good_m == forced_m
    # Check rotation
    doubled = list(good_m) + list(good_m)
    is_rot = any(doubled[i:i+8] == list(forced_m) for i in range(8))
    # Check antipodal
    anti = tuple((m+2)%4 for m in good_m)
    doubled_anti = list(anti) + list(anti)
    is_anti_rot = any(doubled_anti[i:i+8] == list(forced_m) for i in range(8))
    # Check reversal
    rev = tuple(reversed(good_m))
    doubled_rev = list(rev) + list(rev)
    is_rev_rot = any(doubled_rev[i:i+8] == list(forced_m) for i in range(8))
    # Check antipodal reversal
    anti_rev = tuple((m+2)%4 for m in reversed(good_m))
    doubled_ar = list(anti_rev) + list(anti_rev)
    is_ar_rot = any(doubled_ar[i:i+8] == list(forced_m) for i in range(8))

    if idx < 10 or not (is_rot or is_anti_rot or is_rev_rot or is_ar_rot):
        print(f"Cycle {idx}: same={same} rot={is_rot} anti_rot={is_anti_rot} rev_rot={is_rev_rot} anti_rev_rot={is_ar_rot}")
        print(f"  good:   {good_m}")
        print(f"  forced: {forced_m}")

# ============================================================
# INVESTIGATION 4: WHY partner is in complement
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 4: Why partner is in complement")
print("="*60)

# Key operation analysis:
# At step t, config c_t with mover m_t.
# partner(c_t, m_t) = c_t XOR (1 << (m_t+2)%4)
#
# For partner to be in cycle, there'd need to be some step s with path[s] = partner.
# Let's check: what's the XOR between c_t and every other cycle config?

print("\nXOR / Hamming distance analysis:")
for idx, (path, movers) in enumerate(conflict_free[:3]):
    print(f"\nCycle {idx}: movers={movers}")
    for t in range(8):
        c = path[t]
        m = movers[t]
        anti = (m+2) % 4
        p = partner(c, m)
        # Is p equal to any cycle config?
        for s in range(8):
            if path[s] == p:
                print(f"  ERROR: step {t} partner = step {s} config")
        # What IS the relationship between c and c XOR (1<<anti)?
        # Since the cycle is on Q4, c and partner differ in exactly bit anti.
        # For partner to NOT be in cycle: bit anti separates c from all other cycle configs
        # that agree on bits != anti.
        #
        # Let mask = ~(1<<anti) & 0xF  (all bits except anti)
        # c_masked = c & mask
        # partner_masked = p & mask = c_masked (they agree on all other bits)
        # So partner and c have the same projection onto {bits \ anti}
        # For partner to be outside cycle: of the two configs {c, c^(1<<anti)},
        # exactly one is in the cycle.
        #
        # This is like a MATCHING on Q4: each edge along dimension anti
        # has exactly one endpoint in the cycle.
        pass

# Check: for conflict-free cycles, does each dimension induce a perfect matching
# between cycle and complement?
print("\nDimension matching analysis:")
for idx, (path, movers) in enumerate(conflict_free[:5]):
    cycle_set = set(path)
    complement = set(range(NCONFIGS)) - cycle_set
    for d in range(N):
        # For each pair (c, c^(1<<d)), check if exactly one is in cycle
        pairs_split = 0
        pairs_both_in = 0
        pairs_both_out = 0
        for c in range(0, NCONFIGS, 1):
            if c & (1 << d):
                continue  # Only look at c with bit d = 0
            p = c ^ (1 << d)
            c_in = c in cycle_set
            p_in = p in cycle_set
            if c_in and p_in:
                pairs_both_in += 1
            elif not c_in and not p_in:
                pairs_both_out += 1
            else:
                pairs_split += 1
        if idx < 3:
            print(f"  Cycle {idx}, dim {d}: split={pairs_split} both_in={pairs_both_in} both_out={pairs_both_out}")

# ============================================================
# INVESTIGATION 4b: Coset / linear structure
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 4b: Coset structure of cycle configs")
print("="*60)

for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    # XOR closure (difference set)
    diffs = set()
    configs = list(cycle_set)
    for a in configs:
        for b in configs:
            diffs.add(a ^ b)
    is_coset = (len(diffs) == 8)  # If coset of order-8 subgroup, diffs = subgroup
    if idx < 5 or not is_coset:
        print(f"  Cycle {idx}: |diffs| = {len(diffs)}, coset={is_coset}")
        if len(diffs) <= 16:
            print(f"    Diffs: {sorted([f'{d:04b}' for d in diffs])}")

# ============================================================
# INVESTIGATION 5: The XOR twin relationship
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 5: XOR twin analysis")
print("="*60)

# For each conflict-free cycle, the partner operation at step t
# sends c_t to c_t XOR (1<<(m_t+2)%4).
# Key insight: if the cycle visits EXACTLY one config from each pair
# {c, c^(1<<d)} for the relevant dimension d, then partner is forced outside.
#
# But dimension d = (m_t+2)%4 CHANGES with each step!
# So the question is: does the mover sequence conspire so that
# at each step, the "anti" dimension separates cycle from complement?

# Let's compute: for each step, which "anti dimensions" are used?
print("\nAnti-dimension usage:")
anti_dim_counts = Counter()
for idx, (path, movers) in enumerate(conflict_free):
    antis = [(m+2)%4 for m in movers]
    anti_dim_counts[tuple(sorted(Counter(antis).items()))] += 1
    if idx < 5:
        print(f"  Cycle {idx}: movers={movers}, antis={antis}, freq={dict(Counter(antis))}")

print(f"\nAnti-dim frequency distribution: {dict(anti_dim_counts)}")

# ============================================================
# INVESTIGATION 6: Explicit partner-complement proof attempt
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 6: Why partner(c_t, m_t) is NOT in cycle")
print("="*60)

# partner(c_t, m_t) = c_t ^ (1 << (m_t+2)%4)
# This is a NEIGHBOR of c_t in Q4, specifically along dimension (m_t+2)%4.
#
# The cycle step at t goes c_t -> c_{t+1} = c_t ^ (1 << m_t), along dimension m_t.
# The partner goes along dimension (m_t+2)%4.
# Since m_t != (m_t+2)%4, these are different dimensions.
#
# For partner to be in cycle, partner = c_s for some s.
# Then c_s and c_t differ in exactly bit (m_t+2)%4.
# But c_s is connected to c_{s-1} and c_{s+1} by single bit flips along
# dimensions m_{s-1} and m_s respectively.
#
# Could we prove that if c_s = c_t ^ (1<<(m_t+2)%4), this leads to a TF conflict?

# Test: for each cycle config pair that differ by one bit,
# if both are in the cycle, does this create a TF conflict?
print("\nHamming-1 pairs within cycle:")
for idx, (path, movers) in enumerate(conflict_free[:3]):
    cycle_set = set(path)
    step_map = {path[s]: s for s in range(8)}
    print(f"\nCycle {idx}: movers={movers}")
    for t in range(8):
        c = path[t]
        for d in range(N):
            nbr = c ^ (1 << d)
            if nbr in cycle_set:
                s = step_map[nbr]
                # This is a neighbor in the cycle
                # When d = (movers[t]+2)%4, this would mean partner is IN cycle
                is_anti = (d == (movers[t]+2)%4)
                if is_anti:
                    print(f"  WOULD BE ANTI: step {t} c={c:04b} m={movers[t]} dim={d} -> step {s} c'={nbr:04b} m'={movers[s]}")

print("\n--- Checking: for conflict cycles, do anti-dimension neighbors appear? ---")
anti_in_cycle_count = 0
anti_not_in_cycle_count = 0
for path, movers in conflict_cycles[:100]:
    cycle_set = set(path)
    for t in range(8):
        c = path[t]
        m = movers[t]
        anti = (m+2) % 4
        p = c ^ (1 << anti)
        if p in cycle_set:
            anti_in_cycle_count += 1
        else:
            anti_not_in_cycle_count += 1

print(f"In conflict cycles (sample 100): anti-neighbor in cycle: {anti_in_cycle_count}, not in cycle: {anti_not_in_cycle_count}")

# For ALL conflict-free:
cf_anti_in = 0
cf_anti_out = 0
for path, movers in conflict_free:
    cycle_set = set(path)
    for t in range(8):
        c = path[t]
        m = movers[t]
        anti = (m+2) % 4
        p = c ^ (1 << anti)
        if p in cycle_set:
            cf_anti_in += 1
        else:
            cf_anti_out += 1

print(f"In conflict-free cycles: anti-neighbor in cycle: {cf_anti_in}, not in cycle: {cf_anti_out}")

# ============================================================
# INVESTIGATION 7: What makes conflict-free cycles special?
# ============================================================
print("\n" + "="*60)
print("INVESTIGATION 7: Structural properties of conflict-free cycles")
print("="*60)

# Mover sequences of all conflict-free cycles
print("\nAll conflict-free mover sequences:")
mover_seqs = set()
for idx, (path, movers) in enumerate(conflict_free):
    mover_seqs.add(movers)
    print(f"  {idx}: movers={movers} configs={[f'{c:04b}' for c in path]}")

# Check: Hamming weight distribution
print("\nHamming weight distribution in cycle:")
for idx, (path, movers) in enumerate(conflict_free[:5]):
    weights = [bin(c).count('1') for c in path]
    print(f"  Cycle {idx}: weights={weights}, sorted={sorted(weights)}")

# Bipartite structure: Q4 is bipartite with even/odd weight configs
print("\nBipartite split (even/odd Hamming weight):")
for idx, (path, movers) in enumerate(conflict_free[:5]):
    even_count = sum(1 for c in path if bin(c).count('1') % 2 == 0)
    odd_count = 8 - even_count
    print(f"  Cycle {idx}: even_weight={even_count}, odd_weight={odd_count}")

print("\n=== SUMMARY ===")
print(f"Total fair 8-cycles: {len(all_cycles_list)}")
print(f"Conflict-free: {len(conflict_free)} (× 8 rotations = {len(conflict_free)*8})")
print(f"With conflict: {len(conflict_cycles)}")
