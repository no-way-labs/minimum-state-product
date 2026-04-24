"""
Final verification and forced-successor algebraic proof.
"""
from collections import Counter
from itertools import permutations

N = 4

def bit(c, j):
    return (c >> j) & 1

def flip(c, j):
    return c ^ (1 << j)

# ============================================================
# Part 1: Verify condition (A)+(B) vs cyclic-no-antipodal are equivalent
# ============================================================
print("="*60)
print("Part 1: Condition equivalence check")
print("="*60)

all_perms = list(permutations(range(4)))

for perm in all_perms:
    # Condition from algebra:
    # (A) no t in {1,2,3} with π_{t-1} = (π_t+2)%4
    # (B) π_3 ≠ (π_0+2)%4
    condA = any(perm[t-1] == (perm[t]+2)%4 for t in range(1,4))
    condB = (perm[3] == (perm[0]+2)%4)
    blocked_AB = condA or condB

    # Cyclic no-antipodal: no cyclically consecutive pair is antipodal
    # i.e., for all t in {0,1,2,3}: π_t ≠ (π_{(t+1)%4}+2)%4
    # equivalently: |π_t - π_{(t+1)%4}| ≠ 2 mod 4
    cyclic_anti = any(perm[t] == (perm[(t+1)%4]+2)%4 for t in range(4))

    if blocked_AB != cyclic_anti:
        print(f"  MISMATCH at π={perm}: AB={blocked_AB}, cyclic={cyclic_anti}")

print("Conditions (A)+(B) and cyclic-no-antipodal are equivalent: checked all 24 perms")

# ============================================================
# Part 2: Complete forced-successor algebraic analysis
# ============================================================
print("\n" + "="*60)
print("Part 2: Forced successor algebraic proof")
print("="*60)

# Forced successor offset = o_t ^ e_{π_t} ^ e_{anti(π_t)} where anti(j)=(j+2)%4
# For t in {0,...,3}: o_t = S[t] = prefix sum of first t dimensions
# For t in {4,...,7}: o_t = S[t-4] ^ F where F = 1111
#
# fs_offset = o_t ^ e_{π_t} ^ e_{anti(π_t)}
# = o_t ^ (e_{π_t} ^ e_{(π_t+2)%4})
#
# Note: e_j ^ e_{(j+2)%4} flips two bits that are 2 apart on the ring.
# For j ∈ {0,1,2,3}: e_j ^ e_{(j+2)%4} ∈ {0101, 1010}
# Specifically: if j ∈ {0,2}, e_j^e_{j+2} = 0101; if j ∈ {1,3}, = 1010.
# So the 2-bit flip is always either 0101 (=5) or 1010 (=10).
#
# fs_offset = o_t ^ D where D ∈ {0101, 1010}
#
# For this to be in S ∪ S^F:
# Case 1: fs_offset = S[s] for some s
#   o_t ^ D = S[s]
#   For t < 4: S[t] ^ D = S[s], so S[t] ^ S[s] = D
#   S[t]^S[s] has |t-s| bits set (all different dims since π is a perm)
#   D has exactly 2 bits set
#   So |t-s| = 2, and the two dims must form an antipodal pair.
#
# Case 2: fs_offset = S[s] ^ F for some s
#   o_t ^ D = S[s] ^ F
#   For t < 4: S[t] ^ D = S[s] ^ F, so S[t] ^ S[s] = D ^ F = D ^ 1111
#   D ^ 1111 has 2 bits set (complement of 2 bits in {0,1,2,3} that D covers)
#   So again |t-s| = 2.
#
# Let's verify: when |t-s| = 2, which dims appear?

print("\nCase analysis for |t-s|=2:")
for perm in sorted(all_perms):
    # For each pair (t,s) with |t-s|=2 and t,s ∈ {0,1,2,3}:
    # (t,s) ∈ {(0,2),(2,0),(1,3),(3,1)}
    # S[t]^S[s] = XOR of dims π_{min(t,s)}, π_{min(t,s)+1}
    for t, s in [(0,2), (1,3)]:
        dims = {perm[t], perm[t+1]}  # The two dims in between
        diff = (1 << perm[t]) ^ (1 << perm[t+1])
        is_anti_pair = (abs(perm[t]-perm[t+1]) == 2) or (abs(perm[t]-perm[t+1]) == 2)
        # D = 0101 or 1010, which means antipodal pairs {0,2} or {1,3}
        # S[t]^S[s] = e_{π_t} ^ e_{π_{t+1}}
        # This equals D iff {π_t, π_{t+1}} is an antipodal pair
        is_D = diff in (5, 10)  # 0101 or 1010
        # S[t]^S[s] ^ F has same structure but for the OTHER pair
        is_DF = (diff ^ 15) in (5, 10)

        if perm == (0,1,2,3) or perm == (0,2,1,3):
            print(f"  π={perm}, (t,s)=({t},{s}): dims={dims}, S[t]^S[s]={diff:04b}, isD={is_D}, isDF={is_DF}")

print("\nSo forced successor o_t ^ D avoids S ∪ S^F iff:")
print("  For ALL consecutive dim-pairs in π, they don't form an antipodal pair.")
print("  Specifically: {π_0,π_1}, {π_1,π_2}, {π_2,π_3} are NOT antipodal.")
print("  Plus the F-XOR case adds: {π_0,π_1}, {π_1,π_2} for the cross-half check.")

# Actually let me just verify computationally that the cyclic-no-antipodal condition
# is exactly what's needed for BOTH partner and forced successor to avoid the cycle.

print("\n" + "="*60)
print("Part 3: Verify cyclic-no-antipodal is exact for both partner AND forced successor")
print("="*60)

for perm in sorted(all_perms):
    mseq = list(perm) * 2
    # Compute offsets
    S = [0]
    for i in range(3):
        S.append(S[-1] ^ (1 << perm[i]))
    offsets = S + [s ^ 15 for s in S]
    offset_set = set(offsets)

    # Check partner
    partner_ok = True
    for t in range(8):
        anti = (mseq[t] + 2) % 4
        po = offsets[t] ^ (1 << anti)
        if po in offset_set:
            partner_ok = False

    # Check forced successor
    fs_ok = True
    for t in range(8):
        j = mseq[t]
        anti = (j + 2) % 4
        fso = offsets[t] ^ (1 << j) ^ (1 << anti)
        if fso in offset_set:
            fs_ok = False

    # Cyclic condition
    cyclic_ok = not any(perm[t] == (perm[(t+1)%4]+2)%4 for t in range(4))

    if partner_ok != cyclic_ok or fs_ok != cyclic_ok:
        print(f"  π={perm}: cyclic_ok={cyclic_ok} partner_ok={partner_ok} fs_ok={fs_ok}")

print("All 24 perms: cyclic-no-antipodal <=> partner avoids cycle <=> forced-succ avoids cycle")

# ============================================================
# Part 4: Why forced successor also stays in complement (PROOF)
# ============================================================
print("\n" + "="*60)
print("Part 4: Forced successor proof sketch")
print("="*60)

# The forced successor offset is o_t ^ D where D = e_{π_t} ^ e_{anti(π_t)}.
# D is ALWAYS one of {0101, 1010} — the two "diagonal" elements of Z_2^4.
# These correspond to the two antipodal pairs: {0,2} -> 0101, {1,3} -> 1010.
#
# For fs_offset ∈ S: need S[t] ^ S[s] = D for some s, requires |t-s|=2
#   and {π_min, π_{min+1}} forms the same antipodal pair as {π_t, anti(π_t)}.
#   Since anti(π_t) = (π_t+2)%4, the pair is always {π_t, (π_t+2)%4}.
#   For |t-s|=2 with s>t: S[t]^S[s] involves dims {π_t, π_{t+1}}.
#   So we need {π_t, π_{t+1}} = {π_t, (π_t+2)%4}, i.e. π_{t+1} = (π_t+2)%4.
#   This is exactly the "consecutive antipodal" condition!
#
# For fs_offset ∈ S^F: similar analysis with 3-bit differences.
#   Need S[t]^S[s]^F = D, i.e. S[t]^S[s] = D^F.
#   D^F also has 2 bits — the OTHER antipodal pair.
#   |t-s| = 2, and {π_min, π_{min+1}} = other antipodal pair.
#   Since {π_t, anti(π_t)} and {π_min, π_{min+1}} are the only possibilities,
#   and D^F uses the complementary pair... let me check.

for j in range(4):
    D = (1 << j) ^ (1 << ((j+2)%4))
    DF = D ^ 15
    print(f"  j={j}: D={D:04b}, D^F={DF:04b}")
    # D = e_j ^ e_{(j+2)%4}, D^F = e_k ^ e_{(k+2)%4} where {k,(k+2)%4} = other pair

# So D^F for j∈{0,2} is 1010, and for j∈{1,3} is 0101.
# In both cases D^F corresponds to the OTHER antipodal pair.
#
# For fs_offset ∈ S^F with |t-s|=2:
# {π_min, π_{min+1}} must form the OTHER antipodal pair from {π_t, anti(π_t)}.
# This is a different condition from (A).
#
# But does cyclic-no-antipodal also block this? YES:
# If {π_t, π_{t+1}} form ANY antipodal pair (either the same or different),
# then consecutive movers are antipodal, which is blocked.

# Verify: the 8 surviving permutations have NO consecutive antipodal pair at ALL
print("\nSurviving permutations — no consecutive antipodal pair (any pair):")
for perm in sorted(all_perms):
    cyclic_ok = not any(abs(perm[t] - perm[(t+1)%4]) == 2 for t in range(4))
    if cyclic_ok:
        print(f"  {perm}")

# ============================================================
# Part 5: Structure of the 8 surviving permutations
# ============================================================
print("\n" + "="*60)
print("Part 5: Structure of the 8 conflict-free permutations")
print("="*60)

# The condition is: no cyclically adjacent pair in π is ring-antipodal.
# Ring-antipodal on Z_4: {0,2} and {1,3}.
# So in the cyclic permutation π_0 π_1 π_2 π_3, no adjacent elements
# (including π_3,π_0 wrap) can be from the same antipodal pair.

# This is equivalent to: the permutation, viewed as a cyclic sequence,
# ALTERNATES between the two antipodal pairs {0,2} and {1,3}.
# i.e., π_t and π_{t+1} are always from DIFFERENT pairs.

print("Alternation check:")
for perm in sorted(all_perms):
    # Classify each element: pair A = {0,2}, pair B = {1,3}
    classes = ['A' if p in {0,2} else 'B' for p in perm]
    alternates = all(classes[t] != classes[(t+1)%4] for t in range(4))
    cyclic_ok = not any(abs(perm[t] - perm[(t+1)%4]) == 2 for t in range(4))
    if cyclic_ok or alternates:
        print(f"  π={perm}: classes={''.join(classes)}, alternates={alternates}, conflict_free={cyclic_ok}")

# These should be the same!
print("\nAlternation == conflict-free for all 24 perms:")
match = True
for perm in all_perms:
    classes = ['A' if p in {0,2} else 'B' for p in perm]
    alternates = all(classes[t] != classes[(t+1)%4] for t in range(4))
    cyclic_ok = not any(abs(perm[t] - perm[(t+1)%4]) == 2 for t in range(4))
    if alternates != cyclic_ok:
        match = False
        print(f"  MISMATCH: π={perm}")
print(f"Match: {match}")

# Count: 4 positions, must alternate ABAB or BABA.
# For ABAB: 2 choices for A-slot × 2 choices for A-slot = 2×1 × 2×1 = 4 each
# Total: 2 patterns (ABAB, BABA) × 2! × 2! = 2 × 2 × 2 = 8. ✓

# ============================================================
# Part 6: Forced complement mover relationship (exact formula)
# ============================================================
print("\n" + "="*60)
print("Part 6: Complement forced mover relationship")
print("="*60)

# We showed: forced mover sequence = rotation of reversal.
# Let me find the exact relationship.

# Build all data
for start in range(16):
    pass  # skip, already computed

# Recompute
all_cycles_set = set()
all_cycles_list = []

def canonical(path, movers):
    n = len(path)
    best = None
    for i in range(n):
        candidate = (path[i:] + path[:i], movers[i:] + movers[:i])
        if best is None or candidate < best:
            best = candidate
    return best

for start in range(16):
    def dfs(path, visited, movers, fire_count, start_config):
        if len(path) == 8:
            c = path[-1]
            for j in range(4):
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
        for j in range(4):
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

def has_tf_conflict(path, movers):
    for j in range(4):
        ctx_m = set()
        ctx_nm = set()
        for step in range(8):
            c = path[step]
            m = movers[step]
            ctx = (bit(c,(j-1)%4), bit(c,j), bit(c,(j+1)%4))
            if m == j:
                ctx_m.add(ctx)
            else:
                ctx_nm.add(ctx)
        if ctx_m & ctx_nm:
            return True
    return False

conflict_free = [(p,m) for p,m in all_cycles_list if not has_tf_conflict(p,m)]

print(f"Conflict-free cycles: {len(conflict_free)}")

for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    complement = set(range(16)) - cycle_set

    # Build forced map
    forced_map = {}
    for step in range(8):
        c = path[step]
        m = movers[step]
        p = c ^ (1 << ((m+2)%4))
        fs = p ^ (1 << m)
        forced_map[p] = (fs, m)

    # Trace forced cycle
    start = min(complement)
    cur = start
    forced_path = [cur]
    forced_movers = []
    for _ in range(8):
        nxt, m = forced_map[cur]
        forced_movers.append(m)
        if nxt == start and len(forced_path) == 8:
            break
        forced_path.append(nxt)
        cur = nxt

    # Compare mover sequences
    gm = list(movers)
    fm = forced_movers

    # What transformation maps gm -> fm?
    # Good = (π_0,π_1,π_2,π_3,π_0,π_1,π_2,π_3)
    # Forced = (σ_0,...,σ_7) — check if σ = reversed and rotated good
    # Also check: σ_t = anti(π_{7-t})? or σ_t = anti(π_{...})?

    # Check: is forced = rotation of (anti(π_3), anti(π_2), anti(π_1), anti(π_0), ...)?
    anti_rev = [(m+2)%4 for m in reversed(gm[:4])] * 2
    is_anti_rev_match = False
    for off in range(8):
        test = anti_rev[off:] + anti_rev[:off]
        if test[:8] == fm:
            is_anti_rev_match = True
            break

    # Simpler: check forced mover at position t
    print(f"  Cycle {idx}: good_base={movers[:4]}, forced_base={fm[:4]}")

# All forced mover bases:
print("\nGood base -> Forced base mapping:")
for idx, (path, movers) in enumerate(conflict_free):
    cycle_set = set(path)
    forced_map = {}
    for step in range(8):
        c = path[step]
        m = movers[step]
        p = c ^ (1 << ((m+2)%4))
        fs = p ^ (1 << m)
        forced_map[p] = (fs, m)

    start = min(set(range(16)) - cycle_set)
    cur = start
    fm = []
    for _ in range(8):
        nxt, m = forced_map[cur]
        fm.append(m)
        cur = nxt

    gb = movers[:4]
    fb = tuple(fm[:4])
    print(f"  {gb} -> {fb}")

    # Check: is fb = (anti(gb[2]), anti(gb[1]), anti(gb[0]), anti(gb[3]))?
    # Or some other rearrangement?
    # Let's be systematic: try all mappings
    anti = tuple((m+2)%4 for m in gb)
    rev = tuple(reversed(gb))
    anti_rev = tuple((m+2)%4 for m in reversed(gb))

    # Check various transformations
    for name, candidate in [
        ("anti", anti),
        ("rev", rev),
        ("anti_rev", anti_rev),
        ("rev_shift1", rev[1:]+rev[:1]),
        ("rev_shift2", rev[2:]+rev[:2]),
        ("rev_shift3", rev[3:]+rev[:3]),
        ("anti_rev_s1", anti_rev[1:]+anti_rev[:1]),
        ("anti_rev_s2", anti_rev[2:]+anti_rev[:2]),
        ("anti_rev_s3", anti_rev[3:]+anti_rev[:3]),
    ]:
        if candidate == fb:
            print(f"    MATCH: {name}")
