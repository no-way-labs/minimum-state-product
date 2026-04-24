"""
Deep dive: WHY partner stays in complement for conflict-free 8-cycles on Q4.

Key finding from v3: all 16 conflict-free cycles have period-4 mover sequences.
Forced complement mover sequence = rotation of reversal of good mover sequence.
"""
from collections import Counter, defaultdict
from itertools import permutations

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
conflict_free = []
conflict_cycles = []

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

for path, movers in all_cycles_list:
    if has_tf_conflict(path, movers):
        conflict_cycles.append((path, movers))
    else:
        conflict_free.append((path, movers))

print(f"Total fair 8-cycles: {len(all_cycles_list)}")
print(f"Conflict-free: {len(conflict_free)}")
print(f"With conflict: {len(conflict_cycles)}")

# ============================================================
# KEY FINDING: All conflict-free have period-4 mover sequences
# ============================================================
print("\n" + "="*60)
print("CHARACTERIZATION: Mover sequences of conflict-free cycles")
print("="*60)

# All mover sequences
cf_mover_seqs = set()
for path, movers in conflict_free:
    cf_mover_seqs.add(movers)

print("Distinct mover sequences (canonical):")
for ms in sorted(cf_mover_seqs):
    # Check: is it a permutation of {0,1,2,3} repeated twice?
    first_half = ms[:4]
    second_half = ms[4:]
    is_perm = sorted(first_half) == [0,1,2,3]
    is_repeat = first_half == second_half
    print(f"  {ms}  perm={is_perm} repeat={is_repeat}")

# How many distinct permutations of {0,1,2,3} appear?
base_perms = set()
for ms in cf_mover_seqs:
    base_perms.add(ms[:4])
print(f"\nDistinct base permutations: {len(base_perms)} of 24 possible")
print("They are:", sorted(base_perms))

# Which permutations are missing?
all_perms = set(permutations(range(4)))
missing = all_perms - base_perms
print(f"Missing permutations: {len(missing)}")
for mp in sorted(missing):
    print(f"  {mp}")

# ============================================================
# KEY ANALYSIS: Why period-4 movers => partner in complement
# ============================================================
print("\n" + "="*60)
print("ANALYSIS: Why period-4 movers guarantee partner in complement")
print("="*60)

# Consider cycle 0: movers = (0,1,2,3,0,1,2,3)
# Starting from config c_0, the cycle is:
# c_0 -> flip(c_0,0) -> flip(flip(c_0,0),1) -> ...
# After 4 steps: all 4 bits have been flipped once => c_4 = c_0 XOR 1111 = complement
# After 8 steps: all 4 bits flipped again => c_8 = c_4 XOR 1111 = c_0 ✓
#
# So for mover sequence (0,1,2,3,0,1,2,3):
# c_0, c_0^1, c_0^3, c_0^7, c_0^15, c_0^14, c_0^12, c_0^8
# = c_0, c_0^0001, c_0^0011, c_0^0111, c_0^1111, c_0^1110, c_0^1100, c_0^1000

# The 8 XOR offsets are: 0000, 0001, 0011, 0111, 1111, 1110, 1100, 1000
# These are the "Gray code" path generated by cycling through dimensions 0,1,2,3.

# The COMPLEMENT consists of configs with XOR offsets NOT in this set:
# 0010, 0100, 0101, 0110, 1001, 1010, 1011, 1101

# For step t with mover m_t, partner = c_t XOR (1 << (m_t+2)%4)
# c_t = c_0 XOR offset_t
# partner = c_0 XOR offset_t XOR (1 << (m_t+2)%4)
# = c_0 XOR (offset_t XOR (1 << (m_t+2)%4))
#
# So partner is in complement iff (offset_t XOR (1<<(m_t+2)%4)) is NOT one of the 8 cycle offsets.

print("\nOffset analysis for mover sequence (0,1,2,3,0,1,2,3):")
offsets = [0]
m_seq = [0,1,2,3,0,1,2,3]
for t in range(7):
    offsets.append(offsets[-1] ^ (1 << m_seq[t]))
offset_set = set(offsets)
print(f"Cycle offsets: {[f'{o:04b}' for o in offsets]}")
print(f"Cycle offset set: {sorted([f'{o:04b}' for o in offset_set])}")

for t in range(8):
    m = m_seq[t]
    anti = (m+2) % 4
    partner_offset = offsets[t] ^ (1 << anti)
    in_cycle = partner_offset in offset_set
    print(f"  Step {t}: offset={offsets[t]:04b}, m={m}, anti={anti}, partner_offset={partner_offset:04b}, in_cycle={in_cycle}")

# ============================================================
# GENERAL: For any permutation pi, the offsets form a generalized Gray code
# ============================================================
print("\n" + "="*60)
print("GENERAL: Offset structure for all 16 conflict-free mover sequences")
print("="*60)

for ms in sorted(cf_mover_seqs):
    base = ms[:4]
    offsets = [0]
    for t in range(7):
        offsets.append(offsets[-1] ^ (1 << ms[t]))
    offset_set = set(offsets)

    all_partners_out = True
    for t in range(8):
        m = ms[t]
        anti = (m+2) % 4
        po = offsets[t] ^ (1 << anti)
        if po in offset_set:
            all_partners_out = False

    # Check: what's the XOR between consecutive offsets?
    # offset_{t+1} = offset_t XOR (1 << m_t)
    # partner_offset_t = offset_t XOR (1 << (m_t+2)%4)

    # KEY: partner_offset_t = offset_t XOR (1 << anti_t)
    # For partner to be IN cycle, we'd need offset_t XOR (1<<anti_t) = offset_s for some s
    # i.e., offset_t XOR offset_s = (1 << anti_t) -- they differ in exactly bit anti_t

    # The offsets form a path on Q4 visiting 8 vertices.
    # The partner operation at step t tries to reach the neighbor along dimension anti_t.
    # This neighbor is NOT on the path iff the path does NOT include that Q4 edge.

    print(f"  Movers {base}: partners_all_outside={all_partners_out}")

# ============================================================
# THE KEY INSIGHT: Which Q4 edges are used by the cycle?
# ============================================================
print("\n" + "="*60)
print("KEY INSIGHT: Edge structure of cycle vs partner edges")
print("="*60)

for idx, ms in enumerate(sorted(cf_mover_seqs)):
    if idx > 3:
        break
    offsets = [0]
    for t in range(7):
        offsets.append(offsets[-1] ^ (1 << ms[t]))

    # Edges used by cycle: (offset_t, offset_{t+1}) along dimension m_t
    cycle_edges = set()
    for t in range(8):
        a = offsets[t]
        b = offsets[(t+1) % 8]
        dim = ms[t]
        edge = (min(a,b), max(a,b), dim)
        cycle_edges.add(edge)

    # Partner edges: (offset_t, offset_t ^ (1<<anti_t)) along dimension anti_t
    partner_edges = set()
    for t in range(8):
        a = offsets[t]
        anti = (ms[t]+2) % 4
        b = a ^ (1 << anti)
        dim = anti
        edge = (min(a,b), max(a,b), dim)
        partner_edges.add(edge)

    overlap = cycle_edges & partner_edges
    print(f"\nMovers {ms[:4]}:")
    print(f"  Cycle edges ({len(cycle_edges)}):")
    for e in sorted(cycle_edges):
        print(f"    {e[0]:04b} -- {e[1]:04b} dim={e[2]}")
    print(f"  Partner edges ({len(partner_edges)}):")
    for e in sorted(partner_edges):
        in_cycle = e in cycle_edges
        print(f"    {e[0]:04b} -- {e[1]:04b} dim={e[2]}  {'*** IN CYCLE' if in_cycle else ''}")
    print(f"  Overlap: {len(overlap)} edges")

# ============================================================
# THE REAL KEY: partner offset never equals any cycle offset
# ============================================================
print("\n" + "="*60)
print("ALGEBRAIC ANALYSIS: Why partner offset avoids cycle offsets")
print("="*60)

# For mover perm π = (π_0, π_1, π_2, π_3), the offsets are:
# o_0 = 0
# o_1 = e_{π_0}
# o_2 = e_{π_0} + e_{π_1}
# o_3 = e_{π_0} + e_{π_1} + e_{π_2}
# o_4 = e_{π_0} + e_{π_1} + e_{π_2} + e_{π_3} = 1111
# o_5 = 1111 + e_{π_0} = complement of e_{π_0}
# o_6 = 1111 + e_{π_0} + e_{π_1}
# o_7 = 1111 + e_{π_0} + e_{π_1} + e_{π_2}
# (all additions mod 2)
#
# Offsets: {prefix sums of π} ∪ {1111 XOR prefix sums of π}
# = S ∪ (1111 XOR S) where S = {0, e_{π_0}, e_{π_0}+e_{π_1}, e_{π_0}+e_{π_1}+e_{π_2}}
#
# Partner offset at step t: o_t XOR e_{(π_{t%4}+2)%4}
# = o_t XOR e_{anti(π_{t%4})}
#
# For t < 4: o_t = sum of first t basis vectors in π order
# anti(π_t) = (π_t + 2) % 4

# Let's work this out symbolically
print("\nSymbolic offset table:")
for perm in sorted(base_perms):
    S = [0]
    for i in range(3):
        S.append(S[-1] ^ (1 << perm[i]))
    # Full offsets: S[0..3] and S[0..3] XOR 15
    all_offsets = S + [s ^ 15 for s in S]

    print(f"\n  π = {perm}")
    print(f"  S = {[f'{s:04b}' for s in S]}")
    print(f"  S^1111 = {[f'{s^15:04b}' for s in S]}")

    # Check partner offsets
    mseq = list(perm) + list(perm)
    for t in range(8):
        o = all_offsets[t]
        anti = (mseq[t] + 2) % 4
        po = o ^ (1 << anti)

        # Express po in terms of S
        # For t < 4: o = S[t], po = S[t] ^ e_{anti(π_t)}
        # For t >= 4: o = S[t-4] ^ 1111, po = S[t-4] ^ 1111 ^ e_{anti(π_{t-4})}

        in_S = po in S
        in_S_comp = (po ^ 15) in S
        in_offsets = po in set(all_offsets)

        if t < 4:
            print(f"    t={t}: S[{t}]={o:04b} ^ e_{anti}={1<<anti:04b} = {po:04b}  inS={in_S} inS^15={in_S_comp} inOffsets={in_offsets}")
        else:
            print(f"    t={t}: S[{t-4}]^F={o:04b} ^ e_{anti}={1<<anti:04b} = {po:04b}  inS={in_S} inS^15={in_S_comp} inOffsets={in_offsets}")

# ============================================================
# CRITICAL: Why does S[t] ^ e_{anti(π_t)} avoid S and S^F?
# ============================================================
print("\n" + "="*60)
print("CRITICAL: Why S[t] ^ e_{anti(π_t)} avoids S ∪ (S^F)")
print("="*60)

# S = {0, e_{π_0}, e_{π_0}+e_{π_1}, e_{π_0}+e_{π_1}+e_{π_2}}
# These are prefix sums of the permutation.
#
# S[t] ^ e_{anti(π_t)} means: take the t-th prefix sum, then flip bit anti(π_t).
# anti(π_t) = (π_t + 2) % 4 is the OPPOSITE proc on the ring.
#
# S contains prefix sums — these have bits set for {π_0, ..., π_{t-1}}.
# The partner flips bit anti(π_t), which is the bit OPPOSITE to π_t.
#
# Claim: anti(π_t) is NEITHER in {π_0,...,π_{t-1}} NOR is it π_t.
# Wait, that's not always true. Let π = (0,1,2,3). Then anti(π_0)=anti(0)=2.
# {π_0,...,π_{-1}} = {} (empty for t=0). And 2 ≠ 0. So anti(π_0) ∉ {π_0}.
# But anti(π_t) could be in {π_0,...,π_{t-1}}.
# π = (0,1,2,3), t=2: anti(π_2)=anti(2)=0. {π_0,π_1}={0,1}. 0 ∈ {0,1}! So yes.

# Let me think about this differently.
# S[t] has bits set for {π_0,...,π_{t-1}} (the first t dimensions).
# S[t] ^ e_d where d=anti(π_t): this flips bit d.
#
# For this to equal S[s] (some other prefix sum), we need:
# S[t] ^ e_d = S[s]
# => S[t] ^ S[s] = e_d
# => exactly one bit differs between S[t] and S[s].
#
# S[t] ^ S[s] = e_{π_min(t,s)} ^ e_{π_{min(t,s)+1}} ^ ... ^ e_{π_{max(t,s)-1}}
# (the XOR of the bits added between steps min and max)
# This equals e_d iff |{s,...,t-1}| = 1 AND the single bit is d.
# i.e., |t-s| = 1 AND π_{min(t,s)} = d = anti(π_t).
#
# Case s = t+1: π_t = d = anti(π_t) = (π_t+2)%4 => π_t = π_t + 2 mod 4, impossible.
# Case s = t-1: π_{t-1} = d = anti(π_t) = (π_t+2)%4.
#
# So S[t]^e_d = S[s] only if s=t-1 and π_{t-1} = (π_t+2)%4.
# i.e., consecutive movers are antipodal.
#
# For s and t differing by > 1: S[t]^S[s] has multiple bits set, so ≠ e_d.
# Wait — that's wrong. S[t]^S[s] for |t-s|>1 has |t-s| bits set (since π is a permutation,
# each step adds a DIFFERENT dimension). So |t-s| > 1 means ≥ 2 bits differ.
# And e_d has exactly 1 bit. So S[t]^e_d ≠ S[s] when |t-s| > 1. ✓

# Also need to check S[t]^e_d ∉ S^F = {s^1111 : s ∈ S}
# S[t]^e_d = S[s]^1111
# => S[t]^S[s] = e_d ^ 1111 = e_d ^ e_0 ^ e_1 ^ e_2 ^ e_3
# => S[t]^S[s] has exactly 3 bits set (flip d in 1111).
# S[t]^S[s] has |t-s| bits set (for s,t in 0..3).
# This equals 3 iff |t-s| = 3, i.e. {s,t} = {0,3}.
# Then S[0]^S[3] = e_{π_0}^e_{π_1}^e_{π_2} and we need this = e_0^e_1^e_2^e_3 ^ e_d
# = all bits except d. Since {π_0,π_1,π_2} = {0,1,2,3}\{π_3}, we get
# S[0]^S[3] = e_{π_0}^e_{π_1}^e_{π_2} = all bits except e_{π_3} = 1111 ^ e_{π_3}.
# We need this = 1111 ^ e_d where d = anti(π_t).
# If t=0: d=anti(π_0), need 1111^e_{π_3} = 1111^e_{anti(π_0)}, i.e. π_3 = anti(π_0)=(π_0+2)%4.
# If t=3: d=anti(π_3), need 1111^e_{π_3} = 1111^e_{anti(π_3)}, i.e. π_3 = anti(π_3)=(π_3+2)%4, impossible.

# So S[t]^e_{anti(π_t)} ∈ S ∪ S^F requires:
# (A) s=t-1 and π_{t-1} = (π_t+2)%4 [partner offset = S[t-1] ∈ S], or
# (B) t=0, s=3, and π_3 = (π_0+2)%4 [partner offset = S[3]^F ∈ S^F]

# Condition (A): consecutive movers are ANTIPODAL
# Condition (B): first and last movers in half are ANTIPODAL

# For the conflict-free cycles, these conditions must NEVER hold!
# So: no two consecutive movers (in the period-4 pattern) are antipodal,
# AND π_3 ≠ (π_0+2)%4.

print("\nChecking antipodal conditions for all permutations:")
for perm in sorted(all_perms):
    has_consec_anti = False
    for t in range(1, 4):
        if perm[t-1] == (perm[t]+2) % 4:
            has_consec_anti = True
    has_wrap_anti = (perm[3] == (perm[0]+2) % 4)

    is_cf = perm in base_perms
    blocked_by_A = has_consec_anti
    blocked_by_B = has_wrap_anti

    status = "CF" if is_cf else "CONFLICT"
    print(f"  π={perm}: consec_anti={blocked_by_A}, wrap_anti={blocked_by_B}, actual={status}, predicted_CF={not blocked_by_A and not blocked_by_B}")

# ============================================================
# VERIFY: Does the algebraic condition perfectly separate?
# ============================================================
print("\n" + "="*60)
print("VERIFICATION: Algebraic condition matches exactly?")
print("="*60)

predicted_cf = set()
for perm in all_perms:
    has_consec_anti = any(perm[t-1] == (perm[t]+2)%4 for t in range(1,4))
    has_wrap_anti = (perm[3] == (perm[0]+2)%4)
    if not has_consec_anti and not has_wrap_anti:
        predicted_cf.add(perm)

print(f"Predicted conflict-free perms: {len(predicted_cf)}")
print(f"Actual conflict-free perms: {len(base_perms)}")
print(f"Match: {predicted_cf == base_perms}")

if predicted_cf != base_perms:
    print(f"  In predicted but not actual: {predicted_cf - base_perms}")
    print(f"  In actual but not predicted: {base_perms - predicted_cf}")

# ============================================================
# FORCED SUCCESSOR: Why it stays in complement
# ============================================================
print("\n" + "="*60)
print("FORCED SUCCESSOR: Why flip(partner, m) stays in complement")
print("="*60)

# partner(c_t, m_t) = c_t ^ e_{anti(m_t)} has offset o_t ^ e_{anti(π_{t%4})}
# forced_succ = partner ^ e_{m_t} has offset o_t ^ e_{anti(π_{t%4})} ^ e_{π_{t%4}}
# = o_t ^ e_{(π_{t%4}+2)%4} ^ e_{π_{t%4}}
#
# For binary, e_a ^ e_b where a=(j+2)%4 and b=j: this flips bits j and (j+2)%4.
# So forced_succ offset = o_t ^ e_j ^ e_{(j+2)%4} where j = π_{t%4}.
#
# This is a 2-bit flip. We need to check this is NOT in S ∪ S^F.
# Similar analysis: need o_t ^ (e_j ^ e_{j+2}) ≠ S[s] and ≠ S[s]^F for any s.

print("\nForced successor offset analysis:")
for perm in sorted(list(base_perms)[:4]):
    S = [0]
    for i in range(3):
        S.append(S[-1] ^ (1 << perm[i]))
    all_offsets = set(S + [s ^ 15 for s in S])

    print(f"\n  π = {perm}")
    mseq = list(perm) + list(perm)
    for t in range(8):
        o = S[t%4] if t < 4 else S[t%4] ^ 15
        j = mseq[t]
        anti_j = (j+2) % 4
        fs_offset = o ^ (1 << j) ^ (1 << anti_j)
        in_offsets = fs_offset in all_offsets
        print(f"    t={t}: offset={o:04b} ^ e_{j} ^ e_{anti_j} = {fs_offset:04b}  inOffsets={in_offsets}")

# ============================================================
# SUMMARY
# ============================================================
print("\n" + "="*60)
print("SUMMARY OF MECHANISM")
print("="*60)
print("""
1. Every conflict-free fair 8-cycle on Q4 has a PERIOD-4 mover sequence:
   movers = (π_0, π_1, π_2, π_3, π_0, π_1, π_2, π_3)
   where π is a permutation of {0,1,2,3}.

2. The cycle configs are offsets S ∪ (S ⊕ 1111) where
   S = {0, e_{π_0}, e_{π_0}⊕e_{π_1}, e_{π_0}⊕e_{π_1}⊕e_{π_2}}
   (prefix sums of the permutation).

3. Partner(c_t, m_t) has offset o_t ⊕ e_{anti(π_{t%4})} where anti(j) = (j+2)%4.
   This is NOT in S ∪ (S⊕F) iff:
   (A) No consecutive pair (π_{t-1}, π_t) are antipodal: π_{t-1} ≠ (π_t+2)%4
   (B) First and last aren't antipodal: π_3 ≠ (π_0+2)%4

4. Forced successor has offset o_t ⊕ e_{π_t} ⊕ e_{anti(π_t)}.
   This is a 2-bit flip (mover + anti-mover). Same analysis shows it avoids S ∪ (S⊕F).

5. The INVARIANT: no two cyclically consecutive movers in the period-4 pattern are antipodal.
   "Antipodal" means j and (j+2)%4: {0,2} or {1,3}.
""")

# Count: 24 perms, how many avoid all consecutive antipodal pairs (cyclically)?
count = 0
for perm in all_perms:
    ok = True
    for t in range(4):
        if perm[t] == (perm[(t+1)%4] + 2) % 4:
            ok = False
            break
    if ok:
        count += 1
print(f"Permutations with no cyclically-consecutive antipodal pair: {count}")
print(f"Matches conflict-free count: {count == len(base_perms)}")
