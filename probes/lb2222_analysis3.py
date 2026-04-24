"""Prove partner avoidance from no-TF-conflict + GoodCycle properties."""

def flip(cfg, j):
    return cfg ^ (1 << j)

def get_bit(cfg, j):
    return (cfg >> j) & 1

def left_p(j):
    return (j + 3) % 4

def right_p(j):
    return (j + 1) % 4

def tf_key(cfg, proc):
    return (get_bit(cfg, left_p(proc)), get_bit(cfg, proc), get_bit(cfg, right_p(proc)))

# Check: if partner(c_k, m_k) = c_j is in cycle, then m_j = m_k.
# Then at c_k and c_j, proc m_k fires. They have the same TF context for m_k.
# At c_k, for every non-mover j != m_k: j is non-mover, so f_j(ctx) = c_k[j].
# At c_j, for every non-mover j != m_k: j is non-mover (if m_j = m_k), so f_j(ctx) = c_j[j].
# BUT c_k and c_j differ at bit anti(m_k).
# For j != m_k, anti(m_k) IS in j's TF neighborhood, so ctx differs. No constraint.

# Key insight: if partner(c_k) is in the cycle, and the cycle has no TF conflict,
# what constraints follow?

# Let's try: partner(c_k) = c_j, m_j = m_k =: m.
# c_{k+1} = flip(c_k, m), c_{j+1} = flip(c_j, m).
# c_{k+1} and c_{j+1} differ at anti(m) (same as c_k and c_j).

# At c_{k+1}: mover is m_{k+1}. At c_{j+1}: mover is m_{j+1}.
# c_{k+1} and c_{j+1} have SAME TF context for m (anti(m) not in m's neighborhood).
# proc m is NOT the mover at k+1 (in general), NOT the mover at j+1 (in general).

# If m_{k+1} != m and m_{j+1} != m:
#   proc m is non-mover at both k+1 and j+1 with same TF context.
#   f_m(ctx) = c_{k+1}[m] and f_m(ctx) = c_{j+1}[m]. But c_{k+1}[m] = c_{j+1}[m]
#   (they only differ at anti(m) != m). So consistent. No TF conflict.

# If m_{k+1} = m (mover at k+1) and m_{j+1} != m (non-mover at j+1):
#   Same TF context for m at both. Mover: f_m(ctx) = 1-S. Non-mover: f_m(ctx) = S.
#   TF CONFLICT! Contradiction with no-TF-conflict hypothesis.

# If m_{k+1} != m and m_{j+1} = m: same, TF conflict.

# If m_{k+1} = m and m_{j+1} = m: both movers, same TF context, both give 1-S. Consistent.

# So: if partner(c_k) ∈ cycle, then at c_{k+1} and c_{j+1}:
#   EITHER m_{k+1} = m_{j+1} = m, OR m_{k+1} != m and m_{j+1} != m.

# Case 1: m_{k+1} = m_{j+1} = m. Then by the same argument:
#   partner(c_{k+1}) = c_{j+1} (since c_{k+1}, c_{j+1} differ at anti(m)).
#   By induction: m_t = m for ALL t. Only one proc fires. Contradicts fairness. FALSE.

# Case 2: m_{k+1} != m and m_{j+1} != m.
#   Now c_{k+1} and c_{j+1} differ at anti(m). But m_{k+1} might != m_{j+1}.
#   Let's check: at c_{k+1} and c_{j+1}, proc m_{k+1} is mover at k+1.
#   Is proc m_{k+1} privileged at c_{j+1}?

# For proc m_{k+1} at c_{j+1}: TF context = (c_{j+1}[left(m_{k+1})], c_{j+1}[m_{k+1}], c_{j+1}[right(m_{k+1})]).
# anti(m) is in the TF neighborhood of m_{k+1} (since m_{k+1} != m → anti(m_{k+1}) != anti(m)).
# Actually anti(m) ∈ {left(m_{k+1}), m_{k+1}, right(m_{k+1})} iff anti(m) != anti(m_{k+1}).
# Since m_{k+1} != m, we have anti(m_{k+1}) != anti(m), so anti(m) IS in m_{k+1}'s neighborhood.
# So TF contexts of m_{k+1} at c_{k+1} and c_{j+1} DIFFER (at the bit position of anti(m)).

# This means we can't directly get a TF conflict from m_{k+1} at these two configs.
# But can we get a conflict involving m_{k+1} at c_{k+1} vs c_{j+1}?

# At c_{k+1}: m_{k+1} is mover. At c_{j+1}: m_{j+1} is mover (not m_{k+1}).
# So at c_{j+1}, m_{k+1} is non-mover. But TF contexts differ. No constraint.

# The question is: does the chain eventually lead to a contradiction?

# Let's trace what happens at each step.
# Define p_t = anti(m_t) - 2 mod 4 = m_t. Wait, anti(m) = (m+2)%4.
# The "partner bit" at step t is anti(m_t).

# At step k: partner bit = anti(m). c_k and c_j differ at anti(m).
# At step k+1: c_{k+1} and c_{j+1} still differ at anti(m).
# At step k+2: do they still differ at anti(m)?
#   c_{k+2} = flip(c_{k+1}, m_{k+1}). c_{j+2} = flip(c_{j+1}, m_{j+1}).
#   If m_{k+1} = m_{j+1}: then c_{k+2} and c_{j+2} still differ at anti(m) only.
#   If m_{k+1} != m_{j+1}: then the difference changes!
#     c_{k+2} = c_{k+1} XOR e_{m_{k+1}}. c_{j+2} = c_{j+1} XOR e_{m_{j+1}}.
#     c_{k+2} XOR c_{j+2} = (c_{k+1} XOR c_{j+1}) XOR e_{m_{k+1}} XOR e_{m_{j+1}}
#                          = e_{anti(m)} XOR e_{m_{k+1}} XOR e_{m_{j+1}}.
#     This is a 3-bit (or 1-bit) difference.

# This gets complicated. Let me think about Case 2 differently.

# In Case 2: m_{k+1} != m, m_{j+1} != m.
# We need: at step k+1, both c_{k+1} and c_{j+1} have a single privileged proc.
# At c_{k+1}: the mover is m_{k+1} (unique privileged).
# At c_{j+1}: the mover is m_{j+1} (unique privileged).

# Now: if m_{k+1} = m_{j+1} =: m', then m' != m.
#   proc m' is the mover at both. TF contexts of m' at c_{k+1} and c_{j+1} differ
#   (anti(m) is in m's neighborhood). So different TF contexts, mover at both. No conflict.
#   But: c_{k+1} and c_{j+1} differ at anti(m). partner(c_{k+1}, m') = flip(c_{k+1}, anti(m')).
#   Is c_{j+1} = partner(c_{k+1}, m')? That requires c_{j+1} = flip(c_{k+1}, anti(m')),
#   i.e., anti(m') = anti(m), i.e., m' = m. But m' != m. So c_{j+1} != partner(c_{k+1}, m').
#   Instead c_{j+1} = flip(c_{k+1}, anti(m)).
#   So we have two configs c_{k+1}, c_{j+1} in the cycle, both with mover m',
#   differing at anti(m) (not anti(m')).

#   At step k+2: c_{k+2} = flip(c_{k+1}, m'), c_{j+2} = flip(c_{j+1}, m').
#   Difference: still anti(m). And m_{k+2}, m_{j+2} again either = m or != m...

#   This creates a second "paired" situation with the SAME difference bit anti(m).

# If m_{k+1} != m_{j+1}: then the difference changes. Let's trace.

# Actually, let me just check computationally: for the conflict-free cycles,
# can partner(c_k) be in the cycle while satisfying no-TF-conflict?

# We already know the answer is NO (all 16 conflict-free cycles have partner avoidance).
# The question is WHY.

# Let me check: is Case 2 (m_{k+1} != m, m_{j+1} != m, m_{k+1} = m_{j+1} = m') possible?
# If so, the same pair (c_{k+1}, c_{j+1}) differs at anti(m), with mover m' != m.
# This continues: at step k+2, if m_{k+2} = m_{j+2} = m'' != m:
#   c_{k+2} and c_{j+2} differ at anti(m), mover m'' != m.
# By induction: m_t = m_t' for ALL t (where t' = t shifted by (j-k)).
# But m never appears! That violates fairness (proc m never fires? No, m fires at step k).
# Hmm, m fires at steps k and j but never again?

# Actually: m fires at k (with mover = m) and at j (with mover = m). After that,
# the mover at k+1 is m' != m. At j+1 it's also m'. If m' fires at k+1 and j+1
# and the movers stay synchronized, the sequence is: m, m', m'', ...
# After L steps back to k: all movers repeat. The total mover sequence on the cycle
# visits m at positions k (and j), and non-m movers elsewhere. m fires at k and j
# (2 times). Fairness requires each proc fires at least once.

# How many times does m fire? At step k and step j. Are there other steps where m fires?
# In the synchronized case: m_t = m_{t+(j-k)} for all t.
# If L = cycle length and d = j-k, then m_t = m_{t+d} for all t.
# Proc m fires at steps k, j=k+d, k+2d, k+3d, ... until it wraps around.
# The number of times is L/gcd(L, d)?? No, m only fires when the mover is m.
# m fires at exactly the set of t where m_t = m. The constraint m_t = m_{t+d}
# means this set is closed under adding d mod L.

# In the "all paired, same movers" scenario: the mover sequence has period d = j-k.
# Not period L. So the mover sequence repeats with period dividing d.
# If d | L and the movers repeat with period d, then each proc fires (L/d) times
# the number of times it appears in one period.

# OK this is getting very detailed. Let me just try the clean proof:

# CLAIM: partner(c_k, m_k) ∈ C implies the mover is m_k at every step.
# Proof attempt:
# partner(c_k, m_k) = c_j. m_j = m_k = m (Step 4a).
# c_{k+1} and c_{j+1} differ at anti(m).
# If m_{k+1} = m: continue as before, eventually all movers = m. Contradicts fairness.
# If m_{k+1} ≠ m: then at c_{j+1}, proc m is not the mover (as shown, otherwise TF conflict).
#   So m_{j+1} ≠ m.
#   Now check: is m_{k+1} the unique privileged proc at c_{j+1}?
#   Proc m_{k+1} at c_{j+1}: TF context differs from c_{k+1} (anti(m) is in the neighborhood).
#   We don't know if m_{k+1} is privileged at c_{j+1}.
#   But m_{j+1} is the unique privileged proc at c_{j+1}.

# Actually, I think the cleanest argument is:

# By induction, if all steps have mover m, fairness fails.
# If at some step the mover changes, we get m_{k+1} != m, m_{j+1} != m.
# Now consider the TF context of proc m at c_{k+1}:
#   TF = (c_{k+1}[left(m)], c_{k+1}[m], c_{k+1}[right(m)])
# And at c_{j+1}:
#   TF = (c_{j+1}[left(m)], c_{j+1}[m], c_{j+1}[right(m)])
# These are THE SAME (c_{k+1} and c_{j+1} differ at anti(m) only, which is not in m's nbhd).
# At both steps, m is NON-MOVER. So f_m(TF) = c_{k+1}[m] = c_{j+1}[m]. Consistent.

# Now proc m was mover at step k. TF at step k = (c_k[left(m)], c_k[m], c_k[right(m)]).
# And at step k+1, c_{k+1} = flip(c_k, m). So c_{k+1}[m] = 1 - c_k[m].
# c_{k+1}[left(m)] = c_k[left(m)] (m != left(m) for n >= 3).
# c_{k+1}[right(m)] = c_k[right(m)].
# So TF of m at step k: (L, S, R). TF of m at step k+1: (L, 1-S, R).
# At step k: mover: f_m(L, S, R) = 1-S.
# At step k+1: non-mover: f_m(L, 1-S, R) = 1-S (since value at m is now 1-S and it's preserved).
# Different TF contexts! (L, S, R) vs (L, 1-S, R). No conflict.

# Hmm, this doesn't give a contradiction. The TF contexts differ.

# So the "clean induction" doesn't work directly. The movers can change
# while maintaining no-TF-conflict.

# Let me check: for n=4, can partner(c_k) ∈ cycle EVER happen with no TF conflict?
# The computational answer is NO (all 16 conflict-free cycles have partner avoidance).
# But can this be PROVED without case analysis?

# Let me check all 29008 fair cycles: how many have partner(c_0) in cycle but no TF conflict?
print("Checking all fair cycles for partner-in-cycle + no-TF-conflict...")

def find_all_fair_cycles():
    cycles = []
    def dfs(start, cur, visited, path, fair_mask):
        for proc in range(4):
            nxt = flip(cur, proc)
            new_fair = fair_mask | (1 << proc)
            new_path = path + [(cur, proc)]
            if nxt == start:
                if new_fair == 15:
                    cycles.append(list(new_path))
            elif nxt not in visited and len(path) < 16:
                dfs(start, nxt, visited | {nxt}, new_path, new_fair)
    for s in range(16):
        dfs(s, s, {s}, [], 0)
    seen_canon = set()
    unique = []
    for cyc in cycles:
        L = len(cyc)
        rotations = [tuple(cyc[(r+i) % L] for i in range(L)) for r in range(L)]
        canon = min(rotations)
        if canon not in seen_canon:
            seen_canon.add(canon)
            unique.append(cyc)
    return unique

def has_tf_conflict(cycle):
    tf_map = {}
    for cfg, mover in cycle:
        ctx = tf_key(cfg, mover)
        key = (mover, ctx)
        val = 1 - ctx[1]
        if key not in tf_map:
            tf_map[key] = set()
        tf_map[key].add(val)
        for j in range(4):
            if j == mover:
                continue
            ctx_j = tf_key(cfg, j)
            key_j = (j, ctx_j)
            val_j = ctx_j[1]
            if key_j not in tf_map:
                tf_map[key_j] = set()
            tf_map[key_j].add(val_j)
    for key, vals in tf_map.items():
        if len(vals) > 1:
            return True
    return False

cycles = find_all_fair_cycles()
print(f"Total fair cycles: {len(cycles)}")

# Count cycles with TF conflict
tf_conflict_count = sum(1 for c in cycles if has_tf_conflict(c))
print(f"TF conflict: {tf_conflict_count}")
print(f"No TF conflict: {len(cycles) - tf_conflict_count}")

# For conflict-free cycles, check if partner avoidance MUST hold
conflict_free = [c for c in cycles if not has_tf_conflict(c)]
partner_violation = 0
for cyc in conflict_free:
    cfg_set = {c for c, _ in cyc}
    for cfg, mover in cyc:
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner in cfg_set:
            partner_violation += 1
            break

print(f"Conflict-free with partner violation: {partner_violation}")
print(f"Conflict-free with partner avoidance: {len(conflict_free) - partner_violation}")

# Now let's check: for ALL cycles (including TF-conflicted),
# how many have partner avoidance?
partner_avoid_tf = 0
partner_avoid_notf = 0
for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    has_pa = True
    for cfg, mover in cyc:
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner in cfg_set:
            has_pa = False
            break
    if has_tf_conflict(cyc):
        if has_pa:
            partner_avoid_tf += 1
    else:
        if has_pa:
            partner_avoid_notf += 1

print(f"\nPartner avoidance among TF-conflict cycles: {partner_avoid_tf}/{tf_conflict_count}")
print(f"Partner avoidance among conflict-free cycles: {partner_avoid_notf}/{len(conflict_free)}")

# Check how many TF-conflict cycles also have forced kernel
print("\n=== Alternative: check forced kernel for conflict-free cycles ===")
for i, cyc in enumerate(conflict_free):
    cfg_set = {c for c, _ in cyc}
    complement = set(range(16)) - cfg_set

    tf_map = {}
    for cfg, mover in cyc:
        ctx = tf_key(cfg, mover)
        tf_map[(mover, ctx)] = 1 - ctx[1]
        for j in range(4):
            if j != mover:
                ctx_j = tf_key(cfg, j)
                tf_map[(j, ctx_j)] = ctx_j[1]

    # For complement: count determined TF entries and forced privileged
    total_determined = 0
    forced_priv_count = 0
    for cfg in complement:
        for j in range(4):
            ctx = tf_key(cfg, j)
            key = (j, ctx)
            if key in tf_map:
                total_determined += 1
                if tf_map[key] != ctx[1]:
                    forced_priv_count += 1

    print(f"  Cycle {i}: determined entries in complement = {total_determined}/32, "
          f"forced privileged = {forced_priv_count}")
