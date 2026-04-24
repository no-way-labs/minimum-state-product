"""Check: when partner(c_k, m_k) = c_j, is m_j always != m_k?"""

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

cycles = find_all_fair_cycles()

same_mover_count = 0
diff_mover_count = 0
same_mover_but_no_conflict = 0

for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    cfg_to_idx = {c: i for i, (c, _) in enumerate(cyc)}
    L = len(cyc)

    for k, (cfg, mover) in enumerate(cyc):
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner in cfg_set:
            j = cfg_to_idx[partner]
            _, mover_j = cyc[j]
            if mover_j == mover:
                same_mover_count += 1
            else:
                diff_mover_count += 1

print(f"Partner in cycle with SAME mover: {same_mover_count}")
print(f"Partner in cycle with DIFF mover: {diff_mover_count}")

# Hmm wait - Step 4a claimed m_j = m_k because partner has proc m_k privileged
# and unique_privileged forces m_j = m_k.
# But that assumes the cycle has unique_privileged at partner!
# Actually, the GoodCycle has unique_privileged at ALL its configs.
# partner is in the cycle, so it's one of the cycle configs.
# So unique_privileged holds at partner.
# Since proc m_k is privileged at partner (by Lemma 2),
# and the unique privileged proc at c_j is m_j,
# we must have m_j = m_k.

# But the computation shows DIFFERENT movers! Let me re-examine.

# Wait -- unique_privileged says there exists a UNIQUE privileged proc.
# Lemma 2 says proc m_k IS privileged at partner.
# But `mover_j` is the proc that actually fires (from gc.closed).
# gc.closed says: ∃ i, privileged sys c_j i ∧ next = move sys c_j i.
# unique_privileged says: ∃! i, privileged sys c_j i.
# So: the unique privileged proc at c_j IS m_j. And proc m_k is also privileged at c_j.
# By uniqueness: m_j = m_k.

# But the computation says otherwise! Let me check more carefully.
# Maybe the issue is that these cycles DON'T satisfy unique_privileged.

# Check: for each cycle, does each config have a unique privileged proc
# (i.e., exactly one proc has f(L,S,R) != S)?
# But we don't know f! The cycle just specifies (config, chosen mover).
# unique_privileged is a property of the SYSTEM, not of the cycle alone.

# The point is: in a fair cycle on Q4, the mover at each step is CHOSEN.
# The cycle defines which proc fires at each step.
# unique_privileged constrains the SYSTEM such that at each good config,
# exactly one proc CAN fire. But the cycle just says which proc DOES fire.

# So: Lemma 2 says proc m_k is privileged at partner(c_k) for ANY system
# where m_k is privileged at c_k. But for the cycle to have partner(c_k) = c_j,
# AND unique_privileged at c_j, the SYSTEM must have m_j = m_k.

# The DFS finds cycles where multiple procs COULD fire at the same config.
# The GoodCycle constraint says only ONE proc CAN fire.
# So not all fair Q4 cycles correspond to GoodCycles.

# In the DFS analysis, the "cycles" allow any proc to fire at any step.
# The TF conflict check looks at ALL constraints simultaneously.
# The GoodCycle constraint (unique_privileged) is ADDITIONAL.

# So the proof should be:
# Given a GoodCycle gc (with unique_privileged),
# if partner(c_k, m_k) = c_j, then m_j = m_k (by Lemma 2 + uniqueness).
# This gives a TF conflict or fairness violation.

# But computationally, for cycles with unique privileged (from the DFS),
# the partner-in-cycle case might not arise at all, because
# unique_privileged eliminates most cycles.

# Actually, the DFS cycles DON'T guarantee unique_privileged. They just
# specify one mover at each step. Multiple procs might be privileged.

# The GoodCycle has unique_privileged. Let's check:
# IF we assume unique_privileged and partner(c_k) = c_j ∈ cycle,
# THEN m_j = m_k. Now at step k+1:
# c_{k+1} = flip(c_k, m_k), c_{j+1} = flip(c_j, m_k).
# c_{k+1} and c_{j+1} differ at anti(m_k).
# At c_{k+1}: proc m_k has TF = (c_{k+1}[left(m_k)], 1-S, c_{k+1}[right(m_k)]).
# This is non-mover at k+1 (unless m_{k+1} = m_k).
# At c_{j+1}: proc m_k has same TF (anti(m_k) not in m_k's nbhd).
# This is non-mover at j+1 (unless m_{j+1} = m_k).

# Case A: m_{k+1} = m_k and m_{j+1} = m_k. All movers = m_k by induction. Fairness violated.
# Case B: m_{k+1} = m_k and m_{j+1} ≠ m_k.
#   proc m_k is mover at k+1 and non-mover at j+1, same TF context. TF CONFLICT.
# Case C: m_{k+1} ≠ m_k and m_{j+1} = m_k. Same, TF conflict (symmetric).
# Case D: m_{k+1} ≠ m_k and m_{j+1} ≠ m_k. Both non-mover, same TF, consistent.
#   But now consider c_{k+1} and c_{j+1} as a new pair differing at anti(m_k).
#   Is c_{j+1} = partner(c_{k+1}, m_{k+1})? Only if anti(m_{k+1}) = anti(m_k), i.e., m_{k+1} = m_k. Not our case.
#   But by unique_privileged at c_{j+1}: the unique privileged proc is m_{j+1}.
#   By unique_privileged at c_{k+1}: the unique privileged proc is m_{k+1}.
#   Since m_{k+1} ≠ m_k and m_{j+1} ≠ m_k, and c_{k+1}, c_{j+1} differ at anti(m_k):

#   Is proc m_{k+1} privileged at c_{j+1}?
#   TF of m_{k+1} at c_{k+1}: some (L,S,R).
#   TF of m_{k+1} at c_{j+1}: differs because anti(m_k) ∈ nbhd(m_{k+1}) (since m_{k+1} ≠ m_k).
#   So different TF context. We don't know if m_{k+1} is privileged at c_{j+1}.

#   Is proc m_{j+1} privileged at c_{k+1}?
#   Same issue: TF differs.

#   Now apply partner argument at step k+1:
#   partner(c_{k+1}, m_{k+1}) = flip(c_{k+1}, anti(m_{k+1})).
#   This may or may not be c_{j+1}.

#   Actually, I think the key insight is:
#   In Case D, c_{j+1} is NOT the partner of c_{k+1} (w.r.t. m_{k+1}).
#   So the partner argument at step k+1 is independent.
#   We can apply Lemma 4 at step k+1: partner(c_{k+1}, m_{k+1}) ∈ C?
#   If yes, same argument recurses. If no, we have what we need for Step B.

#   But the issue is: this doesn't give a contradiction from step k's hypothesis.
#   We assumed partner(c_k, m_k) ∈ C. In Case D, we don't derive a contradiction.
#   Instead, we get a new pair (c_{k+1}, c_{j+1}) in C differing at anti(m_k),
#   with movers m_{k+1} ≠ m_{k} and m_{j+1} ≠ m_k.

#   Let's continue to step k+2:
#   c_{k+2} = flip(c_{k+1}, m_{k+1}), c_{j+2} = flip(c_{j+1}, m_{j+1}).
#   If m_{k+1} = m_{j+1}: diff still at anti(m_k).
#     At c_{k+2}: proc m_{k+1} has TF = some context. Non-mover (unless m_{k+2} = m_{k+1}).
#     At c_{j+2}: same TF for proc m_{k+1}. Non-mover (unless m_{j+2} = m_{k+1}).
#     Same case analysis: Cases A-D with m_{k+1} playing the role of m_k.

#   If m_{k+1} ≠ m_{j+1}: diff changes!
#     c_{k+2} XOR c_{j+2} = e_{anti(m_k)} XOR e_{m_{k+1}} XOR e_{m_{j+1}}.
#     This is multi-bit. The pair structure breaks down.

# I think Case D with m_{k+1} ≠ m_{j+1} is the hard case.
# Let me check: does Case D ever happen in practice?

print("\n=== Case analysis for partner-in-cycle with GoodCycle constraints ===")
# Simulate: for fair cycles, assume unique_privileged (so m_j = m_k when partner in cycle).
# Then check which case (A/B/C/D) applies.

for cyc in cycles[:5]:
    cfg_set = {c for c, _ in cyc}
    cfg_to_idx = {c: i for i, (c, _) in enumerate(cyc)}
    L = len(cyc)

    for k, (cfg, mover) in enumerate(cyc):
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner in cfg_set:
            j = cfg_to_idx[partner]
            _, mover_j = cyc[j]

            # Under unique_privileged, m_j would be forced to equal mover.
            # But in the DFS cycle, m_j might differ. Skip those.
            if mover_j != mover:
                # Under GoodCycle, this can't happen (unique_priv forces m_j = m_k).
                # So this is a "virtual" TF conflict.
                pass

            # Assume m_j = mover (as GoodCycle would force).
            m = mover
            # Step k+1, j+1:
            k1 = (k + 1) % L
            j1 = (j + 1) % L
            _, m_k1 = cyc[k1]
            _, m_j1 = cyc[j1]

            if m_k1 == m and m_j1 == m:
                case = "A (both same)"
            elif m_k1 == m and m_j1 != m:
                case = "B (k+1 same, j+1 diff)"
            elif m_k1 != m and m_j1 == m:
                case = "C (k+1 diff, j+1 same)"
            else:
                case = "D (both diff)"

            print(f"  Cycle len={L}, k={k}, j={j}, m={m}, m_k1={m_k1}, m_j1={m_j1}: {case}")
            break

# Let me think about this differently.
# The critical realization: under unique_privileged, if partner(c_k) = c_j with m_j = m_k = m,
# then at the NEXT step, proc m has the SAME TF context at c_{k+1} and c_{j+1}
# (since they differ at anti(m) which is NOT in m's nbhd).
# The TF context of m at c_{k+1} is (L', 1-S, R') where (L', _, R') are from the
# non-m-bits of c_{k+1} and S is the original value of bit m at c_k.

# At c_{k+1}: if m is non-mover, f_m(L', 1-S, R') = 1-S (preserved).
# At c_{j+1}: if m is non-mover, f_m(L', 1-S, R') = 1-S (preserved). Consistent.
# At c_{k+1}: if m IS mover, f_m(L', 1-S, R') = S (flips back). So f(ctx) = S ≠ 1-S.
# At c_{j+1}: if m IS mover, same thing. Consistent if both mover.
# Cross: if m is mover at k+1, non-mover at j+1: f = S vs f = 1-S. CONFLICT.
# So: mover status of m at k+1 and j+1 must agree. Cases A or D.

# In Case D: m is non-mover at both k+1 and j+1.
# Now: at c_{k+1}, unique privileged is m_{k+1} ≠ m.
# At c_{j+1}, unique privileged is m_{j+1} ≠ m.
# c_{k+1} and c_{j+1} differ at anti(m).
# What if m_{k+1} = m_{j+1} = m'?
# Then proc m' is privileged at both c_{k+1} and c_{j+1}.
# TF of m' at c_{k+1} vs c_{j+1}: anti(m) ∈ nbhd(m') (since m' ≠ m), so they DIFFER.
# Both are mover: f_m'(ctx1) = 1-S1, f_m'(ctx2) = 1-S2. Different contexts, consistent.

# What if m_{k+1} ≠ m_{j+1}?
# Then m_{k+1} is privileged at c_{k+1} but not necessarily at c_{j+1}.
# And m_{j+1} is privileged at c_{j+1} but not necessarily at c_{k+1}.
# By unique_privileged at c_{j+1}: m_{j+1} is the ONLY privileged proc.
# Is m_{k+1} privileged at c_{j+1}? If it were, m_{k+1} = m_{j+1}. Contradiction.
# So m_{k+1} is NOT privileged at c_{j+1}.
# TF of m_{k+1} at c_{j+1}: different from at c_{k+1} (anti(m) in nbhd).
# So f_{m_{k+1}} returns the current value at c_{j+1} (not privileged).
# And f_{m_{k+1}} returns a DIFFERENT value at c_{k+1} (privileged).
# Different TF contexts, so no constraint.

# The argument needs to propagate. Let me think about it over the full cycle.

# Key observation: under Case D, c_{k+1} and c_{j+1} differ at anti(m).
# If m_{k+1} = m_{j+1}: they form a new pair with same property.
# Repeating: m_{k+t} = m_{j+t} for all t, OR at some point it splits (Cases B/C -> conflict).
# If it splits: say at step t, m_{k+t} = m but m_{j+t} ≠ m (or vice versa). Then TF conflict.
# If it never splits: m_{k+t} = m_{j+t} for all t.
# After L steps: (k+L, j+L) = (k, j). The mover sequences are identical
# shifted by (j-k): m_s = m_{s+(j-k)} for all s.
# The mover sequence has period dividing gcd(L, j-k).
# By fairness, all 4 procs fire at least once in the period.
# But j-k < L, so the period divides some proper divisor of L.

# Actually wait: m_{k+t} = m_{j+t} for ALL t doesn't mean the sequence has period j-k.
# It means the sequence is periodic with period dividing j-k.

# Hmm, actually: m_s = m_{s+d} for all s (where d = j-k mod L, d > 0).
# This means the sequence has period dividing d.
# So in one period (d steps), each proc fires F_i times.
# In L steps, each proc fires (L/d) * F_i times.
# For fairness: F_i >= 1 for all i. So each proc fires >= L/d >= 2 times.
# For binary: each proc fires an even number of times. So 2 | F_i.
# L/d divides L. F_i >= 1. Sum of F_i = d.
# Since all 4 F_i >= 1: d >= 4. L >= 8.
# Each F_i even: d >= 8. But d < L. If L = 8, d < 8 and d >= 8: contradiction!

# WAIT - each F_i doesn't need to be even within ONE period. The TOTAL fires
# (L/d) * F_i need to be even (since binary -> bit flips back). So (L/d)*F_i is even.
# If L/d is even, then (L/d)*F_i is always even regardless of F_i. OK.
# If L/d is odd, then F_i must be even for all i. So d >= 8. But d < L. If L <= 16, d <= 15.
# If L = 8, d < 8, so d in {1,...,7} with d | gcd(8, ...).
# Actually d doesn't need to divide L. But m_s = m_{s+d} for all s (mod L).
# So after L/gcd(L,d) * d steps: we get m_s = m_s. The period divides gcd(L,d).
# Wait no: m_s = m_{s+d mod L}. The period of this divides gcd(L, d).
# Let p = gcd(L, d). Then m_s = m_{s+p} for all s.
# In p steps: each proc fires F_i times with sum F_i = p.
# Total fires in L steps: (L/p) * F_i must be even for all i.

# For L = 8: p divides gcd(8, d). d ∈ {1,...,7}.
# p = gcd(8, d). Possible p: 1, 2, 4.
# If p = 4: F_i ≥ 1 for all 4, sum = 4 → F_i = 1 for all. (8/4)*1 = 2 = even. OK!
# If p = 2: F_i ≥ 1 for all 4, sum = 2. But 4 procs need ≥ 1 each: impossible (sum = 2 < 4).
# If p = 1: sum = 1, 4 procs need ≥ 1: impossible.

# So p = 4. That means d = 4 (gcd(8, d) = 4 → d = 4).
# So j - k ≡ 4 mod 8, i.e., j = k + 4 mod 8.
# The mover sequence has period 4 with each proc firing exactly once.

# CRUCIAL: after 4 steps, the movers repeat. m_k = m_{k+4}, m_{k+1} = m_{k+5}, etc.
# And d = 4 means the paired config c_j at step j = k+4 also has mover m_k.
# After 4 more steps, back to start.

# Now: c_k and c_{k+4} differ at anti(m_k).
# The movers at k, k+1, k+2, k+3 are a permutation of {0,1,2,3} (each fires once in period 4).
# At each step t: c_t and c_{t+4} differ at anti(m_k).
# At step t: proc m_t fires. At step t+4: proc m_{t+4} = m_t fires.
# TF of m_t at c_t and c_{t+4}: same (anti(m_k) not in m_t's nbhd ONLY if m_t = m_k).
# For m_t ≠ m_k: anti(m_k) IS in m_t's nbhd. Different TF. No constraint.
# For m_t = m_k (i.e., t = k and t = k+4): same TF, both mover. Consistent.

# But the key question remains: why can't this actually exist?
# Under Case D with d = 4 and L = 8: is there a contradiction?

# Wait - I need to re-examine. The assumption was partner(c_k) ∈ C.
# Under Case D propagation: c_t and c_{t+4} differ at anti(m_k) for all t.
# And m_t = m_{t+4} for all t.

# Now: the cycle visits 8 configs. Each config at step t has a partner at step t+4.
# These 4 pairs {c_t, c_{t+4}} for t=0..3 partition the 8 cycle configs.
# Each pair differs at bit anti(m_k).

# This means: in the cycle, every config c_t has c_t XOR e_{anti(m_k)} also in the cycle.
# The cycle is closed under flipping bit anti(m_k).

# Now: bit anti(m_k) is one of {0,1,2,3}. The cycle consists of 8 configs
# closed under flipping this bit. So 4 pairs of configs differing at bit anti(m_k).

# Do such cycles exist? Let me check.
print("\n=== Checking cycles closed under anti(m) flip ===")
for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    L = len(cyc)
    if L != 8:
        continue
    for bit in range(4):
        closed = all(flip(c, bit) in cfg_set for c in cfg_set)
        if closed:
            movers = [m for _, m in cyc]
            # Check if all movers have anti(m) = bit
            anti_vals = [(m + 2) % 4 for m in movers]
            all_same_anti = all(a == bit for a in anti_vals)
            if all_same_anti:
                print(f"  Found: cfgs={sorted(cfg_set)}, bit={bit}, movers={movers}")
                # Check mover sequence period-4 with m_t = m_{t+4}
                per4 = all(movers[t] == movers[(t+4) % L] for t in range(L))
                # Check if TF conflict exists
                has_c = has_tf_conflict_fn(cyc)
                print(f"    Period-4: {per4}, TF conflict: {has_c}")

def has_tf_conflict_fn(cycle):
    tf_map = {}
    for cfg, mover in cycle:
        ctx = tf_key(cfg, mover)
        key = (mover, ctx)
        val = 1 - ctx[1]
        if key not in tf_map: tf_map[key] = set()
        tf_map[key].add(val)
        for j in range(4):
            if j == mover: continue
            ctx_j = tf_key(cfg, j)
            key_j = (j, ctx_j)
            val_j = ctx_j[1]
            if key_j not in tf_map: tf_map[key_j] = set()
            tf_map[key_j].add(val_j)
    return any(len(v) > 1 for v in tf_map.values())

print("\n=== Actually checking ALL length-8 fair cycles for anti-flip closure ===")
count = 0
for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    L = len(cyc)
    if L != 8:
        continue
    movers = [m for _, m in cyc]
    for bit in range(4):
        closed = all(flip(c, bit) in cfg_set for c in cfg_set)
        if closed:
            # Check movers: m_t = m_{t+4}?
            per4 = all(movers[t] == movers[(t+4) % L] for t in range(L))
            if per4 and all((m+2)%4 == bit for m in movers):
                has_c = has_tf_conflict_fn(cyc)
                count += 1
                if count <= 5:
                    print(f"  cfgs={sorted(cfg_set)}, bit={bit}, movers={movers}, conflict={has_c}")

print(f"Total anti-flip-closed + per4 + all-same-anti cycles: {count}")

# Check: any such cycle WITHOUT TF conflict?
count_no_conflict = 0
for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    L = len(cyc)
    if L != 8:
        continue
    movers = [m for _, m in cyc]
    for bit in range(4):
        closed = all(flip(c, bit) in cfg_set for c in cfg_set)
        if closed:
            per4 = all(movers[t] == movers[(t+4) % L] for t in range(L))
            if per4:
                has_c = has_tf_conflict_fn(cyc)
                if not has_c:
                    count_no_conflict += 1
                    print(f"  NO CONFLICT: cfgs={sorted(cfg_set)}, bit={bit}, movers={movers}")
                    break

print(f"Anti-flip-closed + per4 cycles without TF conflict: {count_no_conflict}")
