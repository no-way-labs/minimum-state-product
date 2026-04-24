"""Check if L=16 fair cycles exist with no TF conflict."""

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

def has_tf_conflict(cycle):
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

cycles = find_all_fair_cycles()

from collections import Counter
lengths = Counter(len(c) for c in cycles)
print(f"Length distribution: {sorted(lengths.items())}")

cf = [c for c in cycles if not has_tf_conflict(c)]
cf_lengths = Counter(len(c) for c in cf)
print(f"Conflict-free length distribution: {sorted(cf_lengths.items())}")

# Check L=16 specifically
l16 = [c for c in cycles if len(c) == 16]
print(f"\nL=16 cycles: {len(l16)}")
l16_cf = [c for c in l16 if not has_tf_conflict(c)]
print(f"L=16 conflict-free: {len(l16_cf)}")

# Actually, for L=16 to happen, the cycle visits all 16 configs.
# Let's check: does the GoodCycle constraint (unique_privileged at every config)
# rule out L=16?

# For unique_privileged: each config has EXACTLY ONE privileged proc.
# That means f_j(L,S,R) != S for exactly one j.
# For the other 3 procs: f_j(L,S,R) = S.

# With 16 configs and 4 procs, there are 64 (config, proc) pairs.
# 16 are mover (one per config), 48 are non-mover.
# Each mover pair (j, ctx) gives f_j(ctx) = 1-S.
# Each non-mover pair (j, ctx) gives f_j(ctx) = S.

# TF conflict: same (j, ctx) with different requirements.
# (j, (L,S,R)) with mover: f_j(L,S,R) = 1-S.
# (j, (L,S,R)) with non-mover: f_j(L,S,R) = S.
# Conflict iff S != 1-S, which is always true for S in {0,1}. So any (j, ctx) that
# appears both as mover and non-mover gives a conflict.

# There are 4 procs x 8 TF contexts = 32 possible (proc, TF) pairs.
# We have 16 mover pairs and 48 non-mover pairs. Total 64 assignments to 32 keys.
# By pigeonhole: each key gets 2 assignments on average.
# For no conflict: each key must have all assignments agree (all mover or all non-mover).

# Can this work? 16 of 64 are mover. If some (j, ctx) is mover at 2 configs: it contributes 2 to mover count.
# If some (j, ctx) is non-mover at all its configs: contributes 0 to mover count.
# Total mover = 16.

# Each key appears at exactly 2 configs (each TF context (L,S,R) for proc j:
# L = c[left(j)], S = c[j], R = c[right(j)]. anti(j) is not involved.
# So two configs that agree on left(j), j, right(j) but differ on anti(j) share the TF for j.
# There are exactly 2 such configs (differing at anti(j)).
# So each (j, ctx) appears at exactly 2 configs.

# For no conflict at (j, ctx): both configs must have the SAME mover status for j.
# Either both have j as mover (contributing 2 to mover count), or neither does.
# With 32 keys: let x keys have both configs as mover (contributing 2x movers),
# and 32-x keys have both as non-mover (contributing 0).
# Total mover pairs: 2x = 16, so x = 8.

# So: for L=16 with no TF conflict: exactly 8 of the 32 (proc, TF) keys must be
# "doubly mover" and 24 must be "doubly non-mover".

# For each proc j: the 8 TF contexts partition into y_j "doubly mover" and 8-y_j "doubly non-mover".
# The doubly mover keys give 2*y_j configs where j is mover. Sum: 2*(y_0+y_1+y_2+y_3) = 16.
# But also: each config has exactly one mover. So each config contributes 1 to the total.
# Total = 16. Consistent.

# But more constraints: for each config c, exactly one proc j has (j, tfCtx(c,j)) as mover.
# The paired config c' = flip(c, anti(j)) also has (j, tfCtx(c,j)) as mover (doubly mover).
# So c' also has j as its unique mover.
# This means: anti(j)-paired configs have the SAME mover j.

# For proc j: each "doubly mover" TF context pairs two configs (differing at anti(j)).
# Both have j as mover. After j fires at c: c' = flip(c, j). After j fires at c_paired: c'_paired = flip(c_paired, j).
# c and c_paired differ at anti(j). c' and c'_paired also differ at anti(j) (since j != anti(j)).

# Now: at c' = flip(c, j), what's the mover? It's some proc j'. We need j' != j (or j' = j).
# If j' = j: j fires again. TF context: (L, 1-S, R). Different TF context from (L, S, R).
# This is a "doubly mover" key for j at (L, 1-S, R)? Only if the paired config (differing at anti(j))
# also has j as mover with context (L, 1-S, R). The paired config = flip(c', anti(j)) = flip(flip(c, j), anti(j)).
# Its TF for j: (L', 1-S, R') where L' = c'[left(j)] (might differ if anti(j) = left(j)... but anti(j) is NOT in j's nbhd).
# So TF = (L, 1-S, R). Its paired config's TF is also (L, 1-S, R). If j is mover at both: doubly mover.
# Both have S' = 1-S. After j fires: S'' = S. The cycle goes c -> c' (flip j) -> c'' (flip j) = c. Period 2.
# But we need all 4 procs to fire. If j fires every step: only j fires. Contradiction with fairness.

# So j' != j at some point. The mover changes.

# This is getting complex. Let me just check computationally: are there ANY L=16 fair cycles
# on Q4 with no TF conflict?
print(f"\nFinal answer: L=16 conflict-free cycles exist: {len(l16_cf) > 0}")
print(f"All conflict-free cycles have L=8: {all(len(c) == 8 for c in cf)}")

# Also check: is L=16 possible with unique_privileged?
# For unique_privileged, we need: for each config, exactly one proc is privileged.
# This depends on f. With L=16 and no TF conflict, we showed x=8 doubly-mover keys.
# Each config has exactly one mover. Unique_privileged requires the mover to be the ONLY
# privileged proc. Non-movers must NOT be privileged.
# Non-mover (j, ctx): f_j(ctx) = S (current value). Not privileged.
# Mover (j, ctx): f_j(ctx) = 1-S. Privileged.
# So unique_privileged is automatically satisfied: only the mover proc is privileged.

# So L=16 with no TF conflict would give a valid system on rs2222!
# But we know no valid system exists. So L=16 with no TF conflict is impossible.
# We need to prove this.

# The computation says: 0 such cycles exist. So it's true.
# Can we prove it analytically?

# With the doubly-mover structure: 8 doubly-mover keys give 16 mover assignments.
# For each proc j: y_j doubly-mover keys, contributing 2*y_j mover configs.
# Each config has exactly one mover. So for each anti(j)-pair:
# the pair shares a mover j. The 8 anti(j)-pairs are: {c, flip(c, anti(j))}.
# But different procs have different antis! anti(0) = 2, anti(1) = 3, anti(2) = 0, anti(3) = 1.
# So anti-pairs for proc 0 and proc 2 are the SAME: {c, flip(c, 2)}.
# And anti-pairs for proc 1 and proc 3 are the SAME: {c, flip(c, 3)}.

# For anti-pair {c, flip(c, 2)}: if mover at c is 0, then mover at flip(c,2) is also 0.
# But also: (proc 2, tfCtx(c, 2)) should be doubly non-mover (since mover is 0, not 2).
# flip(c, 2) = c' has same (left(2), 2, right(2)) = (1, c[2]', 3). Wait, c' differs at bit 2.
# tfCtx(c', 2) = (c'[1], c'[2], c'[3]) = (c[1], 1-c[2], c[3]). DIFFERENT from tfCtx(c, 2) = (c[1], c[2], c[3]).
# So (proc 2, tfCtx(c, 2)) and (proc 2, tfCtx(c', 2)) are DIFFERENT keys.

# Hmm, I thought each (j, ctx) appears at exactly 2 configs (differing at anti(j)).
# Let me re-examine: tfCtx(c, j) = (c[left(j)], c[j], c[right(j)]).
# Two configs with same tfCtx(c, j) must agree on left(j), j, right(j).
# They can differ only on anti(j). There are exactly 2 such configs.
# So yes: each (j, ctx) key has exactly 2 configs.

# For the pair {c, c'} where c' = flip(c, anti(j)):
# tfCtx(c, j) = tfCtx(c', j). Both in the same key.
# Mover at c is some proc p. Mover at c' is...
# If (p, tfCtx(c, p)) is a doubly-mover key: flip(c, anti(p)) also has mover p.
# But flip(c, anti(p)) might not equal c' = flip(c, anti(j)) unless anti(p) = anti(j), i.e., p = j.

# So: if mover at c is j, then flip(c, anti(j)) = c' also has mover j (doubly-mover).
# If mover at c is p != j, then the doubly-mover constraint for (p, tfCtx(c, p)):
# flip(c, anti(p)) has mover p. But flip(c, anti(p)) != c' (since anti(p) != anti(j)).
# So c' has some mover q where (q, tfCtx(c', q)) is doubly-mover.
# The constraint: q is the mover at c' AND at flip(c', anti(q)).

# This is a complex combinatorial constraint. Let me just verify:
# are there L=16 fair cycles on Q4 at all?
print(f"\nTotal L=16 fair cycles: {len(l16)}")
if l16:
    # Check first few for TF conflict count
    for i, cyc in enumerate(l16[:3]):
        tf_map = {}
        for cfg, mover in cyc:
            ctx = tf_key(cfg, mover)
            key = (mover, ctx)
            if key not in tf_map: tf_map[key] = set()
            tf_map[key].add(1 - ctx[1])
            for j in range(4):
                if j == mover: continue
                ctx_j = tf_key(cfg, j)
                key_j = (j, ctx_j)
                if key_j not in tf_map: tf_map[key_j] = set()
                tf_map[key_j].add(ctx_j[1])
        conflicts = sum(1 for v in tf_map.values() if len(v) > 1)
        print(f"  Cycle {i}: {conflicts} conflicting TF keys")
        movers = [m for _,m in cyc]
        print(f"    Movers: {movers}")
