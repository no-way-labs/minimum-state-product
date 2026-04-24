"""Key question: given a GoodCycle with unique_privileged,
if partner(c_k, m_k) = c_j (so m_j = m_k = m), does the
existence of these two configs with same mover + same TF at proc m
ALWAYS lead to a TF conflict at proc m specifically?

The answer was no (6137 cases had conflict at other procs).
But maybe the conflict at proc m can be found with a more careful argument.

New approach: at c_k (mover m) and c_j (mover m), same TF for m.
At c_{k+1} and c_{j+1}: proc m has SAME TF (different from step k's).
Check if proc m is ever mover at one and non-mover at other.

Trace the TF of proc m through the ENTIRE cycle starting from k and j simultaneously."""

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

# For each cycle with same-mover partner:
# Track TF of proc m at steps k+t and j+t, and whether m is mover.
# We want: ∃t such that TF_m(c_{k+t}) = TF_m(c_{j+t}) and m is mover at one, non-mover at other.

conflict_at_m = 0
conflict_not_at_m = 0
no_conflict_at_m = 0

for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    cfg_to_idx = {c: i for i, (c, _) in enumerate(cyc)}
    L = len(cyc)

    for k, (cfg, mover) in enumerate(cyc):
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner not in cfg_set:
            continue
        j = cfg_to_idx[partner]
        _, mj = cyc[j]
        if mj != mover:
            continue

        m = mover
        # Track TF of proc m at k+t and j+t
        found = False
        for t in range(L):
            kt = (k + t) % L
            jt = (j + t) % L
            cfg_kt, m_kt = cyc[kt]
            cfg_jt, m_jt = cyc[jt]
            tf_kt = tf_key(cfg_kt, m)
            tf_jt = tf_key(cfg_jt, m)

            if tf_kt == tf_jt:
                # Same TF for proc m
                is_mover_kt = (m_kt == m)
                is_mover_jt = (m_jt == m)
                if is_mover_kt != is_mover_jt:
                    found = True
                    conflict_at_m += 1
                    break

        if not found:
            # Check if there's a TF conflict at ANY proc
            tf_map = {}
            has_any = False
            for cfg2, mover2 in cyc:
                ctx = tf_key(cfg2, mover2)
                key2 = (mover2, ctx)
                if key2 not in tf_map: tf_map[key2] = set()
                tf_map[key2].add(1 - ctx[1])
                for p in range(4):
                    if p == mover2: continue
                    ctx_p = tf_key(cfg2, p)
                    key_p = (p, ctx_p)
                    if key_p not in tf_map: tf_map[key_p] = set()
                    tf_map[key_p].add(ctx_p[1])
            for key2, vals in tf_map.items():
                if len(vals) > 1:
                    has_any = True
                    break
            if has_any:
                conflict_not_at_m += 1
            else:
                no_conflict_at_m += 1
        break

print(f"TF conflict at proc m via same-TF tracking: {conflict_at_m}")
print(f"TF conflict at OTHER proc (not via proc m same-TF): {conflict_not_at_m}")
print(f"No TF conflict at all: {no_conflict_at_m}")

# If there are cases where the conflict is NOT at proc m,
# we need a different mechanism for those.
# Let's check: is it always at proc m?
print(f"\nAnswer: conflict always at proc m: {conflict_not_at_m == 0 and no_conflict_at_m == 0}")
