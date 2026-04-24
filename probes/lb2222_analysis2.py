"""Deeper analysis: complement cycle structure and the proof mechanism."""

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
    seen_canon = set()
    unique = []
    for s in range(16):
        dfs(s, s, {s}, [], 0)
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
conflict_free = [c for c in cycles if not has_tf_conflict(c)]

print(f"Conflict-free cycles: {len(conflict_free)}")

for i, cyc in enumerate(conflict_free):
    cfg_set = {c for c, _ in cyc}
    complement = set(range(16)) - cfg_set

    # Build TF
    tf_map = {}
    for cfg, mover in cyc:
        ctx = tf_key(cfg, mover)
        tf_map[(mover, ctx)] = 1 - ctx[1]
        for j in range(4):
            if j != mover:
                ctx_j = tf_key(cfg, j)
                tf_map[(j, ctx_j)] = ctx_j[1]

    # For each complement config, find the unique forced privileged proc and its successor
    print(f"\nCycle {i}: movers={[m for _,m in cyc]}")
    comp_succ = {}
    for cfg in sorted(complement):
        for j in range(4):
            ctx = tf_key(cfg, j)
            key = (j, ctx)
            if key in tf_map and tf_map[key] != ctx[1]:
                succ = flip(cfg, j)
                comp_succ[cfg] = (j, succ)
                in_comp = succ in complement
                print(f"  {bin(cfg)[2:].zfill(4)} -> priv={j} -> succ={bin(succ)[2:].zfill(4)} (in complement: {in_comp})")
                break

    # Trace forced chain from each complement config
    print(f"  Forced chains:")
    visited = set()
    for start in sorted(complement):
        if start in visited:
            continue
        chain = [start]
        cur = start
        visited.add(cur)
        while True:
            if cur not in comp_succ:
                chain.append("DEAD")
                break
            _, nxt = comp_succ[cur]
            if nxt not in complement:
                chain.append(f"ESCAPE({bin(nxt)[2:].zfill(4)})")
                break
            if nxt in visited:
                chain.append(f"CYCLE({bin(nxt)[2:].zfill(4)})")
                break
            chain.append(nxt)
            visited.add(nxt)
            cur = nxt
        print(f"    {' -> '.join(bin(c)[2:].zfill(4) if isinstance(c,int) else c for c in chain)}")

# Now check: is the complement cycle a SINGLE 8-cycle for all?
print("\n=== Complement Cycle Structure ===")
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

    comp_succ = {}
    for cfg in complement:
        for j in range(4):
            ctx = tf_key(cfg, j)
            key = (j, ctx)
            if key in tf_map and tf_map[key] != ctx[1]:
                succ = flip(cfg, j)
                comp_succ[cfg] = succ
                break

    # Find cycle structure
    all_visited = set()
    cycle_lengths = []
    for start in sorted(complement):
        if start in all_visited:
            continue
        cur = start
        path = []
        while cur not in all_visited:
            all_visited.add(cur)
            path.append(cur)
            if cur in comp_succ and comp_succ[cur] in complement:
                cur = comp_succ[cur]
            else:
                path.append("BREAK")
                break
        else:
            # Found a cycle
            cycle_start = cur
            idx = path.index(cycle_start) if cycle_start in path else -1
            if idx >= 0:
                cycle_lengths.append(len(path) - idx)

    print(f"  Cycle {i}: complement cycle lengths = {cycle_lengths}, "
          f"all successors in complement: {all(comp_succ.get(c, -1) in complement for c in complement)}")

# Key check: does each complement config have EXACTLY ONE privileged proc?
print("\n=== Unique Privileged in Complement ===")
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

    all_single = True
    for cfg in complement:
        priv = []
        for j in range(4):
            ctx = tf_key(cfg, j)
            key = (j, ctx)
            if key in tf_map and tf_map[key] != ctx[1]:
                priv.append(j)
        if len(priv) != 1:
            all_single = False
            print(f"  Cycle {i}, cfg {bin(cfg)[2:].zfill(4)}: priv={priv}")

    if all_single:
        pass  # print(f"  Cycle {i}: all complement configs have exactly 1 forced privileged proc")

print("\n=== Partner Identity Check ===")
# For each cycle, check: partner(c_k, m_k) = flipCfg(c_{k+1}, anti(m_{k+1}))?
# i.e., forced_succ(partner(c_k)) = partner(c_{k+1})?
for i, cyc in enumerate(conflict_free[:3]):
    cfg_set = {c for c, _ in cyc}
    complement = set(range(16)) - cfg_set
    L = len(cyc)

    tf_map = {}
    for cfg, mover in cyc:
        ctx = tf_key(cfg, mover)
        tf_map[(mover, ctx)] = 1 - ctx[1]
        for j in range(4):
            if j != mover:
                ctx_j = tf_key(cfg, j)
                tf_map[(j, ctx_j)] = ctx_j[1]

    print(f"\nCycle {i}: movers={[m for _,m in cyc]}")
    for k in range(L):
        cfg_k, m_k = cyc[k]
        cfg_k1, m_k1 = cyc[(k+1) % L]
        anti_k = (m_k + 2) % 4
        anti_k1 = (m_k1 + 2) % 4
        partner_k = flip(cfg_k, anti_k)
        partner_k1 = flip(cfg_k1, anti_k1)

        # Find forced successor of partner_k
        forced_succ_pk = None
        for j in range(4):
            ctx = tf_key(partner_k, j)
            key = (j, ctx)
            if key in tf_map and tf_map[key] != ctx[1]:
                forced_succ_pk = flip(partner_k, j)
                forced_mover = j
                break

        print(f"  k={k}: partner(c_k)={bin(partner_k)[2:].zfill(4)}, "
              f"forced_succ={bin(forced_succ_pk)[2:].zfill(4) if forced_succ_pk else 'NONE'} (mover={forced_mover if forced_succ_pk else 'N/A'}), "
              f"partner(c_{{k+1}})={bin(partner_k1)[2:].zfill(4)}, "
              f"match={forced_succ_pk == partner_k1}")
