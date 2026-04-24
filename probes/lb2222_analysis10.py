"""Check forced_succ shift pattern for all 16 conflict-free cycles."""

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
cf = [c for c in cycles if not has_tf_conflict(c)]

for idx, cyc in enumerate(cf):
    L = len(cyc)
    cfg_set = {c for c,_ in cyc}

    # Build TF map
    tf_map = {}
    for cfg, mover in cyc:
        ctx = tf_key(cfg, mover)
        tf_map[(mover, ctx)] = 1 - ctx[1]
        for j in range(4):
            if j != mover:
                ctx_j = tf_key(cfg, j)
                tf_map[(j, ctx_j)] = ctx_j[1]

    # Compute partners
    partners = {}
    for k, (cfg, mover) in enumerate(cyc):
        anti = (mover + 2) % 4
        partners[k] = flip(cfg, anti)

    # Compute forced successor of each partner
    partner_to_k = {v: k for k, v in partners.items()}
    shifts = []
    for k in range(L):
        p = partners[k]
        mover = cyc[k][1]
        succ = flip(p, mover)
        if succ in partner_to_k:
            target_k = partner_to_k[succ]
            shift = (target_k - k) % L
            shifts.append(shift)
        else:
            shifts.append(-1)

    movers = [m for _,m in cyc]
    print(f"Cycle {idx}: movers={movers}, shifts={shifts}")

# Now let me check: is the forced_succ always partner(c_{k+3})?
# Or does the shift depend on the mover pattern?
print("\n=== Shift analysis ===")
shift_patterns = set()
for idx, cyc in enumerate(cf):
    L = len(cyc)
    cfg_set = {c for c,_ in cyc}

    tf_map = {}
    for cfg, mover in cyc:
        ctx = tf_key(cfg, mover)
        tf_map[(mover, ctx)] = 1 - ctx[1]
        for j in range(4):
            if j != mover:
                ctx_j = tf_key(cfg, j)
                tf_map[(j, ctx_j)] = ctx_j[1]

    partners = {}
    for k, (cfg, mover) in enumerate(cyc):
        anti = (mover + 2) % 4
        partners[k] = flip(cfg, anti)

    partner_to_k = {v: k for k, v in partners.items()}
    shifts = []
    for k in range(L):
        p = partners[k]
        mover = cyc[k][1]
        succ = flip(p, mover)
        target_k = partner_to_k[succ]
        shifts.append((target_k - k) % L)

    shift_patterns.add(tuple(shifts))

print(f"Distinct shift patterns: {shift_patterns}")
print(f"All uniform: {all(len(set(s)) == 1 for s in shift_patterns)}")

# Key result: what is forced_succ(partner(c_k)) algebraically?
# forced_succ(partner(c_k)) = partner(c_k) XOR e_{m_k}
#                            = c_k XOR e_{anti(m_k)} XOR e_{m_k}
# And partner(c_{k+s}) = c_{k+s} XOR e_{anti(m_{k+s})}
# For forced_succ(partner(c_k)) to equal partner(c_{k+s}):
# c_k XOR e_{anti(m_k)} XOR e_{m_k} = c_{k+s} XOR e_{anti(m_{k+s})}
# Now c_{k+s} = c_k XOR e_{m_k} XOR e_{m_{k+1}} XOR ... XOR e_{m_{k+s-1}}
# So: e_{anti(m_k)} XOR e_{m_k} = e_{m_k} XOR e_{m_{k+1}} XOR ... XOR e_{m_{k+s-1}} XOR e_{anti(m_{k+s})}
# Simplify: e_{anti(m_k)} = e_{m_{k+1}} XOR ... XOR e_{m_{k+s-1}} XOR e_{anti(m_{k+s})}

# For s=3, movers [0,1,2,3,...]:
# e_{anti(m_k)} = e_{m_{k+1}} XOR e_{m_{k+2}} XOR e_{anti(m_{k+3})}
# anti(m_k) = (k+2)%4, m_{k+1} = (k+1)%4, m_{k+2} = (k+2)%4, anti(m_{k+3}) = (k+5)%4 = (k+1)%4
# So: e_{(k+2)%4} = e_{(k+1)%4} XOR e_{(k+2)%4} XOR e_{(k+1)%4} = 0. Wait, that's wrong.
# e_{a} XOR e_{b} XOR e_{a} = e_{b}. So e_{(k+1)%4} XOR e_{(k+2)%4} XOR e_{(k+1)%4} = e_{(k+2)%4}.
# And we need this to equal e_{(k+2)%4}. YES! So s=3 works.

# For movers [0,3,2,1,...]: check s.
# m_k=0,3,2,1 repeating. anti: 2,1,0,3.
# For k=0: need e_{anti(0)}=e_2 = e_{m_1} XOR e_{m_2} XOR e_{anti(m_3)}
#         = e_3 XOR e_2 XOR e_{anti(1)} = e_3 XOR e_2 XOR e_3 = e_2. YES! s=3 works.

# General check: for period-4 mover sequences where each proc appears once:
# m_k, m_{k+1}, m_{k+2}, m_{k+3} is a permutation of {0,1,2,3}.
# anti(m_k) = (m_k+2)%4. We need:
# e_{anti(m_k)} = e_{m_{k+1}} XOR e_{m_{k+2}} XOR e_{anti(m_{k+3})}
# i.e., {anti(m_k)} = {m_{k+1}} Δ {m_{k+2}} Δ {anti(m_{k+3})} (symmetric diff of singletons)
# Which means: anti(m_k) ∈ {m_{k+1}, m_{k+2}, anti(m_{k+3})} with odd count.

# anti(m_{k+3}) = (m_{k+3}+2)%4. Since {m_k, m_{k+1}, m_{k+2}, m_{k+3}} = {0,1,2,3}:
# m_{k+3} = the proc NOT in {m_k, m_{k+1}, m_{k+2}}.
# anti(m_k) = (m_k+2)%4.

# Since all 4 procs appear exactly once in the period:
# m_{k+1} XOR m_{k+2}: this is XOR of two distinct procs.
# anti(m_{k+3}): this is (m_{k+3}+2)%4.

# This is getting involved. Let me just verify computationally that s=3 works for all.
print(f"\nAll shifts are 3: {all(all(s == 3 for s in pat) for pat in shift_patterns)}")

# Also check: for shift patterns that are NOT 3, what's the shift?
for pat in shift_patterns:
    if any(s != 3 for s in pat):
        print(f"  Non-3 shift pattern: {pat}")
