"""Clean proof approach for Case 2:
Show that for ANY conflict-free fair Q4 cycle, the complement has a forced cycle.

Key insight: partner(c_k, m_k) is in complement (by Case 1 contrapositive).
At partner(c_k, m_k), proc m_k is privileged.
The forced move flips bit m_k, giving partner(c_k, m_k) XOR e_{m_k}.

Question: does this forced move stay in complement?
And does it chain to cover all complement configs?"""

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

# All 16 conflict-free cycles
cf_cycles = [
    [(0,0),(1,1),(3,2),(7,3),(15,0),(14,1),(12,2),(8,3)],
    [(0,0),(1,3),(9,2),(13,1),(15,0),(14,3),(6,2),(2,1)],
    [(0,1),(2,0),(3,3),(11,2),(15,1),(13,0),(12,3),(4,2)],
    [(0,1),(2,2),(6,3),(14,0),(15,1),(13,2),(9,3),(1,0)],
    [(0,2),(4,1),(6,0),(7,3),(15,2),(11,1),(9,0),(8,3)],
    [(0,2),(4,3),(12,0),(13,1),(15,2),(11,3),(3,0),(2,1)],  # approximate
]

# Let me just use the computational result for one cycle and verify the proof structure.

# Take cycle 0: movers = [0,1,2,3,0,1,2,3], configs = [0,1,3,7,15,14,12,8]
cyc = [(0,0),(1,1),(3,2),(7,3),(15,0),(14,1),(12,2),(8,3)]
L = len(cyc)
cfg_set = {c for c,_ in cyc}
complement = set(range(16)) - cfg_set

print(f"Cycle: {[(bin(c)[2:].zfill(4), m) for c,m in cyc]}")
print(f"Complement: {[bin(c)[2:].zfill(4) for c in sorted(complement)]}")

# Partners: partner(c_k, m_k) = flip(c_k, anti(m_k))
print("\nPartners:")
for k, (cfg, mover) in enumerate(cyc):
    anti = (mover + 2) % 4
    p = flip(cfg, anti)
    print(f"  c_{k}={bin(cfg)[2:].zfill(4)}, m={mover}, anti={anti}, "
          f"partner={bin(p)[2:].zfill(4)} (in complement: {p in complement})")

# Build TF map from cycle
tf_map = {}
for cfg, mover in cyc:
    ctx = tf_key(cfg, mover)
    tf_map[(mover, ctx)] = 1 - ctx[1]
    for j in range(4):
        if j != mover:
            ctx_j = tf_key(cfg, j)
            tf_map[(j, ctx_j)] = ctx_j[1]

print(f"\nDetermined TF entries: {len(tf_map)}")

# For each complement config, find forced privileged proc
print("\nComplement analysis:")
for cfg in sorted(complement):
    priv = []
    for j in range(4):
        ctx = tf_key(cfg, j)
        key = (j, ctx)
        if key in tf_map:
            if tf_map[key] != ctx[1]:
                priv.append(j)
    print(f"  {bin(cfg)[2:].zfill(4)}: forced priv = {priv}")

# Key: for each complement config, the forced privileged proc is exactly
# the proc that appears as mover in the partner construction.
print("\nPartner-to-complement mapping:")
for k, (cfg, mover) in enumerate(cyc):
    anti = (mover + 2) % 4
    p = flip(cfg, anti)
    assert p in complement

    # The forced privileged proc at p should be mover (proc m_k)
    ctx_mk = tf_key(p, mover)
    key_mk = (mover, ctx_mk)
    if key_mk in tf_map:
        forced_val = tf_map[key_mk]
        is_priv = (forced_val != ctx_mk[1])
        succ = flip(p, mover) if is_priv else None
        print(f"  partner(c_{k}) = {bin(p)[2:].zfill(4)}: proc {mover} "
              f"priv={is_priv}, succ={bin(succ)[2:].zfill(4) if succ else 'N/A'}")
        if succ:
            # succ = p XOR e_{mover} = flip(c_k, anti(mover)) XOR e_{mover}
            # = c_k XOR e_{anti(mover)} XOR e_{mover}
            print(f"    succ = c_{k} XOR e_{anti} XOR e_{mover}")
            # Is succ in complement?
            print(f"    succ in complement: {succ in complement}")
            # Is succ = partner(c_{k+1}) for some definition?
            k1 = (k+1) % L
            cfg_k1, m_k1 = cyc[k1]
            anti_k1 = (m_k1 + 2) % 4
            partner_k1 = flip(cfg_k1, anti_k1)
            print(f"    partner(c_{k+1}) = {bin(partner_k1)[2:].zfill(4)}")
            print(f"    succ == partner(c_{k+1}): {succ == partner_k1}")

# Let me check the full chain
print("\n=== Full forced chain in complement ===")
# Start from partner(c_0)
start = flip(cyc[0][0], (cyc[0][1] + 2) % 4)
cur = start
chain = []
for _ in range(10):
    # Find forced privileged
    for j in range(4):
        ctx = tf_key(cur, j)
        key = (j, ctx)
        if key in tf_map and tf_map[key] != ctx[1]:
            chain.append((cur, j))
            cur = flip(cur, j)
            break
    else:
        chain.append((cur, -1))
        break

print("Chain:")
for cfg, mover in chain:
    print(f"  {bin(cfg)[2:].zfill(4)} -> mover {mover}")

# Now: the chain through complement. Each step:
# partner(c_k) has proc m_k forced privileged.
# Forced successor = partner(c_k) XOR e_{m_k} = c_k XOR e_{anti(m_k)} XOR e_{m_k}.
# This is c_k flipped at both anti(m_k) and m_k.
# For n=4: anti(m_k) and m_k are distinct (m_k != anti(m_k)).
# So forced_succ = c_k XOR e_{m_k} XOR e_{anti(m_k)}.

# Now c_{k+1} = c_k XOR e_{m_k}.
# So forced_succ = c_{k+1} XOR e_{anti(m_k)}.
# This is: flip(c_{k+1}, anti(m_k)).

# Is this the partner of c_{k+1}?
# partner(c_{k+1}, m_{k+1}) = flip(c_{k+1}, anti(m_{k+1})).
# So forced_succ = partner(c_{k+1}, m_{k+1}) iff anti(m_k) = anti(m_{k+1}), i.e., m_k = m_{k+1}.

# For alternating movers (m_k cycles through 0,1,2,3): m_k ≠ m_{k+1}.
# So forced_succ ≠ partner(c_{k+1}).
# But forced_succ = flip(c_{k+1}, anti(m_k)) IS some complement config.
# And partner(c_{k+1}) = flip(c_{k+1}, anti(m_{k+1})) is a DIFFERENT complement config.

# The complement configs are:
# For each k: partner(c_k) = flip(c_k, anti(m_k)).
# That's 8 configs (one per cycle step). Since cycle has 8 steps and 8 configs,
# and partner is injective (flipCfg is injective), we get 8 complement configs.
# Total = 16 = 8 + 8. Check!

# Now: forced_succ(partner(c_k)) = flip(c_{k+1}, anti(m_k)).
# This is flip(c_{k+1}, anti(m_k)). Is this one of the partners?
# partner(c_j) = flip(c_j, anti(m_j)) for some j.
# So we need: flip(c_{k+1}, anti(m_k)) = flip(c_j, anti(m_j)) for some j.
# i.e., c_{k+1} XOR e_{anti(m_k)} = c_j XOR e_{anti(m_j)}.

# For cycle 0 with movers [0,1,2,3,0,1,2,3]:
# anti values: [2,3,0,1,2,3,0,1]
# Let's compute all 8 partners and all 8 forced successors:
print("\n=== Complete partner/successor table ===")
partners = {}
for k, (cfg, mover) in enumerate(cyc):
    anti = (mover + 2) % 4
    p = flip(cfg, anti)
    partners[k] = p
    print(f"  partner(c_{k}) = flip({bin(cfg)[2:].zfill(4)}, bit {anti}) = {bin(p)[2:].zfill(4)}")

print()
for k in range(L):
    p = partners[k]
    mover = cyc[k][1]
    succ = flip(p, mover)  # forced successor: flip partner at proc m_k
    # Find which partner this equals
    for k2 in range(L):
        if partners[k2] == succ:
            print(f"  forced_succ(partner(c_{k})) = {bin(succ)[2:].zfill(4)} = partner(c_{k2})")
            break
    else:
        print(f"  forced_succ(partner(c_{k})) = {bin(succ)[2:].zfill(4)} NOT a partner!")
