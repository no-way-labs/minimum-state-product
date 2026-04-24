"""Prove: partner(c_k) in cycle -> TF conflict, for ALL fair Q4 cycles."""

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

# For each fair cycle with partner(c_k) in cycle for some k,
# find the specific TF conflict.
cycles = find_all_fair_cycles()

count_with_partner_in = 0
count_with_conflict = 0
count_partner_conflict = 0

for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    cfg_to_idx = {c: i for i, (c, _) in enumerate(cyc)}
    L = len(cyc)

    # Check if any partner is in cycle
    has_partner_in = False
    partner_k = None
    for k, (cfg, mover) in enumerate(cyc):
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner in cfg_set:
            has_partner_in = True
            partner_k = k
            break

    if not has_partner_in:
        continue

    count_with_partner_in += 1

    # Find the specific TF conflict
    # Collect all TF constraints
    tf_constraints = {}  # (proc, ctx) -> set of required values
    for cfg, mover in cyc:
        # Mover: f_mover(ctx) = 1 - S
        ctx = tf_key(cfg, mover)
        key = (mover, ctx)
        if key not in tf_constraints:
            tf_constraints[key] = set()
        tf_constraints[key].add(1 - ctx[1])

        # Non-movers: f_j(ctx) = S
        for j in range(4):
            if j == mover:
                continue
            ctx_j = tf_key(cfg, j)
            key_j = (j, ctx_j)
            if key_j not in tf_constraints:
                tf_constraints[key_j] = set()
            tf_constraints[key_j].add(ctx_j[1])

    has_conflict = False
    for key, vals in tf_constraints.items():
        if len(vals) > 1:
            has_conflict = True
            break

    if has_conflict:
        count_with_conflict += 1
    else:
        print(f"WARNING: partner in cycle but NO TF conflict!")
        print(f"  Cycle: {cyc}")

print(f"Cycles with partner in cycle: {count_with_partner_in}")
print(f"Of those, with TF conflict: {count_with_conflict}")
print(f"Of those, without TF conflict: {count_with_partner_in - count_with_conflict}")

# Now let's find the MECHANISM: given partner(c_k) in cycle, what's the conflict?
# Let's trace the first few in detail.
print("\n=== Detailed TF conflict from partner-in-cycle ===")
for idx, cyc in enumerate(cycles[:100]):
    cfg_set = {c for c, _ in cyc}
    cfg_to_idx = {c: i for i, (c, _) in enumerate(cyc)}
    L = len(cyc)

    for k, (cfg, mover) in enumerate(cyc):
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner in cfg_set:
            j = cfg_to_idx[partner]
            _, mover_j = cyc[j]

            # Step k: proc mover fires at cfg. Step j: check mover at partner.
            # partner has same TF for `mover` (anti-flip preserves TF nbhd).
            # So: if mover at j != mover at k, then proc `mover` is non-mover at j.
            # That gives TF conflict at `mover`: mover output 1-S vs non-mover output S.

            if mover_j != mover:
                # Direct TF conflict at proc `mover`
                ctx_m = tf_key(cfg, mover)
                ctx_m_j = tf_key(partner, mover)
                assert ctx_m == ctx_m_j
                if idx < 5:
                    print(f"  Cycle {idx}: k={k} cfg={bin(cfg)[2:].zfill(4)} mover={mover}, "
                          f"j={j} partner={bin(partner)[2:].zfill(4)} mover_j={mover_j}")
                    print(f"    Direct TF conflict at proc {mover}: ctx={ctx_m}, "
                          f"mover gives {1-ctx_m[1]}, non-mover gives {ctx_m[1]}")
            else:
                # Both have same mover. No direct TF conflict at proc `mover`.
                # Need to trace further.
                if idx < 5:
                    print(f"  Cycle {idx}: k={k} cfg={bin(cfg)[2:].zfill(4)} mover={mover}, "
                          f"j={j} partner={bin(partner)[2:].zfill(4)} mover_j={mover_j} (SAME mover)")
                    # Trace the chain
                    kk, jj = k, j
                    for step in range(L):
                        cfg_kk, m_kk = cyc[kk]
                        cfg_jj, m_jj = cyc[jj]
                        if m_kk != m_jj:
                            ctx = tf_key(cfg_kk, m_kk)
                            ctx2 = tf_key(cfg_jj, m_kk)
                            print(f"    At step offset {step}: k'={kk} m={m_kk}, j'={jj} m={m_jj}")
                            if ctx == ctx2:
                                print(f"    TF conflict at proc {m_kk}: ctx={ctx}, mover vs non-mover")
                            break
                        kk = (kk + 1) % L
                        jj = (jj + 1) % L
                    else:
                        print(f"    All movers same -> would violate fairness!")
            break
