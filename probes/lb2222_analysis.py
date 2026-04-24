"""Analyze the 128 conflict-free fair Q4 cycles."""
from itertools import product

def flip(cfg, j):
    return cfg ^ (1 << j)

def get_bit(cfg, j):
    return (cfg >> j) & 1

def left_p(j):
    return (j + 3) % 4

def right_p(j):
    return (j + 1) % 4

def tf_key(cfg, proc):
    """TF context for proc at cfg: (L, S, R)"""
    return (get_bit(cfg, left_p(proc)), get_bit(cfg, proc), get_bit(cfg, right_p(proc)))

def find_all_fair_cycles():
    """Find all fair directed cycles on Q4 = {0,1}^4."""
    cycles = []

    def dfs(start, cur, visited, path, fair_mask):
        for proc in range(4):
            nxt = flip(cur, proc)
            new_fair = fair_mask | (1 << proc)
            new_path = path + [(cur, proc)]
            if nxt == start:
                if new_fair == 15:  # all 4 procs fire
                    cycles.append(list(new_path))
            elif nxt not in visited and len(path) < 16:
                dfs(start, nxt, visited | {nxt}, new_path, new_fair)

    seen = set()
    for s in range(16):
        dfs(s, s, {s}, [], 0)

    # Deduplicate: normalize by minimum rotation
    unique = []
    seen_canon = set()
    for cyc in cycles:
        L = len(cyc)
        rotations = []
        for r in range(L):
            rotated = tuple(cyc[(r+i) % L] for i in range(L))
            rotations.append(rotated)
        canon = min(rotations)
        if canon not in seen_canon:
            seen_canon.add(canon)
            unique.append(cyc)

    return unique

def has_tf_conflict(cycle):
    """Check if a cycle has a TF conflict."""
    # Collect all (proc, tf_context, is_mover) triples
    tf_map = {}  # (proc, tf_context) -> set of values f must return
    for cfg, mover in cycle:
        # Mover: f_mover(L, S, R) = 1 - S
        ctx = tf_key(cfg, mover)
        key = (mover, ctx)
        val = 1 - ctx[1]  # 1 - S
        if key not in tf_map:
            tf_map[key] = set()
        tf_map[key].add(val)

        # Non-movers: f_j(L, S, R) = S
        for j in range(4):
            if j == mover:
                continue
            ctx_j = tf_key(cfg, j)
            key_j = (j, ctx_j)
            val_j = ctx_j[1]  # S (not privileged)
            if key_j not in tf_map:
                tf_map[key_j] = set()
            tf_map[key_j].add(val_j)

    for key, vals in tf_map.items():
        if len(vals) > 1:
            return True
    return False

print("Finding all fair Q4 cycles...")
cycles = find_all_fair_cycles()
print(f"Total fair cycles (deduplicated): {len(cycles)}")

conflict_free = [c for c in cycles if not has_tf_conflict(c)]
print(f"Conflict-free cycles: {len(conflict_free)}")

# Analyze conflict-free cycles
for i, cyc in enumerate(conflict_free[:5]):
    movers = [m for _, m in cyc]
    cfgs = [c for c, _ in cyc]
    print(f"\nCycle {i}: length={len(cyc)}")
    print(f"  Configs: {[bin(c)[2:].zfill(4) for c in cfgs]}")
    print(f"  Movers:  {movers}")

# Check all cycle lengths
from collections import Counter
lengths = Counter(len(c) for c in conflict_free)
print(f"\nLength distribution of conflict-free cycles: {dict(lengths)}")

# Check mover patterns
print("\nMover patterns of conflict-free cycles:")
mover_patterns = Counter()
for cyc in conflict_free:
    movers = tuple(m for _, m in cyc)
    mover_patterns[movers] += 1

for pat, cnt in sorted(mover_patterns.items()):
    print(f"  {pat}: {cnt}")

# Check partner avoidance
print("\n=== Partner Avoidance Check ===")
for i, cyc in enumerate(conflict_free):
    cfg_set = {c for c, _ in cyc}
    for cfg, mover in cyc:
        anti = (mover + 2) % 4
        partner = flip(cfg, anti)
        if partner in cfg_set:
            print(f"  Cycle {i}: partner of cfg={bin(cfg)[2:].zfill(4)} (mover={mover}) = {bin(partner)[2:].zfill(4)} IS IN CYCLE!")
            break
    else:
        continue
    break
else:
    print("  ALL partners are in complement for ALL conflict-free cycles!")

# Check forced successor structure in complement
print("\n=== Complement Forced Structure ===")
for i, cyc in enumerate(conflict_free[:3]):
    cfg_set = {c for c, _ in cyc}
    complement = set(range(16)) - cfg_set

    # Build transition function from cycle constraints
    tf_map = {}
    for cfg, mover in cyc:
        ctx = tf_key(cfg, mover)
        tf_map[(mover, ctx)] = 1 - ctx[1]
        for j in range(4):
            if j != mover:
                ctx_j = tf_key(cfg, j)
                tf_map[(j, ctx_j)] = ctx_j[1]

    print(f"\nCycle {i}: cycle={sorted(cfg_set)}, complement={sorted(complement)}")
    print(f"  TF entries determined: {len(tf_map)}")

    # For each complement config, find privileged procs
    for cfg in sorted(complement):
        priv_procs = []
        for j in range(4):
            ctx = tf_key(cfg, j)
            key = (j, ctx)
            if key in tf_map:
                fval = tf_map[key]
                if fval != ctx[1]:  # f != current value -> privileged
                    priv_procs.append(j)
        print(f"  Complement cfg {bin(cfg)[2:].zfill(4)}: privileged at {priv_procs}")
