"""Check which fair cycles on Q4 have TF conflicts."""

def get_bit(cfg, j):
    return (cfg >> j) & 1

def tf_key(cfg, proc):
    left_p = (proc + 3) % 4
    right_p = (proc + 1) % 4
    return (proc, get_bit(cfg, left_p), get_bit(cfg, proc), get_bit(cfg, right_p))

def check_tf_conflict(cycle):
    tf_constraints = {}
    for cfg, mover in cycle:
        for proc in range(4):
            key = tf_key(cfg, proc)
            if proc == mover:
                val = 1 - get_bit(cfg, proc)
            else:
                val = get_bit(cfg, proc)
            if key not in tf_constraints:
                tf_constraints[key] = val
            elif tf_constraints[key] != val:
                return True
    return False

def check_forced_kernel(cycle):
    """Check if complement has a forced kernel (nonempty after sink removal)."""
    # Build TF map from cycle
    tf_map = {}
    for cfg, mover in cycle:
        for proc in range(4):
            key = tf_key(cfg, proc)
            if proc == mover:
                val = 1 - get_bit(cfg, proc)
            else:
                val = get_bit(cfg, proc)
            tf_map[key] = val

    cycle_cfgs = set(c for c, _ in cycle)
    complement = set(range(16)) - cycle_cfgs

    if not complement:
        return False  # Empty complement, no kernel

    # For each complement config, find forced privileged procs
    def forced_targets(cfg, remaining):
        targets = set()
        for proc in range(4):
            key = tf_key(cfg, proc)
            if key in tf_map:
                if tf_map[key] != get_bit(cfg, proc):
                    # proc is privileged (forced)
                    target = cfg ^ (1 << proc)
                    if target in remaining:
                        targets.add(target)
        return targets

    # Iterative sink removal
    remaining = set(complement)
    changed = True
    while changed:
        changed = False
        sinks = set()
        for cfg in remaining:
            if not forced_targets(cfg, remaining):
                sinks.add(cfg)
        if sinks:
            remaining -= sinks
            changed = True

    return len(remaining) > 0  # Kernel exists

# Check ALL fair cycles on Q4
count = 0
no_conflict_count = 0
no_conflict_no_kernel = 0
no_conflict_examples = []

def dfs(start, cur, visited, path, fair_mask):
    global count, no_conflict_count, no_conflict_no_kernel
    for proc in range(4):
        nxt = cur ^ (1 << proc)
        new_fair = fair_mask | (1 << proc)
        new_path = path + [(cur, proc)]
        if nxt == start:
            if new_fair == 15:  # fair
                count += 1
                has_conflict = check_tf_conflict(new_path)
                if not has_conflict:
                    no_conflict_count += 1
                    has_kernel = check_forced_kernel(new_path)
                    if not has_kernel:
                        no_conflict_no_kernel += 1
                        print(f"UNBLOCKED: len={len(new_path)} movers={[m for _,m in new_path]}")
                    elif len(no_conflict_examples) < 3:
                        no_conflict_examples.append((new_path[:], has_kernel))
        elif nxt not in visited:
            dfs(start, nxt, visited | {nxt}, new_path, new_fair)

dfs(0, 0, {0}, [], 0)
print(f"Total fair cycles from 0: {count}")
print(f"TF-conflict-free: {no_conflict_count}")
print(f"TF-conflict-free AND no forced kernel: {no_conflict_no_kernel}")
for ex, kern in no_conflict_examples[:3]:
    print(f"  Example (len {len(ex)}): movers = {[m for _, m in ex]}, kernel={kern}")
