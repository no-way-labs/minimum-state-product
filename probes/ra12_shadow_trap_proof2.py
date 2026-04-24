"""
Shadow Trap Proof — Part 2: Deep structural analysis
Focus on understanding the shift mechanism and why bad cycles form.
"""

import itertools
from collections import defaultdict

def build_sweep_cycle(n, ms):
    """Build right-then-left sweep for given ms."""
    cfg = [0] * n
    configs = [tuple(cfg)]
    movers = []

    # Right sweep
    for p in range(n):
        movers.append(p)
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    # Left sweep
    for p in range(n - 1, -1, -1):
        movers.append(p)
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    assert configs[-1] == configs[0], f"Cycle doesn't close: {configs[-1]} != {configs[0]}"
    configs = configs[:-1]
    CL = len(configs)
    return configs, movers

def extract_context_table(configs, movers, ms):
    """Extract (proc, L, S, R, S') for each step."""
    n = len(ms)
    CL = len(configs)
    table = []
    for k in range(CL):
        p = movers[k]
        cfg = configs[k]
        L = cfg[(p - 1) % n]
        S = cfg[p]
        R = cfg[(p + 1) % n]
        next_cfg = configs[(k + 1) % CL]
        S_prime = next_cfg[p]
        table.append((p, L, S, R, S_prime))
    return table

def build_context_map(table):
    """Map (proc, L, S, R) -> (S', step)."""
    cmap = {}
    for step, (p, L, S, R, Sp) in enumerate(table):
        key = (p, L, S, R)
        cmap[key] = (Sp, step)
    return cmap

def find_all_forced(cfg, cmap, ms):
    """Find all forced procs in cfg."""
    n = len(ms)
    forced = []
    for p in range(n):
        L = cfg[(p - 1) % n]
        S = cfg[p]
        R = cfg[(p + 1) % n]
        key = (p, L, S, R)
        if key in cmap:
            Sp, step = cmap[key]
            forced.append((p, Sp, step))
    return forced

def shift_config(cfg, q, v):
    """Change proc q's value to v in cfg."""
    new = list(cfg)
    new[q] = v
    return tuple(new)

# ============================================================
# ANALYSIS: n=5, all binary
# ============================================================
n = 5
ms = [2] * n
configs, movers = build_sweep_cycle(n, ms)
table = extract_context_table(configs, movers, ms)
cmap = build_context_map(table)
CL = len(configs)
good_set = set(configs)

print(f"n={n}, ms={ms}, CL={CL}")
print(f"Distinct good configs: {len(good_set)}")
print()

# KEY INSIGHT: Examine what happens when we shift one position
print("=== Shifting analysis ===")
for step_idx in range(CL):
    g = configs[step_idx]
    mover = movers[step_idx]
    print(f"\nStep {step_idx}: g={g}, mover={mover}")

    for q in range(n):
        for v in range(ms[q]):
            if v == g[q]:
                continue
            c = shift_config(g, q, v)
            if c in good_set:
                print(f"  Shift proc {q} to {v}: {c} -> GOOD CONFIG")
                continue
            forced = find_all_forced(c, cmap, ms)
            print(f"  Shift proc {q} to {v}: {c} -> {len(forced)} forced procs: {[(p, step) for p, _, step in forced]}")

print("\n\n" + "=" * 60)
print("=== CRITICAL: Understanding the mover context structure ===")
print("=" * 60)

# For each step, which procs have forced contexts?
print("\nAt each good config, which procs match a mover context?")
for step_idx in range(CL):
    g = configs[step_idx]
    forced = find_all_forced(g, cmap, ms)
    forced_procs = [(p, step) for p, _, step in forced]
    # The mover itself should be there
    print(f"Step {step_idx}: g={g}, mover={movers[step_idx]}, all forced: {forced_procs}")

print("\n\n" + "=" * 60)
print("=== KEY: Context coverage analysis ===")
print("=" * 60)

# For each proc p, how many of its possible contexts (L,S,R) appear in the mover table?
for p in range(n):
    total_contexts = ms[(p-1) % n] * ms[p] * ms[(p+1) % n]
    mover_contexts = [(L,S,R) for (pp, L, S, R, Sp) in table if pp == p]
    print(f"Proc {p}: {len(mover_contexts)}/{total_contexts} contexts in mover table: {mover_contexts}")

print("\n\n" + "=" * 60)
print("=== Follow forced orbit from each shifted good config ===")
print("=" * 60)

all_bad_cycles = set()
for step_idx in [0]:  # Start from g_0
    g = configs[step_idx]
    for q in range(n):
        for v in range(ms[q]):
            if v == g[q]:
                continue
            start = shift_config(g, q, v)
            if start in good_set:
                continue

            orbit = [start]
            current = start
            cycle_found = False
            for _ in range(50):
                forced = find_all_forced(current, cmap, ms)
                if not forced:
                    print(f"  STUCK at {current} from shifting proc {q}")
                    break
                # Use the forced proc that matches the current step
                # Actually: which forced proc do we choose?
                # In a deterministic system, there should be exactly one privileged proc
                # But we might have multiple. Let's check.
                if len(forced) > 1:
                    # Multiple forced procs - need to pick one
                    # In the actual system, this means multiple procs are privileged
                    # The scheduler picks one. For the bad cycle to be forced,
                    # we need ALL paths to stay non-good.
                    pass

                # Try following the "natural" order (lowest proc index)
                p, Sp, step = forced[0]
                new_cfg = list(current)
                new_cfg[p] = Sp
                current = tuple(new_cfg)

                if current == start:
                    cycle_found = True
                    print(f"  Shift g_0 proc {q} to {v}: cycle of length {len(orbit)}")
                    all_bad_cycles.add(frozenset(orbit))
                    break
                orbit.append(current)

            if not cycle_found and len(orbit) < 50:
                pass  # stuck case already printed

print(f"\nFound {len(all_bad_cycles)} distinct bad cycles")

# Now the KEY question: when there are multiple forced procs,
# does the choice matter?
print("\n\n" + "=" * 60)
print("=== Multiplicity of forced procs ===")
print("=" * 60)

all_non_good = [c for c in itertools.product(*[range(m) for m in ms]) if c not in good_set]
multi_forced = 0
for c in all_non_good:
    forced = find_all_forced(c, cmap, ms)
    if len(forced) > 1:
        multi_forced += 1
        # Check: do any two forced procs conflict (adjacent)?
        procs = [p for p, _, _ in forced]
        print(f"  {c}: {len(forced)} forced procs at {procs}")

print(f"\n{multi_forced}/{len(all_non_good)} non-good configs have multiple forced procs")

# KEY: Are the forced procs ever adjacent?
# If they're never adjacent, firing order doesn't matter (they commute)
print("\n\n" + "=" * 60)
print("=== Commutativity check: do forced procs ever share a neighbor? ===")
print("=" * 60)

for c in all_non_good:
    forced = find_all_forced(c, cmap, ms)
    if len(forced) <= 1:
        continue
    procs = [p for p, _, _ in forced]
    for i in range(len(procs)):
        for j in range(i+1, len(procs)):
            dist = min(abs(procs[i] - procs[j]), n - abs(procs[i] - procs[j]))
            if dist <= 1:
                print(f"  ADJACENT forced: {c}, procs {procs[i]} and {procs[j]}, dist={dist}")
