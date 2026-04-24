"""
Shadow Cycle Analysis for ms=(2,2,3,2,3) — the second product-72 candidate.

Ring structure: P0(2)-P1(2)-P2(3)-P3(2)-P4(3)
Binary processors: P0, P1, P3 (NOT consecutive — max 2 consecutive)
Ternary processors: P2, P4

Key difference from (2,2,2,3,3): the binary block is SPLIT.
P0-P1 are consecutive binary, P3 is isolated binary.
This changes the sweep dynamics fundamentally.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter

ms = [2, 2, 3, 2, 3]
n = 5
total_configs = 1
for m in ms:
    total_configs *= m
print(f"ms={ms}, product={total_configs}, total configs={total_configs}")

# ============================================================
# PART 1: Understand the structure
# ============================================================

print("\n" + "="*70)
print("PART 1: STRUCTURAL ANALYSIS")
print("="*70)

print(f"""
Ring: P0(2) - P1(2) - P2(3) - P3(2) - P4(3) - [back to P0]

Neighborhoods:
  P0: L=P4(3), S=P0(2), R=P1(2) → domain 3×2×2 = 12
  P1: L=P0(2), S=P1(2), R=P2(3) → domain 2×2×3 = 12
  P2: L=P1(2), S=P2(3), R=P3(2) → domain 2×3×2 = 12
  P3: L=P2(3), S=P3(2), R=P4(3) → domain 3×2×3 = 18
  P4: L=P3(2), S=P4(3), R=P0(2) → domain 2×3×2 = 12

Binary block: P0-P1 (2 consecutive) and P3 (isolated)
Binary state space: P0×P1×P3 = 2×2×2 = 8 states
Non-binary (NB) state: (P2, P4) ∈ {{0,1,2}} × {{0,1,2}} = 9 pairs

Total: 8 × 9 = 72 configs ✓

Sweep structure: The binary "block" is split:
  - P0-P1 sweep together (2 consecutive)
  - P3 sweeps independently
This means the "binary state" is (P0, P1, P3) — 8 values.
""")

# ============================================================
# PART 2: Find ALL consistent length-10 cycles
# ============================================================

print("="*70)
print("PART 2: FINDING CONSISTENT CYCLES")
print("="*70)

def check_cycle_consistency(cycle_configs, n, ms):
    """Check if a cycle has consistent transition entries."""
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx+1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, f"non-single mover at step {idx}"
        mover = diffs[0]

        Li = c[(mover-1) % n]; Si = c[mover]; Ri = c[(mover+1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, f"conflict at f{mover}({Li},{Si},{Ri})"
        required[key] = S_new

        for i in range(n):
            if i != mover:
                Li = c[(i-1) % n]; Si = c[i]; Ri = c[(i+1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}, f"conflict at f{i}({Li},{Si},{Ri})"
                required[key] = Si

    return True, required, "OK"


def find_shadow_cycle(determined, good_set, ms, n, max_len=30):
    """Check if determined entries create a shadow cycle."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        visited = set()
        path = []
        config = start

        for step in range(max_len + 1):
            if config in good_set:
                break
            if config in visited:
                cycle_start = path.index(config)
                shadow = path[cycle_start:]
                return shadow
            visited.add(config)
            path.append(config)

            forced = []
            for i in range(n):
                L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
                key = (i, L, S, R)
                if key in determined and determined[key] != S:
                    forced.append((i, determined[key]))

            if not forced:
                break

            # Try each forced processor; prefer ones staying outside good
            moved = False
            for proc, new_val in forced:
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config not in good_set:
                    config = new_config
                    moved = True
                    break
            if not moved:
                break

    return None


def find_short_cycles(start, ms, max_length=10, max_found=200):
    """Find valid good cycles by DFS."""
    n = len(ms)
    found = []
    def dfs(path, movers_used):
        if len(found) >= max_found:
            return
        config = path[-1]
        if len(path) >= n * 2 and len(movers_used) == n:
            for proc in range(n):
                for new_val in range(ms[proc]):
                    if new_val == config[proc]:
                        continue
                    new_config = list(config)
                    new_config[proc] = new_val
                    if tuple(new_config) == start:
                        ok, req, msg = check_cycle_consistency(list(path), n, ms)
                        if ok:
                            found.append(list(path))
        if len(path) >= max_length:
            return
        visited = set(path)
        for proc in range(n):
            for new_val in range(ms[proc]):
                if new_val == config[proc]:
                    continue
                new_config = list(config)
                new_config[proc] = new_val
                nc = tuple(new_config)
                if nc in visited:
                    continue
                dfs(path + [nc], movers_used | {proc})
    dfs([start], set())
    return found


# Search from (0,0,0,0,0)
print("Searching for consistent length-10 cycles from (0,0,0,0,0)...")
cycles_10 = find_short_cycles((0,0,0,0,0), ms, max_length=10, max_found=500)
print(f"Found {len(cycles_10)} consistent length-10 cycles")

shadow_count = 0
no_shadow_count = 0
no_shadow_examples = []

for i, cyc in enumerate(cycles_10):
    ok, determined, msg = check_cycle_consistency(cyc, n, ms)
    good_set = set(cyc)
    shadow = find_shadow_cycle(determined, good_set, ms, n)

    if shadow:
        shadow_count += 1
    else:
        no_shadow_count += 1
        nb_pairs = sorted(set((c[2],c[4]) for c in cyc))
        bin_states = sorted(set((c[0],c[1],c[3]) for c in cyc))
        no_shadow_examples.append((cyc, nb_pairs, bin_states))

print(f"\nResults: {shadow_count} with shadow, {no_shadow_count} without shadow")

if no_shadow_examples:
    print(f"\n*** {no_shadow_count} CYCLES WITHOUT SHADOW — potential candidates! ***")
    for j, (cyc, nb, bs) in enumerate(no_shadow_examples[:5]):
        movers = []
        for idx in range(len(cyc)):
            c = cyc[idx]
            c_next = cyc[(idx+1) % len(cyc)]
            for k in range(n):
                if c[k] != c_next[k]:
                    movers.append(k)
                    break
        mcounts = Counter(movers)
        print(f"\n  Cycle {j}: movers={dict(sorted(mcounts.items()))}")
        print(f"    NB pairs: {nb}")
        print(f"    Binary states: {bs}")
        for idx, c in enumerate(cyc):
            print(f"    {idx}: {c} → P{movers[idx]}")

# ============================================================
# PART 3: Try other starting configs
# ============================================================

print("\n" + "="*70)
print("PART 3: CYCLES FROM OTHER STARTING CONFIGS")
print("="*70)

other_starts = [
    (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0),
    (0,0,0,0,1), (0,0,0,0,2), (0,0,0,1,0),
    (0,0,1,0,1), (0,0,1,1,0), (1,0,0,0,0),
    (1,1,0,0,0), (0,1,0,0,0), (0,0,2,1,2),
]

total_cycles = 0
total_shadow = 0
total_no_shadow = 0

for start in other_starts:
    cycles = find_short_cycles(start, ms, max_length=10, max_found=200)
    s_count = 0
    ns_count = 0
    for cyc in cycles:
        ok, determined, msg = check_cycle_consistency(cyc, n, ms)
        good_set = set(cyc)
        shadow = find_shadow_cycle(determined, good_set, ms, n)
        if shadow:
            s_count += 1
        else:
            ns_count += 1
            # Print details of shadow-free cycles
            if ns_count <= 2:
                movers = []
                for idx in range(len(cyc)):
                    c = cyc[idx]
                    c_next = cyc[(idx+1) % len(cyc)]
                    for k in range(n):
                        if c[k] != c_next[k]:
                            movers.append(k)
                            break
                nb_pairs = sorted(set((c[2],c[4]) for c in cyc))
                bin_states = sorted(set((c[0],c[1],c[3]) for c in cyc))
                print(f"  Start {start}: SHADOW-FREE cycle!")
                print(f"    NB={nb_pairs}, bin={bin_states}")
                for idx, c in enumerate(cyc):
                    print(f"      {idx}: {c} → P{movers[idx]}")

    total_cycles += len(cycles)
    total_shadow += s_count
    total_no_shadow += ns_count

    if len(cycles) > 0:
        print(f"  Start {start}: {len(cycles)} cycles, {s_count} shadow, {ns_count} no shadow")
    else:
        print(f"  Start {start}: no length-10 cycles found")

print(f"\nTotal: {total_cycles} cycles, {total_shadow} shadow, {total_no_shadow} no shadow")

# ============================================================
# PART 4: For shadow-free cycles, check convergence
# ============================================================

if total_no_shadow > 0:
    print("\n" + "="*70)
    print("PART 4: CONVERGENCE CHECK FOR SHADOW-FREE CYCLES")
    print("="*70)

    import random
    random.seed(42)

    # Collect all shadow-free cycles
    all_sf_cycles = []
    for start in other_starts:
        cycles = find_short_cycles(start, ms, max_length=10, max_found=200)
        for cyc in cycles:
            ok, determined, msg = check_cycle_consistency(cyc, n, ms)
            good_set = set(cyc)
            shadow = find_shadow_cycle(determined, good_set, ms, n)
            if not shadow:
                all_sf_cycles.append((cyc, determined))

    print(f"Total shadow-free cycles to check: {len(all_sf_cycles)}")

    for ci, (cyc, determined) in enumerate(all_sf_cycles[:20]):
        good_set = set(cyc)

        # Build partial transition functions from determined entries
        f = [dict() for _ in range(n)]
        for (proc, L, S, R), out in determined.items():
            f[proc][(L, S, R)] = out

        # Find free entries
        free_entries = []
        for proc in range(n):
            m_L = ms[(proc-1) % n]
            m_S = ms[proc]
            m_R = ms[(proc+1) % n]
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        if (L,S,R) not in f[proc]:
                            free_entries.append((proc, L, S, R))

        # Random search for valid completions
        best_bad = float('inf')
        found_valid = False

        for trial in range(2000):
            # Random completion
            f_complete = [dict(fp) for fp in f]
            for (proc, L, S, R) in free_entries:
                f_complete[proc][(L,S,R)] = random.randint(0, ms[proc]-1)

            # Check convergence
            all_configs = list(iproduct(*[range(m) for m in ms]))

            # Compute successors
            successors = {}
            me_ok = True
            for config in all_configs:
                priv = set()
                for i in range(n):
                    Li = config[(i-1) % n]; Si = config[i]; Ri = config[(i+1) % n]
                    if f_complete[i][(Li,Si,Ri)] != Si:
                        priv.add(i)
                if config in good_set and len(priv) != 1:
                    me_ok = False
                    break
                succs = set()
                for p in priv:
                    nc = list(config)
                    nc[p] = f_complete[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
                    succs.add(tuple(nc))
                successors[config] = succs

            if not me_ok:
                continue

            # Check for bad attractors
            bad_configs = set(all_configs) - good_set
            changed = True
            while changed:
                changed = False
                to_remove = set()
                for c in bad_configs:
                    if c not in successors or not successors[c]:
                        to_remove.add(c)
                        continue
                    if all(s not in bad_configs for s in successors[c]):
                        to_remove.add(c)
                if to_remove:
                    bad_configs -= to_remove
                    changed = True

            if not bad_configs:
                found_valid = True
                print(f"\n  *** VALID SYSTEM FOUND for cycle {ci}! ***")
                print(f"  Cycle: {cyc[:3]}...")
                break
            else:
                if len(bad_configs) < best_bad:
                    best_bad = len(bad_configs)

        if not found_valid:
            print(f"  Cycle {ci}: no valid completion in 2000 trials "
                  f"(best bad attractor: {best_bad})")

else:
    print("\n  All cycles have shadow cycles — ms=(2,2,3,2,3) appears impossible!")

# ============================================================
# PART 5: Summary
# ============================================================

print("\n" + "="*70)
print("SUMMARY")
print("="*70)

print(f"""
ms=(2,2,3,2,3), product=72:

Length-10 cycles checked: {total_cycles}
  With shadow cycles: {total_shadow}
  Without shadow cycles: {total_no_shadow}

{"ALL cycles have shadow cycles → ms=(2,2,3,2,3) IMPOSSIBLE for length-10"
 if total_no_shadow == 0 else
 f"{total_no_shadow} shadow-free cycles found — checking convergence..."}
""")
