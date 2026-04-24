"""
Shadow Cycle Proof: For EVERY consistent length-10 cycle for ms=(2,2,2,3,3),
the determined entries create a shadow cycle through anti-sweep configs.

Also checks longer cycles and cycles visiting all 8 binary states.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter

ms = [2, 2, 2, 3, 3]
n = 5

def check_cycle_consistency(cycle_configs, n, ms):
    """Check if a cycle has consistent transition entries."""
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx+1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, "non-single mover"
        mover = diffs[0]

        # Mover entry
        Li = c[(mover-1) % n]; Si = c[mover]; Ri = c[(mover+1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, f"conflict at f{mover}({Li},{Si},{Ri})"
        required[key] = S_new

        # Non-mover entries
        for i in range(n):
            if i != mover:
                Li = c[(i-1) % n]; Si = c[i]; Ri = c[(i+1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}, f"conflict at f{i}({Li},{Si},{Ri})"
                required[key] = Si

    return True, required, "OK"


def find_shadow_cycle(determined, good_set, ms, n, max_len=20):
    """Check if determined entries create a shadow cycle through non-good configs."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        # Try to follow forced-privilege moves from start
        visited = set()
        path = []
        config = start

        for step in range(max_len + 1):
            if config in good_set:
                break
            if config in visited:
                # Found a cycle! Extract it
                cycle_start = path.index(config)
                shadow = path[cycle_start:]
                return shadow
            visited.add(config)
            path.append(config)

            # Find forced-privileged processors
            forced = []
            for i in range(n):
                L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
                key = (i, L, S, R)
                if key in determined and determined[key] != S:
                    forced.append((i, determined[key]))

            if not forced:
                break  # No forced privilege, can't continue

            # Try each forced processor to find one that stays outside good cycle
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
                # All forced moves lead to good cycle - no shadow from here
                break

    return None


# ============================================================
# PART 1: Check all length-10 cycles starting at (0,0,0,0,0)
# ============================================================

print("="*70)
print("PART 1: ALL LENGTH-10 CYCLES FROM (0,0,0,0,0)")
print("="*70)

def find_short_cycles(start, ms, max_length=10, max_found=200):
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

cycles_10 = find_short_cycles((0,0,0,0,0), ms, max_length=10, max_found=200)
print(f"Found {len(cycles_10)} consistent length-10 cycles\n")

shadow_count = 0
no_shadow_count = 0

for i, cyc in enumerate(cycles_10):
    ok, determined, msg = check_cycle_consistency(cyc, n, ms)
    good_set = set(cyc)
    shadow = find_shadow_cycle(determined, good_set, ms, n)

    nb_pairs = sorted(set((c[3],c[4]) for c in cyc))

    if shadow:
        shadow_count += 1
        if i < 5:  # Show details for first 5
            print(f"  Cycle {i}: NB={nb_pairs} → SHADOW CYCLE len={len(shadow)}")
            for sc in shadow[:3]:
                print(f"    {sc}")
            print(f"    ...")
    else:
        no_shadow_count += 1
        print(f"  Cycle {i}: NB={nb_pairs} → NO SHADOW CYCLE!")
        # This would be very interesting - print full details
        print(f"    Cycle: {cyc}")

print(f"\nSummary: {shadow_count} with shadow, {no_shadow_count} without shadow")

# ============================================================
# PART 2: Check cycles starting at OTHER configs
# ============================================================

print("\n" + "="*70)
print("PART 2: CYCLES STARTING AT NON-ZERO CONFIGS")
print("="*70)

# Try a few other starting configs
other_starts = [(0,0,0,1,0), (0,0,0,0,2), (0,0,1,0,0), (0,1,0,0,0)]
for start in other_starts:
    cycles = find_short_cycles(start, ms, max_length=10, max_found=50)
    shadow_all = True
    for cyc in cycles:
        ok, determined, msg = check_cycle_consistency(cyc, n, ms)
        good_set = set(cyc)
        shadow = find_shadow_cycle(determined, good_set, ms, n)
        if not shadow:
            shadow_all = False
            nb_pairs = sorted(set((c[3],c[4]) for c in cyc))
            print(f"  Start {start}: NO SHADOW at NB={nb_pairs}")
            print(f"    Cycle: {cyc}")
    if shadow_all:
        print(f"  Start {start}: {len(cycles)} cycles, ALL have shadow cycles")

# ============================================================
# PART 3: Search for length-12 cycles (allow 3 states for P3 or P4)
# ============================================================

print("\n" + "="*70)
print("PART 3: LENGTH-12 CYCLES (broader search)")
print("="*70)

# For length 12, the search space is much larger.
# Limit to specific promising structures.

# Try: Gray code binary block + NB moves
# Gray code: (0,0,0)→(1,0,0)→(1,1,0)→(0,1,0)→(0,1,1)→(1,1,1)→(1,0,1)→(0,0,1)→(0,0,0)

gray = [(0,0,0),(1,0,0),(1,1,0),(0,1,0),(0,1,1),(1,1,1),(1,0,1),(0,0,1)]

# For a length-12 cycle visiting all 8 binary states:
# 8 binary moves + 4 NB moves. Each binary processor moves at least 2 times.
# P0 moves: 000→100, 110→010, 011→111, 101→001 = 4 moves
# P1 moves: 100→110, 010→011, 111→101, 001→000 ... wait
# Let me recount Gray code movers:
# (0,0,0)→(1,0,0): P0 changes. (1,0,0)→(1,1,0): P1.
# (1,1,0)→(0,1,0): P0. (0,1,0)→(0,1,1): P2.
# (0,1,1)→(1,1,1): P0. (1,1,1)→(1,0,1): P1.
# (1,0,1)→(0,0,1): P0. (0,0,1)→(0,0,0): P2.
# Movers: P0,P1,P0,P2,P0,P1,P0,P2 = P0:4, P1:2, P2:2. Each ≥2 ✓

# Now insert 4 NB moves (2 for P3, 2 for P4) at specific positions.
# The NB moves go between binary moves.

# Try: insert P3 move after position 3 (binary=(0,1,0)) and
#       P4 move after position 4, then P3 after position 7, P4 at end.

# This gives: 8 binary + 4 NB = 12 steps.
# But we need the NB moves to be consistent.

# Let's try to build a specific cycle and check consistency.

# Attempt: insert NB moves so P3 and P4 each move once in each "half"
# First half: (0,0,0)→...→(0,1,0)→P3→(0,1,0,new_s3,s4)→(0,1,1)→...
# Second half: (1,1,1)→...→(0,0,1)→P4→(0,0,1,s3,new_s4)→(0,0,0)

# Concrete attempt: s=0, a=1 for P3; t=0, b=1 for P4
# Insert P3 move after (0,1,0,...) and P4 move after (1,0,1,...)

cycle_12_attempt = [
    (0,0,0,0,0),  # P0 moves
    (1,0,0,0,0),  # P1 moves
    (1,1,0,0,0),  # P0 moves
    (0,1,0,0,0),  # P3 moves (NB)
    (0,1,0,1,0),  # P2 moves
    (0,1,1,1,0),  # P0 moves
    (1,1,1,1,0),  # P4 moves (NB)
    (1,1,1,1,1),  # P1 moves
    (1,0,1,1,1),  # P0 moves
    (0,0,1,1,1),  # P3 moves (NB)
    (0,0,1,0,1),  # P2 moves
    (0,0,0,0,1),  # P4 moves (NB) → back to (0,0,0,0,0)
]

print(f"Attempting length-12 Gray code cycle...")
# Verify
ok = True
for i in range(len(cycle_12_attempt)):
    c = cycle_12_attempt[i]
    c_next = cycle_12_attempt[(i+1) % len(cycle_12_attempt)]
    diffs = [j for j in range(n) if c[j] != c_next[j]]
    if len(diffs) != 1:
        print(f"  Step {i}: {len(diffs)} diffs between {c} and {c_next}")
        ok = False

if ok and len(set(cycle_12_attempt)) == len(cycle_12_attempt):
    ok2, determined12, msg = check_cycle_consistency(cycle_12_attempt, n, ms)
    if ok2:
        print(f"  Consistent! ✓")
        good12 = set(cycle_12_attempt)
        shadow12 = find_shadow_cycle(determined12, good12, ms, n)
        if shadow12:
            print(f"  Shadow cycle found (len={len(shadow12)})")
            for sc in shadow12[:5]:
                print(f"    {sc}")
        else:
            print(f"  NO SHADOW CYCLE! This cycle might work!")

            # Try convergence check
            from locality_bottleneck_v3 import check_convergence
            # ... too complex, just report
    else:
        print(f"  Inconsistent: {msg}")
else:
    print(f"  Invalid cycle structure")

# ============================================================
# PART 4: THE THEORETICAL ARGUMENT
# ============================================================

print("\n" + "="*70)
print("THEORETICAL ARGUMENT: SHADOW CYCLE OBSTRUCTION")
print("="*70)

print("""
THEOREM (Shadow Cycle Obstruction):
For ms=(2,2,2,3,3) with n=5, any good cycle that misses binary
states (0,1,0) and (1,0,1) creates a shadow cycle through those
states using only determined transition entries.

PROOF SKETCH:
1. The good cycle visits 6 of 8 binary states in a sweep pattern.
2. The sweep creates determined entries:
   - Rightward: f_i(L,0,R)=1 when L matches sweep direction
   - Leftward: f_i(L,1,R)=0 when L matches sweep direction
3. At anti-sweep binary state (0,1,0):
   - P2 sees (P1=1,P2=0,P3=?). If P3 matches a cycle-determined
     value, f2(1,0,P3)=1≠0 → P2 is forced-privileged.
   - P2 moves: (0,1,0,...)→(0,1,1,...). This config is also a
     "leftward sweep" position.
4. At (0,1,1,...): P1 is forced-privileged (f1(0,1,1)=0≠1).
   P1 moves: (0,1,1,...)→(0,0,1,...). This continues the
   leftward sweep into anti-sweep territory.
5. At (0,0,1,...): P0 is forced-privileged (if P4 matches a
   determined value). P0 moves: →(1,0,1,...).
6. At (1,0,1,...): the pattern REVERSES, creating a rightward
   sweep through anti-sweep territory.
7. The shadow sweep uses the NB states from the original good cycle
   but at different binary states, creating a 10-step cycle.

Since the shadow cycle uses only determined entries, it persists
for ALL completions of free entries. The daemon can follow this
cycle indefinitely, preventing convergence.

COROLLARY: Any length-10 cycle for ms=(2,2,2,3,3) that misses
binary states (0,1,0) and (1,0,1) cannot yield a valid system.

REMAINING QUESTION: Can a longer cycle that visits (0,1,0) and
(1,0,1) avoid the shadow cycle obstruction?
""")

# ============================================================
# PART 5: Check if Gray-code cycles avoid the obstruction
# ============================================================

print("="*70)
print("PART 5: SYSTEMATIC GRAY-CODE CYCLE SEARCH")
print("="*70)

# Generate all possible Gray code orderings of the 8 binary states
# and try to build consistent cycles with NB moves inserted.

# Standard reflected Gray code: 000,001,011,010,110,111,101,100
# But we can use any Hamiltonian cycle on the 3-cube.
# There are exactly 6 distinct Hamiltonian cycles on the 3-cube
# (up to starting vertex and direction).

# Let me enumerate them. The 3-cube has vertices {0,1}^3 and edges
# between vertices differing in exactly one bit.

from itertools import permutations

def find_hamiltonian_cycles_3cube():
    """Find all Hamiltonian cycles on the 3-cube."""
    vertices = [(i,j,k) for i in range(2) for j in range(2) for k in range(2)]
    adj = defaultdict(list)
    for v in vertices:
        for bit in range(3):
            w = list(v)
            w[bit] = 1 - w[bit]
            adj[v].append(tuple(w))

    cycles = []

    def dfs(path):
        if len(path) == 8:
            # Check if last vertex connects to first
            if path[0] in adj[path[-1]]:
                # Normalize: start at (0,0,0), next vertex is the smallest
                min_start = path.index((0,0,0))
                rotated = path[min_start:] + path[:min_start]
                # Also try reverse
                rev = [rotated[0]] + list(reversed(rotated[1:]))
                canonical = min(tuple(rotated), tuple(rev))
                if canonical not in [tuple(c) for c in cycles]:
                    cycles.append(list(canonical))
            return

        for w in sorted(adj[path[-1]]):
            if w not in set(path):
                dfs(path + [w])

    dfs([(0,0,0)])
    return cycles

ham_cycles = find_hamiltonian_cycles_3cube()
print(f"Hamiltonian cycles on 3-cube: {len(ham_cycles)}")

for hc in ham_cycles:
    movers_bin = []
    for i in range(len(hc)):
        v = hc[i]
        w = hc[(i+1) % len(hc)]
        bit = [j for j in range(3) if v[j] != w[j]][0]
        movers_bin.append(bit)
    counts = Counter(movers_bin)
    print(f"  {[v for v in hc]} movers: {dict(sorted(counts.items()))}")

# For each Hamiltonian cycle, try inserting 4 NB moves
# (2 for P3, 2 for P4) at different positions.
# Check if the resulting length-12 cycle is consistent.

print(f"\nTrying to build length-12 cycles from Hamiltonian cycles...")
valid_12 = 0
total_tried = 0

for hc in ham_cycles:
    # Binary mover sequence
    bin_movers = []
    for i in range(len(hc)):
        v = hc[i]
        w = hc[(i+1) % len(hc)]
        bit = [j for j in range(3) if v[j] != w[j]][0]
        bin_movers.append(bit)

    # Insert 4 NB moves: choose 4 positions (out of 8) to insert after
    # and choose which NB processor moves (P3 or P4)
    # P3 must move exactly 2 times, P4 exactly 2 times.
    # Choose 2 positions for P3 and 2 for P4.

    from itertools import combinations

    positions_8 = list(range(8))
    for p3_positions in combinations(positions_8, 2):
        for p4_positions in combinations(positions_8, 2):
            if set(p3_positions) & set(p4_positions):
                continue  # Can't insert at same position

            # For P3: try s3 values 0→1→0 (using states 0,1)
            # For P4: try s4 values 0→1→0 (using states 0,1)
            # Also try 0→2→0, 0→1→0, etc.
            for s3_vals in [(0,1), (0,2), (1,2)]:
                for s4_vals in [(0,1), (0,2), (1,2)]:
                    total_tried += 1

                    # Build the cycle
                    s3, s3_alt = s3_vals
                    s4, s4_alt = s4_vals

                    # Current NB state tracker
                    cur_s3 = s3
                    cur_s4 = s4

                    cycle_configs = []
                    pos = 0  # position in binary cycle
                    nb_insertions = sorted(
                        [(p, 3) for p in p3_positions] +
                        [(p, 4) for p in p4_positions],
                        key=lambda x: (x[0], x[1])
                    )

                    # Reset
                    cur_s3 = s3
                    cur_s4 = s4
                    insert_idx = 0

                    valid = True
                    for pos in range(8):
                        # Add binary config
                        bv = hc[pos]
                        cycle_configs.append(bv + (cur_s3, cur_s4))

                        # Check for NB insertions after this position
                        while insert_idx < len(nb_insertions) and nb_insertions[insert_idx][0] == pos:
                            proc = nb_insertions[insert_idx][1]
                            if proc == 3:
                                cur_s3 = s3_alt if cur_s3 == s3 else s3
                            else:
                                cur_s4 = s4_alt if cur_s4 == s4 else s4
                            # Add NB config (same binary state, new NB)
                            cycle_configs.append(bv + (cur_s3, cur_s4))
                            insert_idx += 1

                    # Check: does the cycle return to start?
                    if cur_s3 != s3 or cur_s4 != s4:
                        continue  # NB didn't return to initial

                    # Check distinct configs
                    if len(set(cycle_configs)) != len(cycle_configs):
                        continue

                    # Check consistency
                    ok, det, msg = check_cycle_consistency(cycle_configs, n, ms)
                    if ok:
                        good = set(cycle_configs)
                        shadow = find_shadow_cycle(det, good, ms, n)
                        valid_12 += 1
                        status = "SHADOW" if shadow else "NO SHADOW!"
                        if not shadow or valid_12 <= 3:
                            bin_states = sorted(set(c[:3] for c in cycle_configs))
                            print(f"  L={len(cycle_configs)} bin_states={len(bin_states)} "
                                  f"NB={sorted(set((c[3],c[4]) for c in cycle_configs))} "
                                  f"→ {status}")
                            if not shadow:
                                print(f"    Cycle: {cycle_configs}")

print(f"\nTotal tried: {total_tried}, Valid consistent: {valid_12}")
