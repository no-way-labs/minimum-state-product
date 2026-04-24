"""
Anti-Shadow Witness Construction for n=9.

Strategy: The shadow cycle blocks sub-optimal architectures because binary
procs have fully determined transition tables. The quaternary processor's
free entries are what break the shadow at the optimal product 32·3^{n-4}.

Approach:
1. Extract n=8 witness structure (good cycle, movers, quaternary trajectory)
2. Compute determined vs free entries — identify WHERE the shadow breaks
3. Extend to n=9 using structural insights
4. Fill free entries to prevent shadow formation while ensuring convergence
"""

from itertools import product as iproduct
from collections import defaultdict


# ═══════════════════════════════════════════════════════════════════
# N=8 WITNESS (from n9_targeted_search.py)
# ═══════════════════════════════════════════════════════════════════

def witness_n8():
    ms = (2, 2, 3, 4, 3, 3, 2, 3)
    rules = [
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,(3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,(2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
    ]
    return ms, rules


# ═══════════════════════════════════════════════════════════════════
# CORE ANALYSIS FUNCTIONS
# ═══════════════════════════════════════════════════════════════════

def extract_good_cycle(ms, rules):
    """Extract the good cycle: sequence of single-privilege configs."""
    n = len(ms)
    configs = list(iproduct(*(range(m) for m in ms)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L, S, R = cfg[(i-1)%n], cfg[i], cfg[(i+1)%n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L, S, R = cfg[(proc-1)%n], cfg[proc], cfg[(proc+1)%n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # Find single-privilege configs and follow the chain
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            nxt = move(cfg, priv[0])
            single_priv[cfg] = (nxt, priv[0])

    # Find the cycle
    for start in single_priv:
        path = []
        movers = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover)
            cur = nxt
        if cur == start and len(path) > 0:
            return path, movers

    return None, None


def compute_determined_entries(cycle, movers, n):
    """Compute all transition entries determined by the good cycle."""
    det = {}  # (proc, L, S, R) -> new_S
    det_type = {}  # (proc, L, S, R) -> 'mover' or 'non-mover'

    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mover = movers[idx]

        # Mover entry: the proc that changes
        L, S, R = c[(mover-1)%n], c[mover], c[(mover+1)%n]
        key = (mover, L, S, R)
        det[key] = c_next[mover]
        det_type[key] = 'mover'

        # Non-mover entries: all other procs keep their state
        for i in range(n):
            if i != mover:
                L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
                key = (i, L, S, R)
                det[key] = S
                det_type[key] = 'non-mover'

    return det, det_type


def compute_entry_coverage(cycle, movers, ms, n):
    """For each proc, compute which (L,S,R) triples are observed."""
    observed = {i: set() for i in range(n)}
    observed_as_mover = {i: set() for i in range(n)}

    for idx in range(len(cycle)):
        c = cycle[idx]
        mover = movers[idx]
        for i in range(n):
            L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
            observed[i].add((L, S, R))
            if i == mover:
                observed_as_mover[i].add((L, S, R))

    # Compute total possible triples and free entries
    coverage = {}
    for i in range(n):
        L_size = ms[(i-1)%n]
        S_size = ms[i]
        R_size = ms[(i+1)%n]
        total = L_size * S_size * R_size
        coverage[i] = {
            'total': total,
            'observed': len(observed[i]),
            'free': total - len(observed[i]),
            'observed_set': observed[i],
            'mover_set': observed_as_mover[i],
        }

    return coverage


def find_shadow_cycles(cycle, det, ms, n, max_cycles=20):
    """Find all shadow cycles: cycles of non-good configs using determined entries."""
    good_set = set(cycle)
    all_configs = list(iproduct(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]

    shadow_cycles = []
    visited_global = set()

    for start in non_good:
        if start in visited_global:
            continue

        visited = {}
        path = []
        c = start

        for step in range(len(all_configs) + 10):
            if c in good_set:
                break  # reached good cycle
            if c in visited:
                # Found a cycle
                shadow = path[visited[c]:]
                for sc in shadow:
                    visited_global.add(sc)
                shadow_cycles.append(shadow)
                break

            visited[c] = len(path)
            path.append(c)

            # Find forced-privileged procs (from determined entries only)
            priv = []
            for i in range(n):
                L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    priv.append((i, det[key]))

            if not priv:
                break  # no determined privilege → config is "free"

            # Follow the first forced move that stays outside C
            moved = False
            for proc, new_val in priv:
                new_c = list(c)
                new_c[proc] = new_val
                new_c = tuple(new_c)
                if new_c not in good_set:
                    c = new_c
                    moved = True
                    break
            if not moved:
                break  # all forced moves enter C → this config converges

        if len(shadow_cycles) >= max_cycles:
            break

    return shadow_cycles


# ═══════════════════════════════════════════════════════════════════
# PART 1: N=8 WITNESS ANALYSIS
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 1: N=8 WITNESS — CYCLE STRUCTURE")
print("=" * 70)
print()

ms8, rules8 = witness_n8()
n8 = len(ms8)
cycle8, movers8 = extract_good_cycle(ms8, rules8)

print(f"State counts: {ms8}")
print(f"Product: {eval('*'.join(str(m) for m in ms8))}")
print(f"Cycle length: {len(cycle8)}")
print(f"Total configs: {eval('*'.join(str(m) for m in ms8))}")
print()

# Mover frequency
from collections import Counter
mover_counts = Counter(movers8)
print(f"Mover frequency: {dict(sorted(mover_counts.items()))}")
print(f"Mover sequence: {movers8}")
print()

# Quaternary (P3) trajectory
p3_traj = [cycle8[k][3] for k in range(len(cycle8))]
print(f"P3 (quaternary) state trajectory: {p3_traj}")
print(f"P3 states used: {sorted(set(p3_traj))}")
print(f"P3 state visits: {Counter(p3_traj)}")
print()

# State trajectories for each proc
for i in range(n8):
    traj = [cycle8[k][i] for k in range(len(cycle8))]
    print(f"P{i}({ms8[i]}): states used={sorted(set(traj))}, "
          f"visits={dict(Counter(traj))}, "
          f"moves={mover_counts[i]}")

print()

# ═══════════════════════════════════════════════════════════════════
# PART 2: DETERMINED vs FREE ENTRIES
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 2: DETERMINED vs FREE ENTRIES")
print("=" * 70)
print()

det8, det_type8 = compute_determined_entries(cycle8, movers8, n8)
coverage8 = compute_entry_coverage(cycle8, movers8, ms8, n8)

print(f"{'Proc':>5} {'States':>6} {'Total':>6} {'Observed':>8} {'Free':>5} {'Coverage':>8} {'Mover':>6}")
print("-" * 55)
for i in range(n8):
    c = coverage8[i]
    pct = 100 * c['observed'] / c['total']
    print(f"P{i:>3}  {ms8[i]:>5}  {c['total']:>6}  {c['observed']:>8}  {c['free']:>5}  {pct:>7.1f}%  {len(c['mover_set']):>5}")

print()

# Focus on binary procs — are they fully determined?
print("Binary processor analysis:")
for i in [0, 1, 6]:
    c = coverage8[i]
    L_size = ms8[(i-1)%n8]
    R_size = ms8[(i+1)%n8]
    print(f"  P{i}(binary): L∈[0,{L_size-1}] R∈[0,{R_size-1}], "
          f"total={c['total']}, observed={c['observed']}, free={c['free']}")
    if c['free'] > 0:
        # Which (L,S,R) triples are not observed?
        all_triples = {(L,S,R) for L in range(L_size) for S in range(2) for R in range(R_size)}
        free_triples = all_triples - c['observed_set']
        print(f"    Free entries: {sorted(free_triples)}")

print()

# Quaternary analysis
print("Quaternary processor (P3) analysis:")
c = coverage8[3]
L_size = ms8[2]  # P2
R_size = ms8[4]  # P4
print(f"  P3(quaternary): L∈[0,{L_size-1}] R∈[0,{R_size-1}], "
      f"total={c['total']}, observed={c['observed']}, free={c['free']}")
if c['free'] > 0:
    all_triples = {(L,S,R) for L in range(L_size) for S in range(4) for R in range(R_size)}
    free_triples = sorted(all_triples - c['observed_set'])
    print(f"    Free entries ({len(free_triples)}): {free_triples}")

print()


# ═══════════════════════════════════════════════════════════════════
# PART 3: SHADOW ANALYSIS — HOW DOES THE QUATERNARY BREAK THE SHADOW?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 3: SHADOW ANALYSIS — HOW THE QUATERNARY BREAKS THE SHADOW")
print("=" * 70)
print()

# Find shadow cycles (cycles of non-good configs using determined entries)
shadow_cycles8 = find_shadow_cycles(cycle8, det8, ms8, n8, max_cycles=50)
print(f"Shadow cycles found: {len(shadow_cycles8)}")
if shadow_cycles8:
    for idx, sc in enumerate(shadow_cycles8[:5]):
        print(f"  Shadow {idx}: length {len(sc)}")
        # Show first few configs
        for k, cfg in enumerate(sc[:3]):
            print(f"    s_{k} = {cfg}")
        if len(sc) > 3:
            print(f"    ...")
print()

# Classify non-good configs by their "fate" under determined entries
good_set8 = set(cycle8)
all_configs8 = list(iproduct(*(range(m) for m in ms8)))
non_good8 = [c for c in all_configs8 if c not in good_set8]

fate_counts = {'converge': 0, 'shadow_cycle': 0, 'free': 0, 'deadend': 0}
shadow_cycle_set = set()
for sc in shadow_cycles8:
    for cfg in sc:
        shadow_cycle_set.add(cfg)

for c in non_good8:
    # Trace fate
    priv = []
    for i in range(n8):
        L, S, R = c[(i-1)%n8], c[i], c[(i+1)%n8]
        key = (i, L, S, R)
        if key in det8 and det8[key] != S:
            priv.append((i, det8[key]))

    if not priv:
        fate_counts['free'] += 1
    elif c in shadow_cycle_set:
        fate_counts['shadow_cycle'] += 1
    else:
        # Check if any forced move enters C
        enters_C = False
        for proc, new_val in priv:
            new_c = list(c)
            new_c[proc] = new_val
            if tuple(new_c) in good_set8:
                enters_C = True
                break
        if enters_C:
            fate_counts['converge'] += 1
        else:
            fate_counts['deadend'] += 1  # doesn't enter C but not in shadow cycle

print(f"Non-good config classification ({len(non_good8)} total):")
for fate, count in sorted(fate_counts.items()):
    print(f"  {fate}: {count}")
print()

# For the "free" configs: which procs have NO determined privilege?
print("Free configs analysis (no determined privilege):")
free_configs = []
for c in non_good8:
    priv = []
    for i in range(n8):
        L, S, R = c[(i-1)%n8], c[i], c[(i+1)%n8]
        key = (i, L, S, R)
        if key in det8 and det8[key] != S:
            priv.append(i)
    if not priv:
        free_configs.append(c)

if free_configs:
    # Which procs have free entries at these configs?
    free_proc_counts = Counter()
    for c in free_configs:
        for i in range(n8):
            L, S, R = c[(i-1)%n8], c[i], c[(i+1)%n8]
            key = (i, L, S, R)
            if key not in det8:
                free_proc_counts[i] += 1
    print(f"  {len(free_configs)} free configs")
    print(f"  Procs with free entries at free configs: {dict(sorted(free_proc_counts.items()))}")

    # Show a few examples
    for c in free_configs[:5]:
        free_at = []
        for i in range(n8):
            L, S, R = c[(i-1)%n8], c[i], c[(i+1)%n8]
            key = (i, L, S, R)
            if key not in det8:
                free_at.append(f"P{i}({L},{S},{R})")
        print(f"    {c} → free at: {free_at}")
else:
    print("  No free configs — all non-good configs have determined privilege!")

print()

# Critical question: does the actual system converge?
print("Convergence check for n=8 witness:")
# Use the actual transition functions (not just determined entries)
bad_set = set(non_good8)
changed = True
iterations = 0
while changed:
    changed = False
    to_remove = set()
    for cfg in bad_set:
        priv = []
        for i in range(n8):
            L, S, R = cfg[(i-1)%n8], cfg[i], cfg[(i+1)%n8]
            if rules8[i][(L,S,R)] != S:
                priv.append(i)
        # Check if all moves lead to good cycle or already-removed configs
        all_exit = True
        for p in priv:
            L, S, R = cfg[(p-1)%n8], cfg[p], cfg[(p+1)%n8]
            new_S = rules8[p][(L,S,R)]
            new_cfg = list(cfg)
            new_cfg[p] = new_S
            if tuple(new_cfg) in bad_set:
                all_exit = False
                break
        if all_exit:
            to_remove.add(cfg)
    if to_remove:
        bad_set -= to_remove
        changed = True
        iterations += 1

print(f"  Converges: {len(bad_set) == 0} (remaining bad: {len(bad_set)}, iterations: {iterations})")
print()


# ═══════════════════════════════════════════════════════════════════
# PART 4: N=9 EXTENSION — STRUCTURAL ANALYSIS
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 4: N=9 EXTENSION — WHAT CHANGES?")
print("=" * 70)
print()

# n=8 ring: P0(2)-P1(2)-P2(3)-P3(4)-P4(3)-P5(3)-P6(2)-P7(3)
# n=9 ring: P0(2)-P1(2)-P2(3)-P3(4)-P4(3)-P5(3)-P6(2)-P7(3)-P8(3)
#
# Changes:
# - P7's right neighbor: P0(2) → P8(3)
# - P0's left neighbor: P7(3) → P8(3)  [same state count!]
# - P8 is new: L=P7(3), S=P8(3), R=P0(2)

ms9 = (2, 2, 3, 4, 3, 3, 2, 3, 3)
n9 = 9

print(f"n=9 state counts: {ms9}")
print(f"Product: {eval('*'.join(str(m) for m in ms9))}")
print()

print("Neighbor changes from n=8 to n=9:")
print("  P0: left neighbor P7(3) → P8(3) [SAME state count]")
print("  P1-P6: unchanged")
print("  P7: right neighbor P0(2) → P8(3) [CHANGED: 2→3 states]")
print("  P8: NEW proc, L=P7(3), S=P8(3), R=P0(2)")
print()

# P0's transition function can be REUSED (same neighbor state counts)
# P1-P6 can be REUSED
# P7 needs 6 new entries (R=2, new from P8)
# P8 needs full table (18 entries: 3×3×2)

print("Transition function reuse:")
print("  P0: REUSE (12 entries)")
print("  P1: REUSE (12 entries)")
print("  P2: REUSE (24 entries)")
print("  P3: REUSE (36 entries)")
print("  P4: REUSE (27 entries, but wait...)")

# Actually P4's neighbors: L=P3(4), R=P5(3). Same in both n=8 and n=9.
# P5's neighbors: L=P4(3), R=P6(2). Same.
# P6's neighbors: L=P5(3), R=P7(3). Same.

print("  P5: REUSE (18 entries)")
print("  P6: REUSE (18 entries)")
print("  P7: EXTEND (12 → 18 entries, need 6 new for R=2)")
print("  P8: NEW (18 entries)")
print()
print("Total new entries needed: 6 (P7) + 18 (P8) = 24")
print()


# ═══════════════════════════════════════════════════════════════════
# PART 5: CONSTRUCT N=9 GOOD CYCLE
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 5: CONSTRUCT N=9 GOOD CYCLE")
print("=" * 70)
print()

# Strategy: extend n=8 cycle by inserting P8 moves.
# P8 is between P7 and P0. It's ternary (3 states).
#
# In the n=8 cycle, P7 and P0 interact directly.
# In n=9, P8 relays between them.
#
# Key insight: P0's left neighbor is now P8 (not P7).
# For P0 to behave the same, P8 must present the same states as P7 did.
# This means P8 should "track" P7's state.
#
# But P8 can only see P7 (left) and P0 (right).
# If f8(L,S,R) tries to match L (copy from P7), then P8 is privileged
# whenever S ≠ P7's state.
#
# Approach: in the n=9 cycle, add P8 moves right after P7 moves.
# When P7 changes state, P8 follows one step later.

print("Analyzing n=8 mover sequence for P7 move positions:")
p7_moves = [(idx, movers8[idx]) for idx in range(len(movers8)) if movers8[idx] == 7]
print(f"  P7 moves at cycle positions: {[pos for pos, _ in p7_moves]}")
print(f"  P7 move count: {len(p7_moves)}")

# Show P7 and P0 state transitions at P7 move points
for idx, _ in p7_moves:
    c = cycle8[idx]
    c_next = cycle8[(idx + 1) % len(cycle8)]
    p7_old, p7_new = c[7], c_next[7]
    p0_state = c[0]
    p6_state = c[6]
    print(f"  Step {idx}: P7 {p7_old}→{p7_new}, "
          f"context: P6={p6_state}, P0={p0_state}")
print()

# Also show P0 moves (affected by left neighbor change)
p0_moves = [(idx, movers8[idx]) for idx in range(len(movers8)) if movers8[idx] == 0]
print(f"P0 moves at cycle positions: {[pos for pos, _ in p0_moves]}")
for idx, _ in p0_moves:
    c = cycle8[idx]
    c_next = cycle8[(idx + 1) % len(cycle8)]
    p0_old, p0_new = c[0], c_next[0]
    p7_state = c[7]
    p1_state = c[1]
    print(f"  Step {idx}: P0 {p0_old}→{p0_new}, "
          f"context: P7(left)={p7_state}, P1(right)={p1_state}")
print()

# Show the P7-P0 interaction pattern (their states at each cycle step)
print("P7-P0 state pair throughout cycle:")
p7p0_pairs = [(cycle8[k][7], cycle8[k][0]) for k in range(len(cycle8))]
pair_set = set(p7p0_pairs)
print(f"  Distinct (P7,P0) pairs: {sorted(pair_set)}")
print(f"  Count: {len(pair_set)}")
print()


# ═══════════════════════════════════════════════════════════════════
# PART 6: CYCLE EXTENSION — INSERT P8 AS RELAY
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 6: CYCLE EXTENSION STRATEGIES")
print("=" * 70)
print()

# Strategy A: P8 tracks P7 (relay model)
# After each P7 move, insert a P8 move to copy P7's new state.
# This extends cycle length by len(p7_moves).
#
# P8 transition function (relay): f8(L,S,R) = L (copy left neighbor P7)

print("Strategy A: P8 as relay (tracks P7)")
print(f"  New cycle length: {len(cycle8)} + {len(p7_moves)} = {len(cycle8) + len(p7_moves)}")
print()

# Build extended cycle
def extend_cycle_relay(cycle8, movers8, n8):
    """Extend n=8 cycle to n=9 by inserting P8=relay after P7 moves."""
    extended = []
    extended_movers = []

    for idx in range(len(cycle8)):
        c8 = cycle8[idx]
        mover = movers8[idx]

        # Current P8 state = P7 state at this point (relay maintains tracking)
        # We need to figure out P8's state at each point.
        pass

    return extended, extended_movers

# Actually, let me think about P8's state more carefully.
# Initially (at cycle start), P8 should equal P7.
# When P7 moves, P8 is temporarily out of sync until a P8 move follows.
# So in the cycle, after P7 moves, P8 has the OLD P7 state.
# Then P8 moves to match P7's NEW state.

# Let me trace this step by step.
# Start: P8 = P7 at cycle start.
# At each step:
#   If mover is P7: P7 changes, P8 is now stale
#   If mover is P8 (inserted after P7): P8 copies P7, now in sync
#   Other movers: P8 stays the same (should remain in sync if P7 didn't move)

# Problem: P8 affects P0. When P8 is "stale" (just after P7 moved, before P8 copies),
# P0 sees P8 = old P7 value, not new P7 value. This might change P0's behavior.

# Let me trace the extended cycle explicitly.
print("Building extended cycle (relay model):")

# Start with P8 = P7's initial state
p8_state = cycle8[0][7]
extended_cycle = []
extended_movers = []
p8_pending = False  # True when P8 needs to catch up to P7

for idx in range(len(cycle8)):
    c8 = cycle8[idx]
    mover = movers8[idx]

    # Current n=9 config: c8 + (p8_state,)
    c9 = c8 + (p8_state,)
    extended_cycle.append(c9)
    extended_movers.append(mover)

    # After this move, update states
    c8_next = cycle8[(idx + 1) % len(cycle8)]
    if mover == 7:
        # P7 changed, P8 needs to catch up
        p8_pending = True
    elif mover == 0:
        # P0 moved. In n=8, P0's left neighbor was P7. In n=9 it's P8.
        # P0's transition: f0(P8_state, P0_state, P1_state)
        # In n=8: f0(P7_state, P0_state, P1_state)
        # For these to give the same result: need P8_state == P7_state
        # at this point.
        pass

    # Insert P8 move after P7 move if pending
    if p8_pending and mover == 7:
        # After P7 moved, insert P8 move
        c8_after = c8_next
        p8_new = c8_after[7]  # P8 copies P7's new state
        c9_after_p7 = c8_after + (p8_state,)  # P8 still has old state
        extended_cycle.append(c9_after_p7)
        extended_movers.append(8)  # P8 moves
        p8_state = p8_new
        p8_pending = False

# Check: is the extended cycle valid? (Each config single-privilege under some rules)
print(f"  Extended cycle length: {len(extended_cycle)}")
print(f"  P8 moves: {sum(1 for m in extended_movers if m == 8)}")
print()

# Check if extended cycle is a valid cycle (last config → first via last mover)
print("Checking cycle consistency:")
c_last = extended_cycle[-1]
c_first = extended_cycle[0]
last_mover = extended_movers[-1]
# After the last move, we should get back to the first config
print(f"  Last config:  {c_last}")
print(f"  First config: {c_first}")
# Need to apply last_mover to c_last and check if we get c_first
c_last_next_mover = extended_movers[-1]
if c_last_next_mover < 8:
    # n=8 proc moves
    expected_first = list(c_last)
    L, S, R = c_last[(c_last_next_mover-1)%n9], c_last[c_last_next_mover], c_last[(c_last_next_mover+1)%n9]
    # We don't know the exact transition for n=9 yet
    pass
print(f"  Last mover: P{c_last_next_mover}")
print()

# Check P0's context at P0 moves: is P8=P7?
print("P0 move contexts in extended cycle:")
for idx, m in enumerate(extended_movers):
    if m == 0:
        c = extended_cycle[idx]
        p7, p8, p0, p1 = c[7], c[8], c[0], c[1]
        sync = "✓" if p7 == p8 else f"✗ (P7={p7}, P8={p8})"
        print(f"  Step {idx}: P0 sees L=P8={p8}, P0={p0}, R=P1={p1}  sync={sync}")
print()


# ═══════════════════════════════════════════════════════════════════
# PART 7: ANTI-SHADOW ANALYSIS
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 7: ANTI-SHADOW — WHAT ENTRIES BREAK THE SHADOW?")
print("=" * 70)
print()

# For n=8, check: at which non-good configs does the ACTUAL system
# (with free entries filled in) provide privilege, but DETERMINED
# entries alone would NOT?
# These are the configs where free entries are LOAD-BEARING for convergence.

print("Load-bearing free entries in n=8 witness:")
load_bearing = []
for c in non_good8:
    # Privilege from determined entries only
    det_priv = []
    for i in range(n8):
        L, S, R = c[(i-1)%n8], c[i], c[(i+1)%n8]
        key = (i, L, S, R)
        if key in det8 and det8[key] != S:
            det_priv.append(i)

    # Privilege from actual rules
    actual_priv = []
    for i in range(n8):
        L, S, R = c[(i-1)%n8], c[i], c[(i+1)%n8]
        if rules8[i][(L,S,R)] != S:
            actual_priv.append(i)

    # Free entries that create NEW privilege
    new_priv = set(actual_priv) - set(det_priv)
    if new_priv:
        for p in new_priv:
            L, S, R = c[(p-1)%n8], c[p], c[(p+1)%n8]
            load_bearing.append({
                'config': c,
                'proc': p,
                'triple': (L, S, R),
                'action': rules8[p][(L,S,R)],
            })

print(f"  {len(load_bearing)} load-bearing free entries")
# Group by proc
lb_by_proc = defaultdict(list)
for lb in load_bearing:
    lb_by_proc[lb['proc']].append(lb)
for p in sorted(lb_by_proc):
    entries = lb_by_proc[p]
    triples = set(e['triple'] for e in entries)
    print(f"  P{p}({ms8[p]}): {len(entries)} configs, "
          f"triples: {sorted(triples)}")
print()

# The KEY question: which proc has the most load-bearing free entries?
# This is the proc whose free entries are essential for breaking the shadow.
print("Load-bearing free entries by proc:")
for p in range(n8):
    if p in lb_by_proc:
        triples = sorted(set(e['triple'] for e in lb_by_proc[p]))
        for t in triples:
            action = lb_by_proc[p][0]['action']  # they should all agree
            acts = set(e['action'] for e in lb_by_proc[p] if e['triple'] == t)
            print(f"  P{p}: f({t[0]},{t[1]},{t[2]}) = {acts}  "
                  f"(used at {sum(1 for e in lb_by_proc[p] if e['triple'] == t)} configs)")

print()

# ═══════════════════════════════════════════════════════════════════
# PART 8: ATTEMPT FULL N=9 CONSTRUCTION
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 8: FULL N=9 CONSTRUCTION ATTEMPT")
print("=" * 70)
print()

# Build n=9 system with relay P8 and reused transition functions.
# P0-P6: reuse n=8 rules
# P7: reuse n=8 rules + extend for R=2
# P8: relay (f=L) initially, then refine

# First, let's try the pure relay approach
rules9_attempt = [None] * 9

# P0: same as n=8 (left neighbor state count unchanged: 3)
rules9_attempt[0] = dict(rules8[0])

# P1-P6: same as n=8
for i in range(1, 7):
    rules9_attempt[i] = dict(rules8[i])

# P7: extend for R=2 (from P8)
# Reuse old entries (R ∈ {0,1})
rules9_attempt[7] = dict(rules8[7])
# Add new entries for R=2
for L in range(ms9[6]):  # P6: 2 states
    for S in range(ms9[7]):  # P7: 3 states
        # Strategy: for R=2, use same behavior as R=1 (P8's "high" state ~ P0's high state)
        # Or: f(L,S,2) = f(L,S,1) (treat P8=2 like P0=1)
        rules9_attempt[7][(L, S, 2)] = rules8[7].get((L, S, 1), S)

# P8: relay (f = L, copy P7's state)
rules9_attempt[8] = {}
for L in range(ms9[7]):  # P7: 3 states
    for S in range(ms9[8]):  # P8: 3 states
        for R in range(ms9[0]):  # P0: 2 states
            rules9_attempt[8][(L, S, R)] = L  # copy left neighbor

print("Attempt 1: P8=relay(L), P7 extended with f(L,S,2)=f(L,S,1)")

# Verify
def verify_system(ms, rules, verbose=True):
    n = len(ms)
    configs = list(iproduct(*(range(m) for m in ms)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L, S, R = cfg[(i-1)%n], cfg[i], cfg[(i+1)%n]
            if rules[i][(L,S,R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L, S, R = cfg[(proc-1)%n], cfg[proc], cfg[(proc+1)%n]
        new_S = rules[proc][(L,S,R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # Liveness
    for cfg in configs:
        if not privileged(cfg):
            if verbose:
                print(f"  FAIL liveness: {cfg}")
            return None

    # Find good cycle
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            nxt = move(cfg, priv[0])
            single_priv[cfg] = (nxt, priv[0])

    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []
        movers_list = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            visited_global.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers_list.append(mover)
            cur = nxt
        if cur == start and len(path) > 0:
            good_cycle = path
            good_movers = movers_list
            break

    if good_cycle is None:
        if verbose:
            print(f"  FAIL: no good cycle (single_priv={len(single_priv)})")
        return None

    good_set = set(good_cycle)
    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                nxt = move(cfg, p)
                if nxt in bad_set:
                    all_exit = False
                    break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove
            changed = True

    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        if verbose:
            missing = set(range(n)) - movers_seen
            print(f"  FAIL fairness: {missing} never move")
        return None

    if bad_set:
        if verbose:
            print(f"  FAIL convergence: {len(bad_set)} bad configs in cycles")
        return None

    if verbose:
        product = 1
        for m in ms:
            product *= m
        print(f"  PASS  product={product}  cycle={len(good_cycle)}  "
              f"bad_converge={len(configs)-len(good_cycle)}")
    return good_cycle, good_movers

result = verify_system(ms9, rules9_attempt, verbose=True)
if result:
    print("  *** N=9 WITNESS FOUND! ***")
else:
    print("  Attempt 1 failed.")
print()

# Try variations of P7 extension and P8 behavior
print("Trying P8 variations...")
print()

# P8 options beyond pure relay:
# (a) f8(L,S,R) = L (relay P7)
# (b) f8(L,S,R) depends on R (P0) too
# (c) f8 makes P8 privileged in different patterns

# P7 extension options:
# (a) f7(L,S,2) = f7(L,S,1)
# (b) f7(L,S,2) = f7(L,S,0)
# (c) f7(L,S,2) = S (never privileged when R=2)
# (d) f7(L,S,2) = (S+1)%3 (always privileged when R=2)

p7_extensions = {
    'copy_R1': lambda L, S: rules8[7].get((L, S, 1), S),
    'copy_R0': lambda L, S: rules8[7].get((L, S, 0), S),
    'keep_S': lambda L, S: S,
}

p8_behaviors = {
    'relay_L': lambda L, S, R: L,
    'relay_R': lambda L, S, R: R,  # copy P0
    'keep': lambda L, S, R: S,     # never privileged
}

results_found = []
for p7_name, p7_ext in p7_extensions.items():
    for p8_name, p8_func in p8_behaviors.items():
        rules9 = [None] * 9
        for i in range(7):
            rules9[i] = dict(rules8[i])

        # P7 extended
        rules9[7] = dict(rules8[7])
        for L in range(ms9[6]):
            for S in range(ms9[7]):
                rules9[7][(L, S, 2)] = p7_ext(L, S)

        # P8
        rules9[8] = {}
        for L in range(ms9[7]):
            for S in range(ms9[8]):
                for R in range(ms9[0]):
                    rules9[8][(L, S, R)] = p8_func(L, S, R)

        result = verify_system(ms9, rules9, verbose=False)
        status = "PASS" if result else "fail"
        if result:
            results_found.append((p7_name, p8_name))
        print(f"  P7={p7_name:10s}  P8={p8_name:10s}  → {status}")

print()
if results_found:
    print(f"*** FOUND {len(results_found)} working combinations! ***")
    for p7_name, p8_name in results_found:
        print(f"  P7={p7_name}, P8={p8_name}")
else:
    print("No simple combination works. Need deeper search.")
    print()

    # ═══════════════════════════════════════════════════════════════
    # PART 9: Z3-BASED SEARCH FOR P7 EXTENSION + P8 TABLE
    # ═══════════════════════════════════════════════════════════════

    print("=" * 70)
    print("PART 9: Z3-BASED SEARCH OVER P7 EXTENSION + P8 TABLE")
    print("=" * 70)
    print()

    try:
        import z3

        solver = z3.Solver()
        solver.set("timeout", 600000)  # 10 minutes

        # Variables: 6 entries for P7(L,S,2) + 18 entries for P8
        p7_vars = {}
        for L in range(2):  # P6 is binary
            for S in range(3):  # P7 is ternary
                var = z3.Int(f'p7_{L}_{S}_2')
                solver.add(var >= 0, var < 3)
                p7_vars[(L, S, 2)] = var

        p8_vars = {}
        for L in range(3):  # P7 is ternary
            for S in range(3):  # P8 is ternary
                for R in range(2):  # P0 is binary
                    var = z3.Int(f'p8_{L}_{S}_{R}')
                    solver.add(var >= 0, var < 3)
                    p8_vars[(L, S, R)] = var

        # Build fixed rules for P0-P6 (same as n=8)
        fixed_rules = {}
        for i in range(7):
            for key, val in rules8[i].items():
                fixed_rules[(i, key)] = val
        # P7 old entries
        for key, val in rules8[7].items():
            fixed_rules[(7, key)] = val

        # Liveness: every config must have at least one privileged proc
        all_configs9 = list(iproduct(*(range(m) for m in ms9)))
        liveness_count = 0

        for cfg in all_configs9:
            # Check if any fixed proc is privileged
            fixed_priv = False
            for i in range(7):
                L, S, R = cfg[(i-1)%9], cfg[i], cfg[(i+1)%9]
                if fixed_rules[(i, (L,S,R))] != S:
                    fixed_priv = True
                    break

            if fixed_priv:
                continue  # Liveness satisfied by fixed procs

            # Check P7 with old entries
            L7, S7, R7 = cfg[6], cfg[7], cfg[8]
            if R7 < 2:  # Old entry exists
                if fixed_rules[(7, (L7, S7, R7))] != S7:
                    continue  # P7 privileged by old entry

            # Need P7(new) or P8 to be privileged
            # P7 new entry: R7 = 2
            if R7 == 2:
                p7_priv = p7_vars[(L7, S7, 2)] != S7
            else:
                p7_priv = z3.BoolVal(False)

            # P8 entry
            L8, S8, R8 = cfg[7], cfg[8], cfg[0]
            p8_priv = p8_vars[(L8, S8, R8)] != S8

            solver.add(z3.Or(p7_priv, p8_priv))
            liveness_count += 1

        print(f"Added {liveness_count} liveness constraints (of {len(all_configs9)} configs)")

        # Solve iteratively: find table, check full system, exclude if bad
        max_iter = 2000
        attempts = 0
        found_witness = False

        import time
        t0 = time.time()

        for iteration in range(max_iter):
            result = solver.check()
            if result == z3.unsat:
                elapsed = time.time() - t0
                print(f"  UNSAT after {iteration} iterations ({elapsed:.1f}s)")
                print("  This orientation is INFEASIBLE.")
                break
            if result == z3.unknown:
                elapsed = time.time() - t0
                print(f"  UNKNOWN after {iteration} iterations ({elapsed:.1f}s)")
                break

            model = solver.model()

            # Extract tables
            rules9_z3 = [None] * 9
            for i in range(7):
                rules9_z3[i] = dict(rules8[i])

            rules9_z3[7] = dict(rules8[7])
            for key, var in p7_vars.items():
                rules9_z3[7][key] = model[var].as_long()

            rules9_z3[8] = {}
            for key, var in p8_vars.items():
                rules9_z3[8][key] = model[var].as_long()

            # Verify
            check = verify_system(ms9, rules9_z3, verbose=False)
            if check:
                elapsed = time.time() - t0
                print(f"\n*** Z3 FOUND N=9 WITNESS at iteration {iteration}! ({elapsed:.1f}s) ***")
                verify_system(ms9, rules9_z3, verbose=True)
                print(f"\nP7 extension (R=2 entries):")
                for key, var in sorted(p7_vars.items()):
                    print(f"  f7{key} = {model[var].as_long()}")
                print(f"\nP8 table:")
                for L in range(3):
                    for S in range(3):
                        row = [rules9_z3[8][(L,S,R)] for R in range(2)]
                        print(f"  f8({L},{S},*) = {row}")
                found_witness = True
                break

            # Exclude this assignment
            exclude = z3.Or(
                *[p7_vars[k] != model[p7_vars[k]].as_long() for k in p7_vars],
                *[p8_vars[k] != model[p8_vars[k]].as_long() for k in p8_vars]
            )
            solver.add(exclude)
            attempts += 1

            if attempts % 100 == 0:
                elapsed = time.time() - t0
                print(f"  {attempts} attempts, {elapsed:.1f}s...")

        if not found_witness and result != z3.unsat:
            elapsed = time.time() - t0
            print(f"  Exhausted {max_iter} iterations without finding witness ({elapsed:.1f}s)")

    except ImportError:
        print("Z3 not available. Falling back to brute force.")
        print()

        # Brute-force over P7(R=2) and P8 tables
        # P7: 6 entries, each ∈ {0,1,2} → 3^6 = 729 options
        # P8: 18 entries, each ∈ {0,1,2} → 3^18 ≈ 387M options
        # Total: too many for full brute force, but we can try structured subsets

        import time
        t0 = time.time()
        attempts = 0

        # Try P8 = relay(L) with all P7 extensions
        print("Brute-forcing P7 extensions with P8=relay(L)...")
        for p7_bits in range(3**6):
            rules9_bf = [None] * 9
            for i in range(7):
                rules9_bf[i] = dict(rules8[i])
            rules9_bf[7] = dict(rules8[7])

            bits = p7_bits
            for L in range(2):
                for S in range(3):
                    rules9_bf[7][(L, S, 2)] = bits % 3
                    bits //= 3

            # P8 = relay
            rules9_bf[8] = {}
            for L in range(3):
                for S in range(3):
                    for R in range(2):
                        rules9_bf[8][(L, S, R)] = L

            check = verify_system(ms9, rules9_bf, verbose=False)
            attempts += 1
            if check:
                elapsed = time.time() - t0
                print(f"\n*** FOUND at attempt {attempts}! ({elapsed:.1f}s) ***")
                verify_system(ms9, rules9_bf, verbose=True)
                break

            if attempts % 100 == 0:
                elapsed = time.time() - t0
                print(f"  {attempts}/729, {elapsed:.1f}s...")

        else:
            elapsed = time.time() - t0
            print(f"  0/729 with P8=relay ({elapsed:.1f}s)")

        # Try other P8 patterns
        print("\nTrying P8 = copy-right-neighbor...")
        for p7_bits in range(3**6):
            rules9_bf = [None] * 9
            for i in range(7):
                rules9_bf[i] = dict(rules8[i])
            rules9_bf[7] = dict(rules8[7])

            bits = p7_bits
            for L in range(2):
                for S in range(3):
                    rules9_bf[7][(L, S, 2)] = bits % 3
                    bits //= 3

            # P8 = copy right (P0)
            rules9_bf[8] = {}
            for L in range(3):
                for S in range(3):
                    for R in range(2):
                        rules9_bf[8][(L, S, R)] = R

            check = verify_system(ms9, rules9_bf, verbose=False)
            if check:
                print(f"\n*** FOUND! ***")
                verify_system(ms9, rules9_bf, verbose=True)
                break
        else:
            print(f"  0/729 with P8=copy-right")

print()
print("=" * 70)
print("ANALYSIS COMPLETE")
print("=" * 70)
