"""
Compare n=7 and n=8 witnesses to understand the extension pattern.

n=7 witness: (3,2,2,2,3,4,3) = rotation of (2,2,3,4,3,3,2)
n=8 witness: (2,2,3,4,3,3,2,3)

Extension: insert P7(3) between P6(2) and P0(2) in the normalized n=7 ring.

Key question: which transition functions change and WHY?
"""

from itertools import product as iproduct
from collections import Counter


# ═══════════════════════════════════════════════════════════════════
# WITNESSES
# ═══════════════════════════════════════════════════════════════════

def witness_n7_original():
    """n=7 witness in original orientation: (3,2,2,2,3,4,3)"""
    ms = (3, 2, 2, 2, 3, 4, 3)
    rules = [
        {(0,0,0):1,(0,0,1):0,(0,1,0):2,(0,1,1):0,(0,2,0):2,(0,2,1):2,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):2,(1,2,1):2,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):1,(2,2,0):2,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):0,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):2,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):0,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):2},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):1,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):1,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):1,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):2,(0,1,2):1,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0,(1,2,0):1,(1,2,1):0,(1,2,2):0,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):0,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):0,(2,2,2):2,(3,0,0):2,(3,0,1):0,(3,0,2):1,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):2,(3,2,1):0,(3,2,2):0},
    ]
    return ms, rules


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


def extract_good_cycle(ms, rules):
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

    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            nxt = move(cfg, priv[0])
            single_priv[cfg] = (nxt, priv[0])

    for start in single_priv:
        path, movers, visited = [], [], set()
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


# ═══════════════════════════════════════════════════════════════════
# PART 1: ROTATE N=7 TO MATCH N=8 ORIENTATION
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 1: N=7 ROTATION + COMPARISON")
print("=" * 70)
print()

ms7_orig, rules7_orig = witness_n7_original()
ms8, rules8 = witness_n8()

# Rotation: n=7 orig P_i → normalized P_{(i-2) mod 7}
# i.e., original P2 → normalized P0, original P3 → normalized P1, etc.
# Rotation by 2 positions: P'_j = P_{j+2 mod 7}

rot = 2
n7 = 7
ms7_rot = tuple(ms7_orig[(i + rot) % n7] for i in range(n7))
print(f"n=7 original:   {ms7_orig}")
print(f"n=7 rotated(+2): {ms7_rot}")
print(f"n=8:             {ms8}")
print()

# Build rotated n=7 rules
# P'_j's rule: maps (L', S', R') where L'=P'_{j-1}, S'=P'_j, R'=P'_{j+1}
# P'_j = P_{j+2}, P'_{j-1} = P_{j+1}, P'_{j+1} = P_{j+3}
# So f'_j(L',S',R') = f_{j+2}(L',S',R') since the input (L,S,R) values are the same
# (just different proc identities, but the function is the same lookup)
rules7_rot = [rules7_orig[(i + rot) % n7] for i in range(n7)]

print("Rotated n=7 state counts (should match n=8 prefix):")
print(f"  n=7 rotated: {ms7_rot}")
print(f"  n=8[0:7]:    {ms8[:7]}")
print(f"  Match: {ms7_rot == ms8[:7]}")
print()

# ═══════════════════════════════════════════════════════════════════
# PART 2: COMPARE TRANSITION FUNCTIONS P1-P5
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 2: COMPARE P1-P5 (should be identical)")
print("=" * 70)
print()

# P1-P5 have same neighbor state counts in both n=7 rotated and n=8
for p in range(1, 6):
    r7 = rules7_rot[p]
    r8 = rules8[p]
    if r7 == r8:
        print(f"  P{p}({ms8[p]}): IDENTICAL ✓")
    else:
        diffs = [(k, r7[k], r8[k]) for k in r7 if k in r8 and r7[k] != r8[k]]
        missing_7 = [k for k in r8 if k not in r7]
        missing_8 = [k for k in r7 if k not in r8]
        print(f"  P{p}({ms8[p]}): DIFFERENT!")
        if diffs:
            print(f"    Changed entries: {diffs}")
        if missing_7:
            print(f"    In n=8 but not n=7: {missing_7}")
        if missing_8:
            print(f"    In n=7 but not n=8: {missing_8}")

print()

# ═══════════════════════════════════════════════════════════════════
# PART 3: COMPARE P0 AND P6 (neighbor changes)
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 3: COMPARE P0 AND P6 (neighbor structure changes)")
print("=" * 70)
print()

# P0 in n=7 rotated: L=P6(2), S=P0(2), R=P1(2)
# P0 in n=8: L=P7(3), S=P0(2), R=P1(2)
# L state count changes: 2 → 3
print("P0 comparison:")
print(f"  n=7: L from P6({ms7_rot[6]}), R from P1({ms7_rot[1]})")
print(f"  n=8: L from P7({ms8[7]}), R from P1({ms8[1]})")
print()

r0_7 = rules7_rot[0]
r0_8 = rules8[0]

# n=7 P0: L ∈ {0,1} (P6 binary), S ∈ {0,1}, R ∈ {0,1}
# n=8 P0: L ∈ {0,1,2} (P7 ternary), S ∈ {0,1}, R ∈ {0,1}
# Common entries: L ∈ {0,1} (shared)
print("  Common entries (L ∈ {0,1}):")
for L in range(2):
    for S in range(2):
        for R in range(2):
            key = (L, S, R)
            v7 = r0_7.get(key, '?')
            v8 = r0_8.get(key, '?')
            match = "✓" if v7 == v8 else f"✗ ({v7}→{v8})"
            print(f"    f0({L},{S},{R}): n7={v7}, n8={v8}  {match}")

print("  New entries in n=8 (L=2):")
for S in range(2):
    for R in range(2):
        key = (2, S, R)
        v8 = r0_8.get(key, '?')
        print(f"    f0(2,{S},{R}): n8={v8}")

print()

# P6 comparison
# n=7: P6(2), L=P5(3), R=P0(2) → R ∈ {0,1}
# n=8: P6(2), L=P5(3), R=P7(3) → R ∈ {0,1,2}
print("P6 comparison:")
print(f"  n=7: L from P5({ms7_rot[5]}), R from P0({ms7_rot[0]})")
print(f"  n=8: L from P5({ms8[5]}), R from P7({ms8[7]})")

r6_7 = rules7_rot[6]
r6_8 = rules8[6]

print("  Common entries (R ∈ {0,1}):")
for L in range(3):
    for S in range(2):
        for R in range(2):
            key = (L, S, R)
            v7 = r6_7.get(key, '?')
            v8 = r6_8.get(key, '?')
            match = "✓" if v7 == v8 else f"✗ ({v7}→{v8})"
            print(f"    f6({L},{S},{R}): n7={v7}, n8={v8}  {match}")

print("  New entries in n=8 (R=2):")
for L in range(3):
    for S in range(2):
        key = (L, S, 2)
        v8 = r6_8.get(key, '?')
        print(f"    f6({L},{S},2): n8={v8}")

print()


# ═══════════════════════════════════════════════════════════════════
# PART 4: COMPARE GOOD CYCLES
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 4: COMPARE GOOD CYCLES")
print("=" * 70)
print()

cycle7_orig, movers7_orig = extract_good_cycle(ms7_orig, rules7_orig)
cycle8, movers8 = extract_good_cycle(ms8, rules8)

# Rotate n=7 cycle
cycle7_rot = [tuple(c[(i + rot) % n7] for i in range(n7)) for c in cycle7_orig]
movers7_rot = [(m - rot) % n7 for m in movers7_orig]

print(f"n=7 cycle length: {len(cycle7_rot)}")
print(f"n=8 cycle length: {len(cycle8)}")
print()

print(f"n=7 movers (rotated): {movers7_rot}")
print(f"n=8 movers:           {movers8}")
print()

# Mover frequencies
freq7 = Counter(movers7_rot)
freq8 = Counter(movers8)
print("Mover frequencies:")
print(f"  n=7: {dict(sorted(freq7.items()))}")
print(f"  n=8: {dict(sorted(freq8.items()))}")
print()

# P6's role: in n=7, P6 wraps to P0. In n=8, P7 is between.
# In n=7, P6 moves how many times?
print(f"P6 moves: n=7={freq7.get(6, 0)}, n=8={freq8.get(6, 0)}")
print(f"P7 moves: n=8={freq8.get(7, 0)}")
print()

# Show state trajectories for P6 and the new P7
for p in [5, 6]:
    traj7 = [cycle7_rot[k][p] for k in range(len(cycle7_rot))]
    traj8 = [cycle8[k][p] for k in range(len(cycle8))]
    print(f"P{p} trajectory:")
    print(f"  n=7: {traj7}")
    print(f"  n=8: {traj8}")

p7_traj = [cycle8[k][7] for k in range(len(cycle8))]
print(f"P7 trajectory (n=8 only): {p7_traj}")
print()


# ═══════════════════════════════════════════════════════════════════
# PART 5: MOVER SEQUENCE ALIGNMENT
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 5: MOVER SEQUENCE ALIGNMENT")
print("=" * 70)
print()

# The n=8 mover sequence should be the n=7 sequence with P7 moves inserted.
# Check: if we remove all P7 moves from n=8, do we get the n=7 sequence?
movers8_no7 = [m for m in movers8 if m != 7]
print(f"n=7 movers (len={len(movers7_rot)}):          {movers7_rot}")
print(f"n=8 movers without P7 (len={len(movers8_no7)}): {movers8_no7}")
print(f"Match: {movers7_rot == movers8_no7}")
print()

# Also check: if we remove P6 and P7 moves from n=8, do we get n=7 without P6?
movers7_no6 = [m for m in movers7_rot if m != 6]
movers8_no67 = [m for m in movers8 if m not in (6, 7)]
print(f"n=7 without P6 (len={len(movers7_no6)}):     {movers7_no6}")
print(f"n=8 without P6,P7 (len={len(movers8_no67)}): {movers8_no67}")
print(f"Match: {movers7_no6 == movers8_no67}")
print()

# Show where P6 and P7 moves are in the n=8 sequence
print("P6 and P7 moves in n=8 sequence:")
for idx, m in enumerate(movers8):
    if m in (6, 7):
        print(f"  Step {idx}: P{m}")
print()

# Pattern: the P6,P7 moves form subsequence [6,7,6,7,...,6,7]
p67_moves = [(idx, m) for idx, m in enumerate(movers8) if m in (6, 7)]
p67_seq = [m for _, m in p67_moves]
print(f"P6,P7 subsequence: {p67_seq}")
print()

# In n=7, P6 moves where?
p6_moves_n7 = [(idx, m) for idx, m in enumerate(movers7_rot) if m == 6]
print(f"P6 moves in n=7: at positions {[idx for idx, _ in p6_moves_n7]}")

# In n=8, (P6,P7) moves where?
print(f"(P6,P7) moves in n=8: at positions {[idx for idx, _ in p67_moves]}")
print()

# Key insight: each P6 move in n=7 became (P6, P7) pair in n=8
# Check: P6 move at position j in n=7 → what in n=8?
# The n=7 P0-P5 subsequence is the same as n=8 P0-P5 subsequence.
# Where P6 appears in n=7, (P6, P7) appears in n=8.

# Count P0-P5 moves before each P6 move in n=7 vs n=8
def moves_before_tail(movers, tail_procs):
    """Count non-tail moves before each tail move."""
    count = 0
    positions = []
    for m in movers:
        if m in tail_procs:
            positions.append(count)
        else:
            count += 1
    return positions

pos7 = moves_before_tail(movers7_rot, {6})
pos8 = moves_before_tail(movers8, {6, 7})
print(f"Non-tail moves before each tail move:")
print(f"  n=7 (tail={{P6}}): {pos7}")
print(f"  n=8 (tail={{P6,P7}}): {pos8}")
print()

# Check the structure: P5 is the boundary between "core" and "tail"
# The tail sequence in n=8 is [6,7,6,7]
# Does this mean: token goes P5→P6→P7→P6→P7 (bouncing)?
print("Tail interaction pattern in n=8:")
for idx, m in enumerate(movers8):
    if m >= 5:
        cfg = cycle8[idx]
        p5, p6, p7 = cfg[5], cfg[6], cfg[7]
        print(f"  Step {idx}: mover=P{m}, (P5,P6,P7)=({p5},{p6},{p7})")

print()

# ═══════════════════════════════════════════════════════════════════
# PART 6: EXTENSION PATTERN ANALYSIS
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 6: EXTENSION PATTERN — HOW TO BUILD N=9")
print("=" * 70)
print()

# From the comparison:
# 1. P1-P5 are IDENTICAL between n=7 (rotated) and n=8
# 2. P0 and P6 have extended tables (new neighbor state count)
# 3. P7 is entirely new
# 4. The mover sequence adds P7 moves paired with P6 moves

# For n=8 → n=9:
# 1. P1-P6 should be IDENTICAL (same neighbor state counts)
# 2. P0's left neighbor: P7(3) → P8(3), SAME state count → P0 unchanged
# 3. P7's right neighbor: P0(2) → P8(3), state count changes 2→3 → P7 extended
# 4. P8 is entirely new

# The n=7→n=8 pattern:
# - P6's R changed from {0,1} to {0,1,2}: P6 needed new entries for R=2
# - P0's L changed from {0,1} to {0,1,2}: P0 needed new entries for L=2

# For n=8→n=9:
# - P7's R changed from {0,1} to {0,1,2}: P7 needs new entries for R=2
# - P0's L: still {0,1,2} → P0 unchanged!

# So the extension is SIMPLER for n=8→n=9 than n=7→n=8!

print("Summary of n=7→n=8 extension:")
print("  P0: L changed (2→3 states). 4 new entries. Common entries: MOSTLY SAME.")
print("  P1-P5: IDENTICAL.")
print("  P6: R changed (2→3 states). 6 new entries. Common entries: checked above.")
print("  P7: NEW (12 entries).")
print()
print("Predicted n=8→n=9 extension:")
print("  P0: UNCHANGED (L still 3 states)")
print("  P1-P6: IDENTICAL")
print("  P7: R changed (2→3 states). 6 new entries needed.")
print("  P8: NEW (18 entries: L=P7(3)×S=P8(3)×R=P0(2))")
print()

# Critical check: did the COMMON entries of P0 and P6 stay the same
# between n=7 and n=8?
print("Did P0's common entries (L∈{0,1}) change between n=7 and n=8?")
p0_changed = False
for L in range(2):
    for S in range(2):
        for R in range(2):
            v7 = rules7_rot[0][(L, S, R)]
            v8 = rules8[0][(L, S, R)]
            if v7 != v8:
                print(f"  CHANGED: f0({L},{S},{R}): {v7} → {v8}")
                p0_changed = True
if not p0_changed:
    print("  All common entries IDENTICAL ✓")
print()

print("Did P6's common entries (R∈{0,1}) change between n=7 and n=8?")
p6_changed = False
for L in range(3):
    for S in range(2):
        for R in range(2):
            v7 = rules7_rot[6][(L, S, R)]
            v8 = rules8[6][(L, S, R)]
            if v7 != v8:
                print(f"  CHANGED: f6({L},{S},{R}): {v7} → {v8}")
                p6_changed = True
if not p6_changed:
    print("  All common entries IDENTICAL ✓")
print()


# ═══════════════════════════════════════════════════════════════════
# PART 7: PREDICT N=9 MOVER SEQUENCE
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 7: PREDICT N=9 MOVER SEQUENCE")
print("=" * 70)
print()

# In n=7→n=8: P6 moves became (P6,P7) pairs
# In n=8→n=9: P7 moves should become (P7,P8) pairs?

# n=8 tail (P6,P7) subsequence: [6,7,6,7,...,6,7]
# n=9 tail (P6,P7,P8) subsequence: [6,7,8,7,8,...] ?

# Actually, the relationship is:
# n=7 tail = {P6}: movers [..., 6, ..., 6]
# n=8 tail = {P6, P7}: movers [..., 6, 7, ..., 6, 7]
# So each P6 move in n=7 became [6, 7] in n=8

# For n=8→n=9: each P7 move in n=8's tail should become [7, 8]?
# n=8 tail: [6, 7, 6, 7]
# n=9 tail: [6, 7, 8, 6, 7, 8]?  → each [6,7] → [6,7,8]?
# Or: [6, 7, 8, 7, 8, 6, 7, 8, 7, 8]? → each P7 → [7,8]

# Let me try the simplest extension: replace each P7 move with [P7, P8]
movers9_pred = []
for m in movers8:
    movers9_pred.append(m)
    if m == 7:
        movers9_pred.append(8)

print(f"n=8 movers (len={len(movers8)}): {movers8}")
print(f"n=9 predicted (len={len(movers9_pred)}): {movers9_pred}")
print(f"  (each P7 → [P7, P8])")
print()

# Also try: insert P8 moves after each P7 move and also independently
# The pattern from n=7→n=8: each P6 → [P6, P7]
# Verify: in n=7 movers, find P6 positions
p6_in_n7 = [i for i, m in enumerate(movers7_rot) if m == 6]
print(f"P6 in n=7: at indices {p6_in_n7}")

# In n=8, find [P6, P7] pairs
pairs_n8 = []
for i in range(len(movers8) - 1):
    if movers8[i] == 6 and movers8[i+1] == 7:
        pairs_n8.append(i)
print(f"(P6,P7) pairs in n=8: at indices {pairs_n8}")
print(f"Number of pairs: {len(pairs_n8)}")
print(f"Number of P6 in n=7: {len(p6_in_n7)}")
print(f"Match count: {len(pairs_n8) == len(p6_in_n7)}")
print()

# So indeed: each P6 move in n=7 became [P6, P7] in n=8.
# By analogy: each P7 move in n=8 should become [P7, P8] in n=9.

# The predicted n=9 mover sequence has length 55 + 4 = 59
# (4 P7 moves each get a P8 appended)

print(f"Predicted n=9 cycle length: {len(movers9_pred)}")
print()


# ═══════════════════════════════════════════════════════════════════
# PART 8: BUILD N=9 CYCLE FROM PREDICTED MOVERS
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("PART 8: BUILD N=9 CYCLE FROM PREDICTED MOVERS")
print("=" * 70)
print()

# Start from the n=8 initial config + P8=0
# P8 tracks P7 (relay model)
# At each step, apply the mover to the current config using:
# - P0-P6: same rules as n=8
# - P7: same rules for R∈{0,1}, need to define R=2
# - P8: relay (f=L, copy P7)

# We'll try to build the cycle forward and check consistency

def build_cycle_from_movers(ms, movers, initial, rules_partial):
    """Build a cycle from mover sequence and partial rules.
    Returns (cycle, determined_entries) or None if inconsistent."""
    n = len(ms)
    cycle = [initial]
    det = {}  # (proc, L, S, R) -> new_S

    for idx, mover in enumerate(movers):
        c = cycle[-1]
        L, S, R = c[(mover-1)%n], c[mover], c[(mover+1)%n]
        key = (mover, L, S, R)

        # Check if we already know this entry
        if key in det:
            new_S = det[key]
        elif rules_partial[mover] is not None and (L, S, R) in rules_partial[mover]:
            new_S = rules_partial[mover][(L, S, R)]
        else:
            return None, None, f"Unknown entry at step {idx}: P{mover}({L},{S},{R})"

        # Mover entry
        det[key] = new_S

        # Non-mover entries
        for i in range(n):
            if i != mover:
                Li, Si, Ri = c[(i-1)%n], c[i], c[(i+1)%n]
                det[(i, Li, Si, Ri)] = Si  # stays same

        new_cfg = list(c)
        new_cfg[mover] = new_S
        cycle.append(tuple(new_cfg))

    return cycle, det, None


# Build initial config: all zeros (following n=8 pattern)
initial9 = (0, 0, 0, 0, 0, 0, 0, 0, 0)

# Partial rules: P0-P6 from n=8, P7 from n=8 (R∈{0,1}), P8 relay
rules9_partial = [None] * 9
for i in range(7):
    rules9_partial[i] = dict(rules8[i])
rules9_partial[7] = dict(rules8[7])
# P8: relay (f = L)
rules9_partial[8] = {}
for L in range(3):
    for S in range(3):
        for R in range(2):
            rules9_partial[8][(L, S, R)] = L

# What P7 entries do we need for R=2?
# Depends on the cycle. Let's try building and see where it fails.
cycle9, det9, error = build_cycle_from_movers(ms9_temp := (2,2,3,4,3,3,2,3,3),
                                               movers9_pred, initial9, rules9_partial)
if error:
    print(f"Cycle build failed: {error}")
    print()

    # The missing entry tells us what P7 needs for R=2
    # Let's try all options
    print("Trying all P7(R=2) extensions to complete the cycle...")
    print()

    from itertools import product as iprod
    success_count = 0

    for p7_bits in range(3**6):
        rules9_test = [None] * 9
        for i in range(7):
            rules9_test[i] = dict(rules8[i])
        rules9_test[7] = dict(rules8[7])
        bits = p7_bits
        for L in range(2):
            for S in range(3):
                rules9_test[7][(L, S, 2)] = bits % 3
                bits //= 3
        rules9_test[8] = {}
        for L in range(3):
            for S in range(3):
                for R in range(2):
                    rules9_test[8][(L, S, R)] = L  # relay

        cycle9, det9, err = build_cycle_from_movers(
            (2,2,3,4,3,3,2,3,3), movers9_pred, initial9, rules9_test)

        if err is None:
            # Check if cycle closes
            if cycle9[-1] == cycle9[0]:
                cycle9 = cycle9[:-1]
                # Check uniqueness
                if len(set(cycle9)) == len(cycle9):
                    print(f"  P7 bits={p7_bits}: cycle CLOSES, length={len(cycle9)}, "
                          f"all unique={'YES' if len(set(cycle9))==len(cycle9) else 'NO'}")
                    success_count += 1

                    # Check single privilege
                    # For this we need full rules including free entries
                    # Let's check if it's promising
                    if success_count <= 3:
                        print(f"    P7(R=2) entries:", end="")
                        bits = p7_bits
                        for L in range(2):
                            for S in range(3):
                                print(f" f({L},{S},2)={bits%3}", end="")
                                bits //= 3
                        print()

    if success_count == 0:
        print("  No P7 extension produces a closing cycle with relay P8.")
        print("  The predicted mover sequence might be wrong.")
else:
    # Check if cycle closes
    if cycle9[-1] == cycle9[0]:
        print(f"Cycle CLOSES! Length = {len(cycle9) - 1}")
    else:
        print(f"Cycle does NOT close: last={cycle9[-1]}, first={cycle9[0]}")

print()
print("=" * 70)
print("ANALYSIS COMPLETE")
print("=" * 70)
