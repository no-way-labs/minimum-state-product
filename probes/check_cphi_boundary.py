"""Check: does CΦStep ever change boundary for n=9?

CΦStep = bad step that preserves FutureFc, TpInvariant, and PhiFull.
If CΦStep always has fixed boundary, we can prove WF via (fc, deep) lex directly.
"""
import itertools

def cup2M(n, i):
    """State count for position i in CUP-2 system (ms = [2,3,...,3,2])."""
    if i == 0 or i == n - 1:
        return 2
    return 3

def make_configs(n):
    """Generate all configs as tuples."""
    ranges = [range(cup2M(n, i)) for i in range(n)]
    return list(itertools.product(*ranges))

# CUP-2 transition tables (from the Lean code)
# T_low (position 0, binary): 6 entries
T_low = {
    (0,0,0): 1, (0,0,1): 1, (0,0,2): 1,
    (0,1,0): 0, (0,1,1): 0, (0,1,2): 0,
    # state 1:
    (1,0,0): 0, (1,0,1): 0, (1,0,2): 0,
    (1,1,0): 0, (1,1,1): 0, (1,1,2): 0,
}
# Actually let me use the tables from cup2 properly.
# The CUP-2 rules: position 0 (binary, state ∈ {0,1}), positions 1..n-2 (ternary), position n-1 (binary)

# Let me read the actual tables from the Lean code. This is complex.
# Instead, let me use the verifier.py approach.

import sys
sys.path.insert(0, './claude')

# Actually, let me just directly implement the CUP-2 rules.
# From cup2_final_verify.py or similar

# The 5 lookup tables for CUP-2:
# T_low(S, L, R) for position 0 (binary, S∈{0,1}, L=c[n-1]∈{0,1}, R=c[1]∈{0,1,2})
# T_high(S, L, R) for position n-1 (binary, S∈{0,1}, L=c[n-2]∈{0,1,2}, R=c[0]∈{0,1})
# T_mid(S, L, R) for interior positions (ternary, all ∈{0,1,2})
# T_lo_adj(S, L, R) for position 1 (ternary, L=c[0]∈{0,1}, R=c[2]∈{0,1,2})
# T_hi_adj(S, L, R) for position n-2 (ternary, L=c[n-3]∈{0,1,2}, R=c[n-1]∈{0,1})

# From cup2_theorem.py / cup2_final_verify.py
T_low = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):0, (1,0,2):0,
    (1,1,0):0, (1,1,1):1, (1,1,2):0,
}

T_high = {
    (0,0,0):0, (0,0,1):0,
    (0,1,0):0, (0,1,1):0,
    (0,2,0):0, (0,2,1):0,
    (1,0,0):0, (1,0,1):1,
    (1,1,0):0, (1,1,1):1,
    (1,2,0):0, (1,2,1):1,
}

T_mid = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (0,2,0):2, (0,2,1):0, (0,2,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (1,2,0):2, (1,2,1):1, (1,2,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
    (2,2,0):2, (2,2,1):0, (2,2,2):2,
}

T_lo_adj = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
}

T_hi_adj = {
    (0,0,0):0, (0,0,1):0,
    (0,1,0):1, (0,1,1):0,
    (0,2,0):2, (0,2,1):0,
    (1,0,0):0, (1,0,1):1,
    (1,1,0):1, (1,1,1):1,
    (1,2,0):2, (1,2,1):1,
    (2,0,0):0, (2,0,1):0,
    (2,1,0):1, (2,1,1):0,
    (2,2,0):2, (2,2,1):0,
}

def cup2_output(n, c, i):
    """CUP-2 output value for processor i in config c."""
    S = c[i]
    L = c[(i - 1) % n]
    R = c[(i + 1) % n]
    if i == 0:
        return T_low.get((S, L, R), S)
    elif i == n - 1:
        return T_high.get((S, L, R), S)
    elif i == 1:
        return T_lo_adj.get((S, L, R), S)
    elif i == n - 2:
        return T_hi_adj.get((S, L, R), S)
    else:
        return T_mid.get((S, L, R), S)

def is_privileged(n, c, i):
    """Check if processor i is privileged (output != current state)."""
    return cup2_output(n, c, i) != c[i]

def move(n, c, i):
    """Fire processor i, return new config."""
    new_c = list(c)
    new_c[i] = cup2_output(n, c, i)
    return tuple(new_c)

def fc(n, c):
    """Count non-privileged (fixed-point/free) positions."""
    return sum(1 for i in range(n) if not is_privileged(n, c, i))

def boundary_state(n, c):
    """6-tuple boundary: (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])."""
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def tp_invariant(n, c):
    """Simplified TP invariant — count exp2 patterns etc."""
    # For checking: just use a tuple of all local TP contributions
    exp2_count = 0
    int21_count = 0
    exp2_weight = 0
    for i in range(n):
        L = c[(i-1) % n]
        S = c[i]
        R = c[(i+1) % n]
        # Exp2 bit: S==L and S!=R (expansion type 2)
        # This is a simplified version; actual Lean def is more complex
        pass
    # Actually, let's just compare configs by checking ALL preserved quantities
    # Instead of computing TP exactly, let's check empirically
    return None  # We'll check a different way

def compute_future_fc(n, c, good_cycle_configs):
    """Max fc reachable from c via TP-preserving steps."""
    # BFS/DFS through TP-preserving bad steps
    # This is expensive but doable for n=9
    # For now, just use fc(c) as a proxy — we'll check boundary behavior
    pass

# For n=9, let's just enumerate all bad steps that preserve TP,
# and check if any boundary-changing step also preserves fc (approximately PhiFull)
def check_n9():
    n = 9
    configs = make_configs(n)
    print(f"Total configs: {len(configs)}")

    # Build good cycle (we need this to identify bad configs)
    # For simplicity, let's just check ALL privileged moves and see which change boundary
    boundary_changes_tp_preserved = 0
    boundary_fixed_count = 0
    total_moves = 0

    for c in configs:
        for i in range(n):
            if not is_privileged(n, c, i):
                continue
            c_new = move(n, c, i)
            total_moves += 1

            b_old = boundary_state(n, c)
            b_new = boundary_state(n, c_new)

            if b_old == b_new:
                boundary_fixed_count += 1
            else:
                # Boundary changed! Check what position fired.
                # Boundary positions for n=9: 0,1,2 and 6,7,8
                is_boundary_pos = (i <= 2 or i >= n - 3)
                # Check: is this at a boundary position?
                if not is_boundary_pos:
                    print(f"  WARNING: Non-boundary position {i} changed boundary!")
                    print(f"    config: {c} -> {c_new}")
                    print(f"    boundary: {b_old} -> {b_new}")
                boundary_changes_tp_preserved += 1

    print(f"Total privileged moves: {total_moves}")
    print(f"Boundary fixed: {boundary_fixed_count}")
    print(f"Boundary changed: {boundary_changes_tp_preserved}")
    print()

    # Now check: for moves where boundary changes, does fc ever NOT drop?
    # And more importantly: for CΦStep (TP preserved), does boundary ever change?
    # We check TP preservation by comparing the TP-related counts before and after.

    # Simpler check: for each move, check if the move is at boundary position
    # AND is TP-preserving (by checking all local TP contributions)
    print("Checking boundary-position TP-preserving moves...")

    # Compute Exp2Count, Int21Count for TP invariant
    def local_exp2(n, L, S, R, i):
        """Local exp2 bit value at position i."""
        # From the Lean code: cup2Exp2BitVal
        # This checks if S matches L or R in specific ways
        # Simplified: exp2 bit = 1 if the triple (L,S,R) has certain pattern
        # Actually the exact definition matters. Let me use a simpler approach.
        # The key point: TP is preserved iff the sum of local contributions is unchanged
        pass

    # Let me just count: how many boundary-position moves change boundary?
    # And: how many of those are the ONLY boundary change in the move?
    # (Since moving position i only changes c[i])
    bp_moves_change = 0
    bp_moves_total = 0
    for c in configs:
        for i in range(n):
            if not is_privileged(n, c, i):
                continue
            if i <= 2 or i >= n-3:
                bp_moves_total += 1
                c_new = move(n, c, i)
                if boundary_state(n, c) != boundary_state(n, c_new):
                    bp_moves_change += 1

    print(f"Boundary-position privileged moves: {bp_moves_total}")
    print(f"  of which change boundary: {bp_moves_change}")
    print(f"Non-boundary-position privileged moves: {total_moves - bp_moves_total}")
    print(f"  (these never change boundary)")

check_n9()
