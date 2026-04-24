#!/usr/bin/env python3
"""
Verify the oans4 pure-mid rank ρ = (N21, N01, N20, N02, -M)
on the exact CUP-2 T_mid table.

Goal: For every score-preserving transition in the pure-mid interval system
(all boundary pairs, interval lengths 1..8), check that ρ strictly decreases.

If any transition violates this, report the exact counterexample.
"""

# T_mid: interior ternary (m_L=3, m_S=3, m_R=3)
T_mid = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
    (2,0,0): 0,  (2,0,1): 0,  (2,0,2): 2,
    (2,1,0): 1,  (2,1,1): 0,  (2,1,2): 2,
    (2,2,0): 0,  (2,2,1): 2,  (2,2,2): 2,
}

def has_202(state, lb, rb):
    """Check if the extended word lb|state|rb has any (2,0,2) triple."""
    ext = [lb] + list(state) + [rb]
    for i in range(1, len(ext) - 1):
        if ext[i-1] == 2 and ext[i] == 0 and ext[i+1] == 2:
            return True
    return False

def get_privileged(state, lb, rb):
    """Return list of privileged positions in state (0-indexed within state)."""
    ext = [lb] + list(state) + [rb]
    priv = []
    for i in range(len(state)):
        L, S, R = ext[i], ext[i+1], ext[i+2]
        if T_mid[(L, S, R)] != S:
            priv.append(i)
    return priv

def fire(state, pos, lb, rb):
    """Fire position pos, return new state."""
    ext = [lb] + list(state) + [rb]
    L, S, R = ext[pos], ext[pos+1], ext[pos+2]
    new_val = T_mid[(L, S, R)]
    new_state = list(state)
    new_state[pos] = new_val
    return tuple(new_state)

def compute_edges(state, lb, rb):
    """Compute edge word for extended state lb|state|rb."""
    ext = [lb] + list(state) + [rb]
    edges = []
    for j in range(len(ext) - 1):
        edges.append((ext[j], ext[j+1]))
    return edges

def compute_rho(state, lb, rb):
    """Compute ρ = (N21, N01, N20, N02, -M) for the extended word."""
    edges = compute_edges(state, lb, rb)
    N21 = sum(1 for e in edges if e == (2, 1))
    N01 = sum(1 for e in edges if e == (0, 1))
    N20 = sum(1 for e in edges if e == (2, 0))
    N02 = sum(1 for e in edges if e == (0, 2))

    M = 0
    for j, e in enumerate(edges):
        if e == (0, 2) or e == (1, 0):
            M += j
        elif e == (1, 2) or e == (2, 0):
            M -= j

    return (N21, N01, N20, N02, -M)

def enumerate_states(k, lb, rb):
    """Enumerate all (2,0,2)-free states of length k with boundaries (lb, rb)."""
    from itertools import product as cart
    states = []
    for s in cart(range(3), repeat=k):
        if not has_202(s, lb, rb):
            states.append(s)
    return states

def verify_rank(max_k=8):
    """Verify ρ strictly decreases on every score-preserving transition."""
    total_edges = 0
    violations = []

    for k in range(1, max_k + 1):
        for lb in range(3):
            for rb in range(3):
                states = enumerate_states(k, lb, rb)
                for s in states:
                    priv = get_privileged(s, lb, rb)
                    for p in priv:
                        s2 = fire(s, p, lb, rb)
                        # Check score-preserving: s2 must be (2,0,2)-free
                        if has_202(s2, lb, rb):
                            continue  # Not score-preserving

                        total_edges += 1
                        rho_before = compute_rho(s, lb, rb)
                        rho_after = compute_rho(s2, lb, rb)

                        if rho_after >= rho_before:
                            violations.append({
                                'k': k, 'lb': lb, 'rb': rb,
                                'state': s, 'pos': p, 'new_state': s2,
                                'rho_before': rho_before,
                                'rho_after': rho_after,
                            })

        print(f"k={k}: checked so far, {total_edges} edges, {len(violations)} violations")

    return total_edges, violations

def verify_acyclicity(max_k=8):
    """Verify the transition graph is acyclic (DAG check)."""
    for k in range(1, max_k + 1):
        for lb in range(3):
            for rb in range(3):
                states = enumerate_states(k, lb, rb)
                state_set = set(states)

                # Build adjacency
                adj = {s: [] for s in states}
                for s in states:
                    priv = get_privileged(s, lb, rb)
                    for p in priv:
                        s2 = fire(s, p, lb, rb)
                        if s2 in state_set:
                            adj[s].append(s2)

                # Cycle detection via DFS
                WHITE, GRAY, BLACK = 0, 1, 2
                color = {s: WHITE for s in states}
                has_cycle = False

                def dfs(u):
                    nonlocal has_cycle
                    if has_cycle:
                        return
                    color[u] = GRAY
                    for v in adj[u]:
                        if color[v] == GRAY:
                            has_cycle = True
                            return
                        if color[v] == WHITE:
                            dfs(v)
                    color[u] = BLACK

                import sys
                sys.setrecursionlimit(100000)
                for s in states:
                    if color[s] == WHITE:
                        dfs(s)

                if has_cycle:
                    print(f"CYCLE FOUND: k={k}, lb={lb}, rb={rb}")
                    return False

        print(f"k={k}: all (lb,rb) acyclic")

    print("All acyclic!")
    return True

def enumerate_local_rewrites():
    """Enumerate all possible local pair-rewrites from T_mid in (2,0,2)-free states.

    When position i fires in extended word y_0...y_{m+1}:
    - Triple = (y_{i}, y_{i+1}, y_{i+2}) where y_{i+1} is the state at position i
    - y_{i+1} changes to S' = T_mid(y_i, y_{i+1}, y_{i+2})
    - The affected edges are e_i = (y_i, y_{i+1}) and e_{i+1} = (y_{i+1}, y_{i+2})
    - They become e'_i = (y_i, S') and e'_{i+1} = (S', y_{i+2})

    Score-preserving means the result is (2,0,2)-free.
    Since we're looking at the local rewrite, we need to check:
    - The new triple at position i: (y_i, S', y_{i+2}) ≠ (2,0,2)
    - But also neighbors: (y_{i-1}, y_i, S') ≠ (2,0,2) and (S', y_{i+2}, y_{i+3}) ≠ (2,0,2)

    For the LOCAL rewrite analysis (as in oans4), we only look at the edge pair change.
    The neighbor constraint depends on the broader context.
    """
    print("\n=== All privileged T_mid entries ===")
    rewrites = []
    for (L, S, R), Sp in T_mid.items():
        if Sp != S:
            old_e1 = (L, S)
            old_e2 = (S, R)
            new_e1 = (L, Sp)
            new_e2 = (Sp, R)
            # Check: is the input state (2,0,2)-free at this position?
            if (L, S, R) == (2, 0, 2):
                print(f"  ({L},{S},{R})→{Sp}: EXCLUDED (is a (2,0,2) triple)")
                continue
            # Check: does the output create (2,0,2) at this position?
            if (L, Sp, R) == (2, 0, 2):
                print(f"  ({L},{S},{R})→{Sp}: creates (2,0,2) — NOT score-preserving locally")
                continue
            print(f"  ({L},{S},{R})→{Sp}: edge rewrite {old_e1}·{old_e2} → {new_e1}·{new_e2}")
            rewrites.append((L, S, R, Sp, old_e1, old_e2, new_e1, new_e2))

    print(f"\nTotal local rewrites: {len(rewrites)}")
    return rewrites

def check_rho_on_rewrites():
    """Check ρ change on each local rewrite.

    For a rewrite at position i changing edges e_{i-1}·e_i to e'_{i-1}·e'_i:
    - ΔN_uv = count of (u,v) in new pair - count of (u,v) in old pair
    - ΔM contribution: for edges that appear/disappear at position i-1 or i
    """
    rewrites = enumerate_local_rewrites()

    print("\n=== ρ analysis per rewrite ===")
    print("ρ = (N21, N01, N20, N02, -M)")

    for L, S, R, Sp, oe1, oe2, ne1, ne2 in rewrites:
        # Change in edge counts at positions i-1 and i
        old_edges = [oe1, oe2]
        new_edges = [ne1, ne2]

        def count_edge(edges, uv):
            return sum(1 for e in edges if e == uv)

        dN21 = count_edge(new_edges, (2,1)) - count_edge(old_edges, (2,1))
        dN01 = count_edge(new_edges, (0,1)) - count_edge(old_edges, (0,1))
        dN20 = count_edge(new_edges, (2,0)) - count_edge(old_edges, (2,0))
        dN02 = count_edge(new_edges, (0,2)) - count_edge(old_edges, (0,2))

        # M = sum_{j: e_j=02} j + sum_{j: e_j=10} j - sum_{j: e_j=12} j - sum_{j: e_j=20} j
        # Change at positions i-1 and i:
        # M changes because edges at positions (i-1) and i change
        # Position i-1 has edge e_{i-1}, position i has edge e_i
        # Let's compute ΔM symbolically in terms of i

        def m_coeff(edge):
            """Return the coefficient of position j in M for edge type edge."""
            if edge == (0, 2): return 1
            if edge == (1, 0): return 1
            if edge == (1, 2): return -1
            if edge == (2, 0): return -1
            return 0

        # ΔM = (coeff(ne1) - coeff(oe1)) * (i-1) + (coeff(ne2) - coeff(oe2)) * i
        # Let's write this as A*(i-1) + B*i = A*i - A + B*i = (A+B)*i - A
        A = m_coeff(ne1) - m_coeff(oe1)
        B = m_coeff(ne2) - m_coeff(oe2)

        # ΔM = (A+B)*i - A for firing at interior position i
        # For the edge-word framework: edges are e_0,...,e_m where e_j = (y_j, y_{j+1})
        # Firing position i (1-indexed in state, which is edge position i in the edge word)
        # changes edges e_{i-1} and e_i (0-indexed edge positions)
        # Actually wait - let me re-derive.
        #
        # Extended word: y_0=a, y_1,...,y_m, y_{m+1}=b
        # Edge j = (y_j, y_{j+1}) for j=0,...,m
        # Position i (1 ≤ i ≤ m) fires: y_i changes to S'
        # Affected edges: e_{i-1} = (y_{i-1}, y_i) → (y_{i-1}, S')
        #                 e_i = (y_i, y_{i+1}) → (S', y_{i+1})
        #
        # ΔM = m_coeff(ne_{i-1})*(i-1) + m_coeff(ne_i)*i
        #     - m_coeff(oe_{i-1})*(i-1) - m_coeff(oe_i)*i
        # = A*(i-1) + B*i  where A = m_coeff(ne_{i-1})-m_coeff(oe_{i-1}), B = m_coeff(ne_i)-m_coeff(oe_i)

        # So Δ(-M) = -ΔM = -A*(i-1) - B*i

        print(f"\n  ({L},{S},{R})→{Sp}: {oe1}·{oe2} → {ne1}·{ne2}")
        print(f"    ΔN21={dN21}, ΔN01={dN01}, ΔN20={dN20}, ΔN02={dN02}")
        print(f"    ΔM = {A}*(i-1) + {B}*i = {A+B}*i + {-A}")

        # Determine which ρ component strictly decreases first
        if dN21 < 0:
            print(f"    → ρ decreases at N21 (Δ={dN21})")
        elif dN21 == 0 and dN01 < 0:
            print(f"    → ρ decreases at N01 (Δ={dN01})")
        elif dN21 == 0 and dN01 == 0 and dN20 < 0:
            print(f"    → ρ decreases at N20 (Δ={dN20})")
        elif dN21 == 0 and dN01 == 0 and dN20 == 0 and dN02 < 0:
            print(f"    → ρ decreases at N02 (Δ={dN02})")
        elif dN21 == 0 and dN01 == 0 and dN20 == 0 and dN02 == 0:
            # Need -M to decrease, i.e. M to increase, i.e. ΔM > 0
            # ΔM = (A+B)*i + (-A) must be > 0 for all valid i
            if A + B == 0 and -A > 0:
                print(f"    → ΔM = {-A} > 0 always (position-independent) → ρ decreases at -M")
            elif A + B == 0 and -A == 0:
                print(f"    *** ΔM = 0 ALWAYS — ρ DOES NOT DECREASE ***")
            elif A + B > 0:
                # ΔM = (A+B)*i - A. For i ≥ 1: ΔM ≥ (A+B) - A = B
                if B > 0:
                    print(f"    → ΔM = {A+B}*i + {-A} ≥ {B} > 0 for i≥1 → ρ decreases at -M")
                elif B == 0:
                    # ΔM = (A+B)*i - A = A*(i-1). For i ≥ 1: ΔM ≥ 0, = 0 when i=1
                    print(f"    *** ΔM = {A}*(i-1), = 0 when i=1 — ρ FAILS at boundary ***")
                else:
                    print(f"    *** ΔM = {A+B}*i + {-A}, need case analysis ***")
            elif A + B < 0:
                print(f"    *** ΔM = {A+B}*i + {-A}, DECREASES for large i — ρ FAILS ***")
            else:
                print(f"    *** Need detailed analysis: ΔM = {A+B}*i + {-A} ***")
        else:
            if dN21 > 0:
                print(f"    *** ρ INCREASES at N21 ***")
            elif dN01 > 0:
                print(f"    *** ρ INCREASES at N01 (with N21 unchanged) ***")
            elif dN20 > 0:
                print(f"    *** ρ INCREASES at N20 (with N21,N01 unchanged) ***")
            elif dN02 > 0:
                print(f"    *** ρ INCREASES at N02 (with N21,N01,N20 unchanged) ***")

if __name__ == "__main__":
    # Step 1: Enumerate and analyze local rewrites
    check_rho_on_rewrites()

    # Step 2: Verify acyclicity for small k
    print("\n\n=== Acyclicity verification ===")
    verify_acyclicity(max_k=8)

    # Step 3: Full ρ verification on all transitions
    print("\n\n=== Full ρ rank verification ===")
    total, violations = verify_rank(max_k=7)
    print(f"\nTotal edges checked: {total}")
    if violations:
        print(f"VIOLATIONS FOUND: {len(violations)}")
        for v in violations[:20]:
            print(f"  k={v['k']}, lb={v['lb']}, rb={v['rb']}")
            print(f"    state={v['state']} → pos={v['pos']} → {v['new_state']}")
            print(f"    ρ: {v['rho_before']} → {v['rho_after']}")
    else:
        print("ALL TRANSITIONS DECREASE ρ — RANK IS VALID")
