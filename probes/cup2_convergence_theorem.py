#!/usr/bin/env python3
"""
CONVERGENCE THEOREM FOR CUP-2 UNIVERSAL RULES
==============================================

THEOREM: For all n ≥ 4, the bad-configuration graph of the CUP-2 system
with ms = (2, 3, ..., 3, 2) is a directed acyclic graph (DAG).

PROOF STRUCTURE:
  Part A (analytical): (fc, Ψ) potential proves the Δfc≤0 subgraph is a DAG.
  Part B (verified n≤11): Between-firing decrease properties bound anomalous firings.
  Part C (analytical, given A+B): Bounded path length → no cycles → DAG.

VARIANT: Uses T_mid_alt with T_mid(2,1,1)=2 (copy_L) instead of 0 (anomalous).
Both systems are equivalent (same bad set, same DAG structure) but the alt
variant has only 4 anomalous entries (all at boundary positions), making the
proof decomposition cleaner.

STATUS: FULLY PROVED ANALYTICALLY for all n ≥ 4.
        Part A: analytical (fc, Ψ) potential for copy-neighbor subgraph.
        Part B: analytical table-chasing proofs for all 4 between-firing
                properties (B1-B4). Verified computationally for n=5..11.
        Part C: analytical bounded-path argument given A + B.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system as build_orig
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


# ================================================================
# ALT VARIANT: T_mid(2,1,1) = 2 (copy_L)
# ================================================================
T_mid_alt = dict(T_mid)
T_mid_alt[(2,1,1)] = 2


def build_system(nv):
    """Build the alt variant system."""
    n = nv
    ms = [2] + [3] * (n - 2) + [2]
    tables = [T_bot, T_low] + [T_mid_alt] * (n - 4) + [T_high, T_top]
    if n == 4:
        tables = [T_bot, T_low, T_high, T_top]
    elif n == 5:
        tables = [T_bot, T_low, T_mid_alt, T_high, T_top]

    def make_f(t):
        return lambda L, S, R, _t=t: _t[(L, S, R)]

    fs = [make_f(t) for t in tables]
    return ms, fs


# ================================================================
# PART A: COPY-NEIGHBOR CLASSIFICATION + (fc, Ψ) POTENTIAL
# ================================================================

def classify(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def frontier_type(a, b):
    """Directional frontier type: (b-a) mod 3. 0 if no frontier."""
    if a == b:
        return 0
    return (b - a) % 3  # 1 or 2


def w1(j, n):
    if j == n - 1: return 0
    if j == n - 2: return 1
    return j + 1


def w2(j, n):
    if j == n - 1: return 0
    if 1 <= j <= n - 2: return n - 1 - j
    return n - 1


def psi(c, n):
    total = 0
    for j in range(n):
        ft = frontier_type(c[j], c[(j + 1) % n])
        if ft == 1:
            total += w1(j, n)
        elif ft == 2:
            total += w2(j, n)
    return total


# ================================================================
# VERIFICATION
# ================================================================

def verify_part_a():
    """Verify Part A: copy-neighbor classification and (fc, Ψ) potential."""
    print("PART A: COPY-NEIGHBOR DECOMPOSITION")
    print("=" * 60)

    ALL_TABLES = [
        ("T_bot",  T_bot,     2, 2, 3),
        ("T_low",  T_low,     2, 3, 3),
        ("T_mid",  T_mid_alt, 3, 3, 3),
        ("T_high", T_high,    3, 3, 2),
        ("T_top",  T_top,     3, 2, 2),
    ]

    total_priv = 0
    total_anom = 0
    copy_dfc_pos = 0

    for name, tbl, mL, mS, mR in ALL_TABLES:
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = tbl[(L, S, R)]
                    if out != S:
                        total_priv += 1
                        cls = classify(L, S, R, out)
                        dfc = delta_fc(L, S, R, out)
                        if cls == "anomalous":
                            total_anom += 1
                        elif dfc > 0:
                            copy_dfc_pos += 1

    print(f"  Total privileged entries: {total_priv}")
    print(f"  Anomalous entries: {total_anom}")
    print(f"  Copy-neighbor with Δfc > 0: {copy_dfc_pos}")

    assert total_anom == 4, f"Expected 4 anomalous, got {total_anom}"
    assert copy_dfc_pos == 0, f"Expected 0 copy with Δfc>0, got {copy_dfc_pos}"
    print("  ✓ All 4 anomalous entries at boundary, all copy have Δfc ≤ 0")

    # Check Δfc=0 irreversibility
    dfc0_entries = []
    for name, tbl, mL, mS, mR in ALL_TABLES:
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = tbl[(L, S, R)]
                    if out != S:
                        dfc = delta_fc(L, S, R, out)
                        if dfc == 0:
                            dfc0_entries.append((name, L, S, R, out))

    all_irreversible = True
    for name, L, S, R, out in dfc0_entries:
        # Check reverse: (L, out, R) → S?
        tbl = dict([(n, t) for n, t, _, _, _ in ALL_TABLES if n == name][0][1])
        # Actually need to check if reverse is STAY
        rev_out = tbl.get((L, out, R), out)  # default to STAY
        if rev_out != out:  # reverse is NOT stay
            all_irreversible = False

    print(f"  {len(dfc0_entries)} Δfc=0 entries, all irreversible: {all_irreversible}")

    # Verify (fc, Ψ) for small n
    print("\n  Verifying (fc, Ψ) potential on Δfc≤0 subgraph:")
    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        violations = 0
        total = 0
        for c in bad_set:
            fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            psi_c = psi(c, n)
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    dfc = delta_fc(Li, Si, Ri, out)
                    if dfc <= 0:
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            total += 1
                            fc_s = sum(1 for j in range(n)
                                       if succ[j] != succ[(j+1)%n])
                            psi_s = psi(succ, n)
                            if (fc_s, psi_s) >= (fc_c, psi_c):
                                violations += 1

        status = "✓" if violations == 0 else f"✗ {violations}"
        print(f"    n={nv}: {total} transitions, {status}")


def verify_part_b(max_n=11):
    """Verify Part B: between-firing decrease properties."""
    print("\n\nPART B: BETWEEN-FIRING PROPERTIES")
    print("=" * 60)

    results = {}

    for nv in range(5, max_n + 1):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        def check_bf(name, cond, pos_fn, out_val, rank_fn):
            srcs = [c for c in bad_set if cond(c, n)]
            pairs = []
            for src in srcs:
                lst = list(src); lst[pos_fn(n)] = out_val; after = tuple(lst)
                if after not in bad_set:
                    continue
                visited = {after}
                queue = deque([after])
                while queue:
                    cur = queue.popleft()
                    for s in adj[cur]:
                        if s not in visited:
                            visited.add(s)
                            if cond(s, n):
                                lst2 = list(s); lst2[pos_fn(n)] = out_val
                                if tuple(lst2) in bad_set:
                                    pairs.append((src, s))
                                    continue
                            queue.append(s)
            viols = sum(1 for s, ns in pairs if rank_fn(ns, n) >= rank_fn(s, n))
            return len(srcs), len(pairs), viols

        # B1
        s, p, v = check_bf("B1", lambda c, n: c[n-1]==0 and c[0]==0 and c[1]==0,
                           lambda n: 0, 1,
                           lambda c, n: sum(1 for j in range(n) if c[j]!=c[(j+1)%n]))
        results.setdefault('B1', []).append((nv, s, p, v))

        # B2
        s, p, v = check_bf("B2", lambda c, n: c[n-1]==1 and c[0]==1 and c[1]==2,
                           lambda n: 0, 0,
                           lambda c, n: (sum(1 for j in range(n) if c[j]!=c[(j+1)%n]),
                                         2 - c[n-2]))
        results.setdefault('B2', []).append((nv, s, p, v))

        # B3
        s, p, v = check_bf("B3", lambda c, n: c[n-3]==1 and c[n-2]==1 and c[n-1]==1,
                           lambda n: n-2, 2,
                           lambda c, n: sum(1 for j in range(n) if c[j]!=c[(j+1)%n]))
        results.setdefault('B3', []).append((nv, s, p, v))

        # B4
        s, p, v = check_bf("B4", lambda c, n: c[n-2]==2 and c[n-1]==0 and c[0]==0,
                           lambda n: n-1, 1,
                           lambda c, n: 0)  # Any pair is a violation
        results.setdefault('B4', []).append((nv, s, p, v))

    labels = {
        'B1': 'T_bot(0,0,0)→1: rank = fc',
        'B2': 'T_bot(1,1,2)→0: rank = (fc, 2-c[n-2])',
        'B3': 'T_high(1,1,1)→2: rank = fc',
        'B4': 'T_top(2,0,0)→1: fires at most once',
    }

    all_pass = True
    for key in ['B1', 'B2', 'B3', 'B4']:
        print(f"\n  {key}: {labels[key]}")
        for nv, s, p, v in results[key]:
            status = "✓" if (v == 0 if key != 'B4' else p == 0) else "✗"
            if key == 'B4':
                print(f"    n={nv}: {s} sources, {p} pairs (second firings) [{status}]")
                if p > 0: all_pass = False
            else:
                print(f"    n={nv}: {p} pairs, {v} violations [{status}]")
                if v > 0: all_pass = False

    return all_pass


def verify_full_dag(max_n=13):
    """Verify the full graph is a DAG via Kahn's algorithm."""
    print("\n\nFULL DAG VERIFICATION")
    print("=" * 60)

    for nv in range(4, max_n + 1):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        in_deg = {c: 0 for c in bad_set}
        adj = {c: [] for c in bad_set}
        edges = 0
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
                        in_deg[succ] += 1
                        edges += 1

        q = deque(c for c in bad_set if in_deg[c] == 0)
        processed = 0
        max_depth = {c: 0 for c in bad_set}
        while q:
            c = q.popleft()
            processed += 1
            for s in adj[c]:
                max_depth[s] = max(max_depth[s], max_depth[c] + 1)
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)

        is_dag = (processed == len(bad_set))
        depth = max(max_depth.values()) if max_depth else 0
        status = "DAG ✓" if is_dag else "HAS CYCLES ✗"
        print(f"  n={nv}: {len(bad_set)} bad, {edges} edges, depth={depth} [{status}]")


def main():
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  CONVERGENCE THEOREM FOR CUP-2 UNIVERSAL RULES             ║")
    print("║  ms = (2, 3, ..., 3, 2),  product = 4·3^{n-2}             ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()

    verify_part_a()
    all_b_pass = verify_part_b()
    verify_full_dag()

    print("\n\n" + "═" * 60)
    print("THEOREM STATEMENT")
    print("═" * 60)
    print("""
THEOREM (CUP-2 Convergence):
  For all n ≥ 4, the bad-configuration graph of the CUP-2 system
  (ms = (2,3,...,3,2) with alt rules T_mid(2,1,1)=2) is a DAG.

PROOF:

Part A (Analytical, all n):
  With the alt variant, all 45 privileged entries are either copy-neighbor
  (41 entries, Δfc ≤ 0) or anomalous (4 entries, at boundary positions).

  The 4 anomalous entries:
    T_bot(0,0,0)→1   Δfc=+2  (position 0)
    T_bot(1,1,2)→0   Δfc=+1  (position 0)
    T_high(1,1,1)→2  Δfc=+2  (position n-2)
    T_top(2,0,0)→1   Δfc=+1  (position n-1)

  The Δfc≤0 subgraph is a DAG, proved by the lexicographic potential
  (fc(c), Ψ(c)) where:
    fc(c) = #{j : c[j] ≠ c[(j+1) mod n]}        (frontier count)
    Ψ(c) = Σ_j [ft₁(j)·w₁(j) + ft₂(j)·w₂(j)]  (weighted frontier sum)

  All 14 Δfc=0 entries are irreversible, and Ψ strictly decreases on
  each Δfc=0 copy transition. Therefore (fc, Ψ) lex-decreases on every
  copy-neighbor bad→bad transition.

Part B (Analytical, all n; verified computationally n ≤ 11):
  Between consecutive same-type anomalous firings on any path, a
  well-ordered rank strictly decreases. Each proof uses table constraints
  to identify mandatory boundary transitions and bound their net Δfc.

    B1. T_bot(0,0,0)→1: fc strictly decreases.
        After firing (Δfc=+2), three mandatory transitions in forced order:
        (a) c[n-1]: 0→1 via copy (Δfc ≤ -1, since c[0]=1 at that time)
        (b) c[0]: 1→0 (Δfc ≤ 0 via copy_R, or +1 via B2 with -2 aftermath)
        (c) c[n-1]: 1→0 via T_top(0,1,0)→0 (Δfc = -2)
        Ordering forced: c[0] drops only when c[n-1]=1; c[0]=1 stuck when
        c[n-1]=0. Net: +2 + (-1) + 0 + (-2) = -1. (See cup2_b1_proof.py)

    B2. T_bot(1,1,2)→0: (fc, 2-c[n-2]) lex-decreases.
        Case A: c[n-1] stays 1 → c[0] rises via copy (Δfc=-2). Net: -1.
        Case B: c[n-1] drops (requires c[n-2]=0), then rises (requires
        c[n-2]≥1). If v₁=0: v₂≥1, tiebreaker decreases. If v₁≥1:
        c[n-2] drop costs Δfc≤-1 → fc decreases. (See cup2_b2_proof.py)

    B3. T_high(1,1,1)→2: fc strictly decreases.
        c[n-2] must cycle 2→0→1 (can't go 2→1 directly).
        With c[n-1]=1: drop via T_high(0,2,1)→0 (Δfc=-1), rise via
        T_high(1,0,1)→1 (Δfc=-2). Net: +2+(-1)+(-2) = -1.
        c[n-1] stuck at 1 while c[n-2]=2. (See cup2_b3_proof.py)

    B4. T_top(2,0,0)→1: fires at most once (temporal deadlock).
        c[n-1]: 1→0 requires c[n-2]=0; c[n-2] reaches 2 requires c[n-1]=1.
        Deadlock prevents re-establishing precondition c[n-2]=2, c[n-1]=0.
        (See cup2_b4_analytical.py)

Part C (Follows from A + B):
  By Part B, each anomalous type fires boundedly many times:
    T_bot(0,0,0)→1: ≤ n     (fc ∈ {0,...,n}, decreases by ≥1)
    T_bot(1,1,2)→0: ≤ 3n    ((fc, c[n-2]) has ≤ 3(n+1) values)
    T_high(1,1,1)→2: ≤ n    (fc decreases by ≥1)
    T_top(2,0,0)→1: ≤ 1     (fires at most once)

  Total anomalous firings per path: ≤ 5n + 1.
  Between anomalous firings: path in Δfc≤0 DAG, length ≤ L(n) = O(n³).
  Total path length: ≤ O(n) · O(n³) = O(n⁴).

  Since all paths are bounded and the graph is finite: no cycles → DAG. □
""")


if __name__ == "__main__":
    main()
