#!/usr/bin/env python3
"""
RA Trap Universality Part 2: Deep dive into key findings from Part 1.

KEY FINDINGS FROM PART 1:
1. SCC size = 2*C(n,3) for ALL n=5,6,7 with Sol1-like privilege (UNIVERSAL)
2. Formula is 2*C(n,3), NOT 2*C(B,3) — it's about n, not binary count
3. The SCC is NOT transition-function-independent when targets change randomly
4. But Inc/Dec (same privilege structure) give IDENTICAL SCC config sets
5. The SCC lives in {0,1}^n (binary subspace) — even non-binary procs use only {0,1}
6. At n=9, SCC = 252 ≠ 2*C(9,3) = 168, so formula BREAKS at n=9

This script investigates:
A. PRIVILEGE STRUCTURE DEPENDENCE: The SCC is the SAME for all transitions
   with the Sol1-like privilege structure. What exactly determines the SCC?
B. THE n=9 ANOMALY: Why does 2*C(n,3) fail at n=9? What's the real formula?
C. ABOVE-THRESHOLD TRAP PERSISTENCE: GenSol1 has traps even above threshold,
   meaning GenSol1 is INVALID. The trap's existence depends on the privilege
   structure, not just on the state counts.
D. The 20 configs in the n=5 SCC — what ARE they combinatorially?
"""

import itertools
from collections import defaultdict
from math import comb
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from verifier import all_configs, privileged_set, apply_move

# Import infrastructure from part 1
from ra_trap_universality import (
    build_game_graph, get_good_cycle, compute_trap, find_trap_sccs,
    make_gensol1, make_decsol1, analyze_trap
)


def get_scc_configs(ms, fs):
    """Return the set of configs in the largest trap SCC."""
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    if not good_set:
        return set(), priv_map
    trap = compute_trap(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)
    if not sccs:
        return set(), priv_map
    largest = max(sccs, key=len)
    return set(largest), priv_map


if __name__ == '__main__':

    # ===========================================================
    # A. What ARE the 20 SCC configs at n=5?
    # ===========================================================
    print("=" * 70)
    print("A. ANATOMY OF THE 20 SCC CONFIGS (n=5)")
    print("=" * 70)

    ms = [2, 2, 2, 3, 3]
    fs = make_gensol1(ms)
    scc, priv_map = get_scc_configs(ms, fs)

    print(f"\nSCC size: {len(scc)}")
    print(f"\nAll 20 configs (sorted), with privilege sets:")

    # Since they're in {0,1}^5, classify by binary pattern
    for c in sorted(scc):
        priv = sorted(priv_map[c])
        hamming = sum(c)
        print(f"  {c}  H={hamming}  priv={priv}")

    # Hamming weight distribution
    hw_dist = defaultdict(int)
    for c in scc:
        hw_dist[sum(c)] += 1
    print(f"\nHamming weight distribution: {dict(sorted(hw_dist.items()))}")

    # Privilege set distribution
    priv_set_dist = defaultdict(list)
    for c in sorted(scc):
        key = tuple(sorted(priv_map[c]))
        priv_set_dist[key].append(c)
    print(f"\nPrivilege set distribution ({len(priv_set_dist)} distinct sets):")
    for ps, configs in sorted(priv_set_dist.items()):
        print(f"  priv={ps}: {len(configs)} configs")
        for c in configs:
            print(f"    {c}")

    # What are the non-SCC configs in {0,1}^5?
    all_01_5 = list(itertools.product(range(2), repeat=5))
    non_scc = [c for c in all_01_5 if c not in scc]
    print(f"\nNon-SCC configs in {{0,1}}^5 ({len(non_scc)}):")
    for c in sorted(non_scc):
        priv = sorted(priv_map[c])
        print(f"  {c}  priv={priv}")

    # KEY INSIGHT: Check if non-SCC are exactly the "wave" configs
    # Wave = consecutive-1s patterns: 00000, 10000, 11000, 11100, 11110, 11111, 01111, 00111, 00011, 00001
    # These are the "sweep" configs in the good cycle
    print(f"\nGood cycle configs:")
    _, cycle = get_good_cycle(ms, fs)
    for c in cycle:
        print(f"  {c}  priv={sorted(priv_map[c])}")

    # ===========================================================
    # B. Combinatorial characterization of SCC
    # ===========================================================
    print("\n" + "=" * 70)
    print("B. COMBINATORIAL CHARACTERIZATION")
    print("=" * 70)

    # Hypothesis: SCC = {0,1}^n configs with exactly 3 privileged procs
    # (for Sol1-like privilege)
    # Check: in Sol1-like privilege, P0 is privileged iff L==S (i.e., c[n-1]==c[0]),
    # and P_i (i>0) is privileged iff L!=S (i.e., c[i-1]!=c[i]).
    # So privilege count = 1 + #{i>0 : c[i-1]!=c[i]} if c[n-1]==c[0]
    #                    = 0 + #{i>0 : c[i-1]!=c[i]} if c[n-1]!=c[0]
    # In {0,1}^n, c[i-1]!=c[i] means a "transition" in the binary string.
    # For c viewed as a circular binary string:
    #   transitions = #{i : c[i]!=c[(i+1)%n]}
    # P0 priv iff c[n-1]==c[0], i.e., position (n-1,0) is NOT a transition.
    # P_i priv iff c[i-1]!=c[i], i.e., position (i-1,i) IS a transition.

    # Let T = number of circular transitions.
    # If c[n-1]==c[0] (no wrap-transition): priv = 1 + (T - 0) = 1 + T... wait
    # More carefully: transitions at positions (0,1), (1,2), ..., (n-2,n-1), (n-1,0)
    # P0 priv iff no transition at (n-1,0)
    # P_i (i>=1) priv iff transition at (i-1,i)

    # So #priv = [1 if no trans at (n-1,0) else 0] + [# trans at (i-1,i) for i=1..n-1]
    #          = [1 if no trans at (n-1,0)] + [total trans - trans at (n-1,0)]
    #          = 1 + T - 2*trans(n-1,0) if we include wrap trans
    # Wait, let me be more precise.

    # Define: for i in {0,...,n-1}, "edge i" = (i, (i+1)%n)
    # transition(edge i) = 1 if c[i] != c[(i+1)%n]
    # T = total transitions = sum over all edges
    # P0 priv iff c[n-1]==c[0], i.e., NOT transition(edge n-1)
    # P_i (i>=1) priv iff c[i-1]!=c[i], i.e., transition(edge i-1)
    # So P_i priv iff transition(edge i-1) for i>=1.
    # And P_0 priv iff NOT transition(edge n-1).
    # Privilege set = {0 if NOT trans(edge n-1)} ∪ {i : 1<=i<=n-1, trans(edge i-1)}
    #              = {0 if NOT trans(n-1)} ∪ {i+1 : 0<=i<=n-2, trans(i)}
    # #priv = [1-trans(n-1)] + sum_{i=0}^{n-2} trans(i)
    #       = 1 - trans(n-1) + T - trans(n-1)
    #       = 1 + T - 2*trans(n-1)
    # If wrap edge has transition: #priv = T - 1
    # If wrap edge has no transition: #priv = T + 1

    print("\nVerifying: #priv = T+1 (no wrap trans) or T-1 (wrap trans)")
    print("where T = total circular transitions")

    for n_val in [5, 6, 7]:
        ms_t = [2] * n_val
        fs_t = make_gensol1(ms_t)
        configs_t, pm_t, _ = build_game_graph(ms_t, fs_t)

        all_ok = True
        for c in configs_t:
            T = sum(1 for i in range(n_val) if c[i] != c[(i+1) % n_val])
            wrap_trans = (c[n_val-1] != c[0])
            expected = T - 1 if wrap_trans else T + 1
            actual = len(pm_t[c])
            if expected != actual:
                all_ok = False
                print(f"  FAIL at n={n_val}: c={c}, T={T}, wrap={wrap_trans}, expected={expected}, actual={actual}")
                break
        print(f"  n={n_val}: formula verified = {all_ok}")

    # So SCC = {c in {0,1}^n : #priv = 3}
    # For no-wrap: T+1=3 -> T=2
    # For wrap: T-1=3 -> T=4
    # Count:
    # Circular binary strings of length n with exactly T transitions:
    # Transitions partition the circle into runs of 0s and 1s.
    # T transitions = T/2 runs of 0 + T/2 runs of 1 (T must be even for circular binary string)
    # T=2: 1 run of 0, 1 run of 1. Each has length from 1 to n-1, sum=n.
    # Number of circular strings with T=2: n (n choices for run length of 0s, from 1 to n-1, but circular: n choices)
    # Actually: # = n (each position can be the start of the 0-run; but strings are distinct).
    # Wait, need to think carefully since strings are labeled (positions matter).

    # For a circular binary string of length n with exactly T=2k transitions:
    # There are k runs of 0 and k runs of 1.
    # Lengths of 0-runs: a_1,...,a_k with sum = #{0s}
    # Lengths of 1-runs: b_1,...,b_k with sum = #{1s}
    # For fixed k, #{0s}+#{1s}=n.
    # But also need to know WHERE the runs start. Given the run lengths,
    # the circular arrangement is determined up to rotation of the run sequence.
    # Actually for labeled positions: fix that position 0 starts a run.
    # If c[0]=0: the arrangement of runs is (0-run of a_1, 1-run of b_1, ..., 0-run of a_k, 1-run of b_k)
    # and the starting position of the first 0-run determines everything.
    # For labeled circular strings, the count is:
    #   C(#{0s}-1, k-1) * C(#{1s}-1, k-1) * something...
    # This is getting complicated. Let me just count directly.

    print("\n\nTransition count distribution in {0,1}^n:")
    for n_val in [5, 6, 7, 8, 9]:
        dist = defaultdict(int)
        for c in itertools.product(range(2), repeat=n_val):
            T = sum(1 for i in range(n_val) if c[i] != c[(i+1) % n_val])
            wrap = (c[n_val-1] != c[0])
            priv = T - 1 if wrap else T + 1
            dist[priv] += 1
        print(f"  n={n_val}: priv_dist = {dict(sorted(dist.items()))}")
        count_3priv = dist.get(3, 0)
        print(f"    #priv=3: {count_3priv}, 2*C(n,3)={2*comb(n_val,3)}, match={count_3priv == 2*comb(n_val,3)}")

    # ===========================================================
    # C. Why does n=9 SCC=252 ≠ 168?
    # ===========================================================
    print("\n" + "=" * 70)
    print("C. THE n=9 SCC ANOMALY")
    print("=" * 70)

    ms_9 = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    fs_9 = make_gensol1(ms_9)
    scc_9, pm_9 = get_scc_configs(ms_9, fs_9)

    print(f"\nSCC size: {len(scc_9)}")

    # Privilege distribution in SCC
    priv_dist_9 = defaultdict(int)
    for c in scc_9:
        priv_dist_9[len(pm_9[c])] += 1
    print(f"Privilege dist in SCC: {dict(sorted(priv_dist_9.items()))}")

    # All 3 SCCs
    configs_9, pm_9_full, succ_9 = build_game_graph(ms_9, fs_9)
    good_9, cycle_9 = get_good_cycle(ms_9, fs_9)
    trap_9 = compute_trap(configs_9, pm_9_full, succ_9, good_9)
    sccs_9 = find_trap_sccs(trap_9, succ_9)

    print(f"\nAll trap SCCs: {[len(s) for s in sccs_9]}")
    total_scc_9 = sum(len(s) for s in sccs_9)
    print(f"Total SCC configs: {total_scc_9}")
    print(f"2*C(9,3)={2*comb(9,3)}, sum of all SCCs={total_scc_9}")

    for i, scc_i in enumerate(sccs_9):
        priv_dist = defaultdict(int)
        for c in scc_i:
            priv_dist[len(pm_9_full[c])] += 1
        in_01 = all(all(v <= 1 for v in c) for c in scc_i)
        print(f"\n  SCC {i}: size={len(scc_i)}, priv_dist={dict(sorted(priv_dist.items()))}, in {{0,1}}^9={in_01}")

    # Check: does the total = 2*C(9,3) + something predictable?
    # 252 + 168 + 72 = 492
    # 2*C(9,3) = 168. Hmm. 252 = 3*C(9,3)/2... no.
    # 252 = C(10,5)/2? No, C(10,5)=252. Interesting!
    # 168 = 2*C(9,3) = 2*84 = 168. One SCC IS 2*C(9,3)!
    # 72 = ?
    # 252 = C(10,5) = 252. Coincidence?

    print(f"\n  252 = C(10,5)? {252 == comb(10,5)}")
    print(f"  168 = 2*C(9,3)? {168 == 2*comb(9,3)}")
    print(f"  72 = 2*C(9,2)? {72 == 2*comb(9,2)}")

    # ===========================================================
    # D. Does the SCC exist EVEN above threshold for GenSol1?
    # ===========================================================
    print("\n" + "=" * 70)
    print("D. GENSOL1 TRAP ABOVE THRESHOLD — IS GENSOL1 INVALID?")
    print("=" * 70)

    # GenSol1 at n=5: the trap existing means GenSol1 is INVALID for those ms.
    # Let's verify: is GenSol1 actually a valid self-stabilizing system?
    from verifier import verify_system

    test_ms = [
        [2, 2, 2, 3, 3],       # sub-threshold, expected invalid
        [2, 2, 2, 3, 4],       # M_5=96, expected invalid (GenSol1 can't handle mixed)
        [3, 3, 3, 3, 3],       # product=243, GenSol1 = Sol1(K=3) — invalid since K<n+1=6
        [6, 6, 6, 6, 6],       # product=7776, Sol1(K=6) — valid since K=n+1
        [2, 2, 2, 4, 4],       # product=128 > threshold — but GenSol1 probably invalid
    ]

    for ms_t in test_ms:
        n = len(ms_t)
        product = 1
        for m in ms_t:
            product *= m
        fs = make_gensol1(ms_t)
        result = verify_system(ms_t, fs)
        r = analyze_trap(ms_t, fs)
        valid = result['valid']
        scc_sz = r['scc_sizes'][0] if r['scc_sizes'] else 0
        print(f"  ms={ms_t} p={product}: valid={valid}, trap={r['trap_size']}, scc={scc_sz}")

    print("\n  KEY: GenSol1 is ALWAYS invalid for mixed ms or K<n+1.")
    print("  The trap exists because GenSol1 itself is broken, not because of the state counts.")

    # ===========================================================
    # E. The REAL question: does a VALID system exist with trap=0?
    # ===========================================================
    print("\n" + "=" * 70)
    print("E. VALID SYSTEMS — do they have empty traps?")
    print("=" * 70)

    # Build actual valid systems and check their traps

    # Sol3 n=5 (valid, ms=(3,3,3,3,3))
    def get_sol3(n):
        ms = [3] * n
        def f_bottom(L, S, R):
            return (S - 1) % 3 if (S + 1) % 3 == R else S
        def f_top(L, S, R):
            return (L + 1) % 3 if L == R and (L + 1) % 3 != S else S
        def f_middle(L, S, R):
            if (S + 1) % 3 == L: return L
            if (S + 1) % 3 == R: return R
            return S
        return ms, [f_bottom] + [f_middle] * (n - 2) + [f_top]

    # Sol1 n=5 K=6 (valid)
    def get_sol1(n, K):
        ms = [K] * n
        def f_dist(L, S, R):
            return (S + 1) % K if L == S else S
        def f_other(L, S, R):
            return L if L != S else S
        return ms, [f_dist] + [f_other] * (n - 1)

    print("\n  Valid systems:")
    for name, (ms_v, fs_v) in [
        ("Sol3 n=5", get_sol3(5)),
        ("Sol1 n=5 K=6", get_sol1(5, 6)),
        ("Sol3 n=4", get_sol3(4)),
    ]:
        result = verify_system(ms_v, fs_v)
        r = analyze_trap(ms_v, fs_v)
        print(f"  {name}: valid={result['valid']}, trap={r['trap_size']}, scc_sizes={r['scc_sizes']}")

    # ===========================================================
    # F. The CRITICAL test: GenSol1 privilege structure is SPECIFIC.
    #    What if we use a DIFFERENT privilege structure?
    # ===========================================================
    print("\n" + "=" * 70)
    print("F. PRIVILEGE STRUCTURE COMPARISON")
    print("  Sol1-like vs Sol3-like privilege on same ms")
    print("=" * 70)

    ms_5 = [3, 3, 3, 3, 3]
    n = 5

    # Sol3 privilege
    _, fs_sol3 = get_sol3(5)
    configs_sol3, pm_sol3, _ = build_game_graph(ms_5, fs_sol3)

    # GenSol1 privilege
    fs_gen = make_gensol1(ms_5)
    configs_gen, pm_gen, _ = build_game_graph(ms_5, fs_gen)

    # Compare privilege distributions
    sol3_pdist = defaultdict(int)
    gen_pdist = defaultdict(int)
    for c in configs_sol3:
        sol3_pdist[len(pm_sol3[c])] += 1
        gen_pdist[len(pm_gen[c])] += 1
    print(f"\n  ms={ms_5}")
    print(f"  Sol3 privilege dist: {dict(sorted(sol3_pdist.items()))}")
    print(f"  GenSol1 privilege dist: {dict(sorted(gen_pdist.items()))}")

    # How many configs differ in privilege?
    diff = sum(1 for c in configs_sol3 if set(pm_sol3[c]) != set(pm_gen[c]))
    print(f"  Configs with different privilege sets: {diff}/{len(configs_sol3)}")

    # ===========================================================
    # G. The 20-config SCC at n=5: is it the SAME set across all
    #    Sol1-like privilege systems, regardless of state counts?
    # ===========================================================
    print("\n" + "=" * 70)
    print("G. IS THE SCC THE SAME {0,1}^n SET ACROSS STATE VECTORS?")
    print("=" * 70)

    # For all n=5 multisets with Sol1-like privilege,
    # extract the SCC and project to {0,1}^5
    ref_scc_set = None
    for ms_t, desc in [
        ([2, 2, 2, 3, 3], "3B+2T"),
        ([2, 2, 2, 3, 4], "3B+T+Q"),
        ([2, 2, 2, 2, 3], "4B+T"),
        ([2, 3, 2, 3, 2], "non-consec"),
        ([2, 2, 2, 2, 2], "all-B"),
        ([2, 2, 2, 4, 4], "3B+2Q"),
    ]:
        fs_t = make_gensol1(ms_t)
        scc_t, _ = get_scc_configs(ms_t, fs_t)
        if ref_scc_set is None:
            ref_scc_set = scc_t
        match = scc_t == ref_scc_set
        print(f"  {desc:15s} ms={ms_t}: SCC size={len(scc_t):3d}, matches ref? {match}")
        if not match and len(scc_t) == 20:
            # Check if same after projection to binary
            proj_ref = set(tuple(min(c[i], 1) for i in range(5)) for c in ref_scc_set)
            proj_t = set(tuple(min(c[i], 1) for i in range(5)) for c in scc_t)
            print(f"    Binary projection match? {proj_ref == proj_t}")

    # ===========================================================
    # H. SUMMARY: What determines the SCC?
    # ===========================================================
    print("\n" + "=" * 70)
    print("H. SUMMARY: THE SCC IS DETERMINED BY...")
    print("=" * 70)

    print("""
FINDINGS:
1. SCC size = 2*C(n,3) for n=5,6,7 with Sol1-like privilege structure.
   - This is the number of {0,1}^n configs with exactly 3 privileged procs.
   - Formula: #priv = T+1 (no wrap) or T-1 (wrap), where T = circular transitions.
   - 3-privileged means T=2 (no wrap) or T=4 (wrap).

2. The SCC is NOT transition-function-independent in general.
   - Random transitions with random privilege structures give wildly different SCCs.
   - But: given FIXED Sol1-like privilege (P0: L==S, others: L!=S), the SCC IS
     the same regardless of the target values.

3. The SCC depends on:
   - The PRIVILEGE STRUCTURE (which configs are privileged, which aren't)
   - NOT on the specific transition values (what f maps to when privileged)

4. The SCC lives in {0,1}^n: even non-binary procs only use values 0 and 1.
   This is because Sol1-like privilege reduces to a binary predicate.

5. At n=9, the formula breaks: SCC=252 ≠ 168=2*C(9,3).
   There are 3 distinct SCCs (252, 168, 72) totaling 492.
   This needs further investigation.

6. GenSol1 is ALWAYS invalid for mixed/small state counts.
   The trap exists because GenSol1 is broken, not because of state counts per se.
   Valid systems (Sol3, Sol1 with K>=n+1) have EMPTY traps.

CONCLUSION:
The "privilege-determined trap" is NOT a universal proof of the lower bound.
It's an artifact of the Sol1-like privilege structure. Different transition
functions (different privilege structures) give different SCCs.
The existing proof via entry conflict / shadow cycles remains necessary.
""")
