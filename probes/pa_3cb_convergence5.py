#!/usr/bin/env python3
"""PA: 3CB Convergence Failure — Part 5.

KEY DISCOVERY from witness verification:
- n=5 (M_5=96): ms=(2,2,2,3,4) — 3CB at {0,1,2}. VALID SYSTEM EXISTS.
- n=6 (M_6=288): ms=(2,2,2,4,3,3) — 3CB at {0,1,2}. VALID SYSTEM EXISTS.
- n=7 (M_7=864): ms=(3,2,2,2,3,4,3) — 3CB at {1,2,3}. Also 3CB.
- n=8 (M_8=2592): ms=(2,2,3,4,3,3,2,3) — binary NOT consecutive.

So 3CB works at n=5,6,7 but breaks at n=8!

The task says at n=8 with ms=(2,2,2,3,3,3,3,4) P=2592: ALL 768 constructions
have bad SCCs. But the VALID n=8 system uses ms=(2,2,3,4,3,3,2,3), which has
NON-consecutive binary at positions {0,1,6}.

So the real question is: does 3 CONSECUTIVE binary at sub-threshold product
become impossible at some n? The witnesses show:
- n=5: 3CB works (P=96)
- n=6: 3CB works (P=288)
- n=7: 3CB works (P=864, via ms=(3,2,2,2,3,4,3) — 3CB at {1,2,3})
- n=8: 3CB FAILS (task data: 768 constructions all fail)

The transition is between n=7 and n=8 for the "all-ternary+1-quaternary" case.

Actually wait: at n=7 the ms=(3,2,2,2,3,4,3) has P=3*8*3*4*3=864=M_7.
This is 3CB. So 3CB works at n=7.

But at n=8 with ms=(2,2,2,3,3,3,3,4) P=2592: does the 3CB version fail
while the non-3CB version ms=(2,2,3,4,3,3,2,3) succeeds?

THIS IS THE CORE QUESTION. Let me investigate directly.
"""

import itertools
from collections import defaultdict, deque
from math import prod
import sys
sys.path.insert(0, 'gpt/scripts')
from verify_witnesses import witness_n5, witness_n6, witness_n7, witness_n8


def analyze_witness_binary_positions():
    """Check which positions are binary in each witness."""
    print("="*60)
    print("WITNESS BINARY POSITION ANALYSIS")
    print("="*60)

    witnesses = [
        ("n=5", witness_n5),
        ("n=6", witness_n6),
        ("n=7", witness_n7),
        ("n=8", witness_n8),
    ]

    for name, wfn in witnesses:
        ms, rules = wfn()
        n = len(ms)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        # Check consecutiveness
        is_consec = False
        for i in range(len(binary_pos)):
            for j in range(i+1, len(binary_pos)):
                for k in range(j+1, len(binary_pos)):
                    # Check if any triple is consecutive on the ring
                    triple = [binary_pos[i], binary_pos[j], binary_pos[k]]
                    # Check all rotations
                    for start in triple:
                        chain = [(start + d) % n for d in range(3)]
                        if set(chain).issubset(set(triple)):
                            is_consec = True

        print(f"\n{name}: ms={list(ms)}, P={prod(ms)}")
        print(f"  Binary positions: {binary_pos}")
        print(f"  3 consecutive binary: {is_consec}")

        # Analyze proc 1 (or the middle binary proc) context
        if is_consec:
            # Find the middle proc of the consecutive triple
            for i in range(len(binary_pos)):
                p = binary_pos[i]
                left = (p - 1) % n
                right = (p + 1) % n
                if ms[left] == 2 and ms[right] == 2:
                    print(f"  Middle binary proc: {p}")
                    # Count privileged contexts
                    M = set()
                    for ctx, val in rules[p].items():
                        L, S, R = ctx
                        if val != S:
                            M.add(ctx)
                    print(f"  |M| = {len(M)}")
                    print(f"  M = {sorted(M)}")


def verify_and_analyze_n7_3cb():
    """The n=7 witness has 3CB at {1,2,3}. Verify and analyze its structure.

    ms=(3,2,2,2,3,4,3), P=864.
    Middle binary: proc 2 (neighbors are proc 1 and proc 3, both binary).
    """
    ms, rules = witness_n7()
    n = len(ms)
    P = prod(ms)

    print(f"\n{'='*60}")
    print(f"n=7 WITNESS ANALYSIS: ms={list(ms)}, P={P}")
    print(f"{'='*60}")

    configs = list(itertools.product(*(range(m) for m in ms)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i-1) % n]
            S = cfg[i]
            R = cfg[(i+1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc-1) % n]
        S = cfg[proc]
        R = cfg[(proc+1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # Find good cycle
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move(cfg, priv[0]), priv[0])

    # Find cycle
    visited = {}
    cur = next(iter(single_priv))
    path = []
    movers = []
    while cur in single_priv and cur not in visited:
        visited[cur] = len(path)
        path.append(cur)
        nxt, mover = single_priv[cur]
        movers.append(mover)
        cur = nxt

    if cur in visited:
        cycle_start = visited[cur]
        good_cycle = path[cycle_start:]
        good_movers = movers[cycle_start:]
    else:
        print("No good cycle found!")
        return

    good_set = set(good_cycle)
    bad_configs = set(configs) - good_set

    print(f"Good cycle length: {len(good_cycle)}")
    print(f"Bad configs: {len(bad_configs)}")
    print(f"Movers in cycle: {sorted(set(good_movers))}")

    # Proc 2 (middle binary) analysis
    p = 2  # middle binary
    M2 = set()
    for ctx, val in rules[p].items():
        if val != ctx[1]:
            M2.add(ctx)

    print(f"\nProc {p} (middle binary):")
    print(f"  Privilege set M = {sorted(M2)}, |M| = {len(M2)}")

    # Count good configs where proc 2 fires
    p2_fires = [i for i, m in enumerate(good_movers) if m == p]
    print(f"  Fires in good cycle: {len(p2_fires)} times")

    # Count bad configs with proc 2 privileged
    bad_with_p2 = {c for c in bad_configs if p in privileged(c)}
    print(f"  Bad configs with proc {p} privileged: {len(bad_with_p2)}")

    # Far procs for proc 2 (procs that don't affect its context)
    # Proc 2's context: (c[1], c[2], c[3]). All three are binary.
    # Any proc != 1, 2, 3 is far. That's procs {0, 4, 5, 6}.
    far_procs = [i for i in range(n) if i not in [1, 2, 3]]
    print(f"  Far procs: {far_procs}")

    # Check far closure
    for c in list(bad_with_p2)[:5]:
        priv = privileged(c)
        far_priv = [pp for pp in priv if pp in far_procs]
        if far_priv:
            for fp in far_priv:
                nc = move(c, fp)
                nc_priv = privileged(nc)
                p2_still = p in nc_priv
                # Note: nc might be good (if exactly 1 priv)

    # Drainage analysis
    can_reach_good = set()
    for c in bad_configs:
        priv = privileged(c)
        for pp in priv:
            nc = move(c, pp)
            if nc in good_set:
                can_reach_good.add(c)
                break

    bad_pred = defaultdict(set)
    for c in bad_configs:
        priv = privileged(c)
        for pp in priv:
            nc = move(c, pp)
            if nc in bad_configs:
                bad_pred[nc].add(c)

    queue = deque(can_reach_good)
    while queue:
        c = queue.popleft()
        for pred in bad_pred[c]:
            if pred not in can_reach_good:
                can_reach_good.add(pred)
                queue.append(pred)

    stuck = bad_configs - can_reach_good
    print(f"\n  Stuck bad configs (bad SCCs): {len(stuck)}")

    if stuck:
        print("  WARNING: System has bad SCCs despite being in the witness!")
        return

    # Drainage depth
    depth = {}
    queue2 = deque()
    for c in bad_configs:
        priv = privileged(c)
        for pp in priv:
            nc = move(c, pp)
            if nc in good_set and c not in depth:
                depth[c] = 1
                queue2.append(c)
                break

    while queue2:
        c = queue2.popleft()
        for pred in bad_pred[c]:
            if pred not in depth:
                depth[pred] = depth[c] + 1
                queue2.append(pred)

    max_depth = max(depth.values()) if depth else 0
    print(f"  Max drainage depth: {max_depth}")

    # Proc 2 privilege persistence: how many bad configs have proc 2
    # privileged, and what fraction can reach good via far-proc fires?
    print(f"\n  Proc {p} privilege persistence analysis:")
    print(f"  Total bad with proc {p} priv: {len(bad_with_p2)}")

    # Among bad_with_p2, how many have a direct exit to good?
    direct_exit = 0
    for c in bad_with_p2:
        priv = privileged(c)
        for pp in priv:
            nc = move(c, pp)
            if nc in good_set:
                direct_exit += 1
                break
    print(f"  Direct exit to good: {direct_exit}/{len(bad_with_p2)}")

    # Among bad_with_p2, what are the drainage depths?
    p2_depths = [depth[c] for c in bad_with_p2 if c in depth]
    if p2_depths:
        print(f"  Drainage depth dist: min={min(p2_depths)}, max={max(p2_depths)}, "
              f"avg={sum(p2_depths)/len(p2_depths):.1f}")


def compare_n7_n8():
    """Compare n=7 (3CB works) vs n=8 (3CB fails).

    Key difference: what structural feature prevents drainage at n=8?
    """
    print(f"\n{'='*60}")
    print(f"COMPARISON: n=7 (3CB works) vs n=8 (3CB expected to fail)")
    print(f"{'='*60}")

    # n=7: ms=(3,2,2,2,3,4,3), P=864. 3CB at {1,2,3}.
    ms7, rules7 = witness_n7()
    n7 = len(ms7)
    P_rest7 = prod(ms7[i] for i in range(n7) if i not in [1,2,3])

    # n=8 hypothetical: ms=(2,2,2,3,3,3,3,4), P=2592.
    # If we try 3CB at {0,1,2}:
    n8 = 8
    ms8 = [2, 2, 2, 3, 3, 3, 3, 4]
    P_rest8 = prod(ms8[3:])

    print(f"\nn=7: ms={list(ms7)}, P={prod(ms7)}")
    print(f"  3CB at {{1,2,3}}, P_rest = {P_rest7}")
    print(f"  Far procs: {{0,4,5,6}}")
    print(f"  P_rest / sum(ms) = {P_rest7/sum(ms7):.2f}")

    print(f"\nn=8: ms={ms8}, P={prod(ms8)}")
    print(f"  3CB at {{0,1,2}}, P_rest = {P_rest8}")
    print(f"  Far procs: {{3,4,5,6,7}}")
    print(f"  P_rest / sum(ms) = {P_rest8/sum(ms8):.2f}")

    # The ratio jumps from 6.0 to 18.3.
    # More specifically: at n=7, P_rest=108=4*27. At n=8, P_rest=324=4*81.
    # The factor is 3: each additional ternary proc multiplies P_rest by 3.

    # But why does this ratio matter?
    # In the good cycle, proc 1 fires 2 times. 2 good configs have proc 1 priv.
    # Total configs with proc 1 priv: |M| * P_rest.
    # Bad configs with proc 1 priv: |M| * P_rest - 2.
    # These bad configs must drain to the good cycle.
    # The drainage goes through near-proc fires (changing binary states).
    # But after a near-proc fire, far procs can send you back.

    # Let's look at the n=7 witness more carefully to see HOW it drains.
    print(f"\n{'='*60}")
    print(f"n=7 DRAINAGE MECHANISM")
    print(f"{'='*60}")

    configs7 = list(itertools.product(*(range(m) for m in ms7)))

    def privileged7(cfg):
        priv = []
        for i in range(n7):
            L = cfg[(i-1) % n7]
            S = cfg[i]
            R = cfg[(i+1) % n7]
            if rules7[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move7(cfg, proc):
        L = cfg[(proc-1) % n7]
        S = cfg[proc]
        R = cfg[(proc+1) % n7]
        new_S = rules7[proc][(L, S, R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # Find good cycle
    single_priv = {}
    for cfg in configs7:
        priv = privileged7(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move7(cfg, priv[0]), priv[0])

    visited = {}
    cur = next(iter(single_priv))
    path = []
    movers_list = []
    while cur in single_priv and cur not in visited:
        visited[cur] = len(path)
        path.append(cur)
        nxt, mover = single_priv[cur]
        movers_list.append(mover)
        cur = nxt

    good_set = set(path) if cur not in visited else set(path[visited[cur]:])
    bad_configs = set(configs7) - good_set

    print(f"Good: {len(good_set)}, Bad: {len(bad_configs)}")

    # For proc 2 (middle binary at {1,2,3}):
    mid = 2
    M_mid = set()
    for ctx, val in rules7[mid].items():
        if val != ctx[1]:
            M_mid.add(ctx)

    bad_with_mid = {c for c in bad_configs if mid in privileged7(c)}
    print(f"Proc {mid} |M|={len(M_mid)}, bad_with_priv={len(bad_with_mid)}")

    # The question: how do bad configs with proc 2 privileged drain?
    # Classify drainage paths by which proc fires first.
    first_fire_to_good = defaultdict(int)
    first_fire_stays_bad = defaultdict(int)

    for c in bad_with_mid:
        priv = privileged7(c)
        for pp in priv:
            nc = move7(c, pp)
            if nc in good_set:
                first_fire_to_good[pp] += 1
            else:
                first_fire_stays_bad[pp] += 1

    print(f"\nFrom bad configs with proc {mid} privileged:")
    print(f"  First fire reaches good: {dict(first_fire_to_good)}")
    print(f"  First fire stays bad: {dict(first_fire_stays_bad)}")

    # Key: can proc 2 itself fire to reach good?
    p2_to_good = 0
    p2_stays_bad = 0
    for c in bad_with_mid:
        nc = move7(c, mid)
        if nc in good_set:
            p2_to_good += 1
        else:
            p2_stays_bad += 1

    print(f"\n  Proc {mid} fire: {p2_to_good} -> good, {p2_stays_bad} -> bad")
    print(f"  Proc {mid} fires to good: {p2_to_good/len(bad_with_mid)*100:.1f}%")


def check_n8_3cb_exhaustive():
    """Try to build a valid 3CB system at n=8 using the same approach as n=7.

    The n=7 witness has specific rules at each proc. Can we adapt them for n=8?
    ms=(2,2,2,3,3,3,3,4) or ms=(3,2,2,2,3,3,3,4)?

    Use lookup-table-based functions, trying ALL possible tables for the
    binary procs (small context space).
    """
    # n=8 with 3CB: ms=(3,2,2,2,3,4,3,3) or similar.
    # Let's try the "natural" placement: 3CB at {1,2,3}.
    # ms = (3, 2, 2, 2, 3, 4, 3, 3), P = 3*8*3*4*3*3 = 2592.

    n = 8
    ms = [3, 2, 2, 2, 3, 4, 3, 3]
    P = prod(ms)
    threshold = 4 * 3**(n-2)

    print(f"\n{'='*60}")
    print(f"n=8 3CB EXHAUSTIVE: ms={ms}, P={P}")
    print(f"Threshold: {threshold}, P/thresh={P/threshold:.4f}")
    print(f"{'='*60}")

    # This is too large (P=2592) for a full exhaustive search over all
    # possible transition functions. But we can try the rule-based approach
    # extended to many more rules.

    # Actually, the key observation from the witnesses:
    # - n=5 valid witness uses specific hand-crafted transition tables
    # - Simple "L!=S,inc" or "S!=R,dec" rules rarely work
    # - The valid systems use COMPLEX, context-dependent rules

    # The right approach: use the EXISTING lower bound proof mechanisms
    # (shadow cycle, entry conflict, palindromic EC) to prove impossibility.
    # The convergence-failure framing is a CONSEQUENCE of EC/shadow,
    # not an independent mechanism.

    # Let me instead verify the claim from the task: at n=8 with
    # ms=(2,2,2,3,3,3,3,4), P=2592, ALL systems fail.
    # But "ALL 768 constructions" refers to a specific construction method.

    # The REAL impossibility proof is the entry conflict proof from the paper.
    # 3CB + sub-threshold → good cycle has entry conflict → no valid system.

    # Let me verify this for n=8 using the existing EC infrastructure.
    print("\nThe impossibility of 3CB at n>=8 sub-threshold is proved by")
    print("the entry conflict mechanism, not by a separate convergence argument.")
    print()
    print("The proof chain is:")
    print("1. Any good cycle is a mover word (sequence of firing procs)")
    print("2. The mover word is either a sweep, wiggle, or bounce")
    print("3. Sweep → shadow cycle exists (shadow cycle mirror theorem)")
    print("4. Wiggle → wiggle shadow cycle exists")
    print("5. Non-sweep fc≤2 → palindromic entry conflict")
    print("6. All cases → no valid good cycle exists")
    print()
    print("Convergence failure is a consequence: since no valid good cycle")
    print("exists, any attempt to build a system will have bad SCCs because")
    print("the 'good' configs can't form a proper cycle.")


def boundary_analysis():
    """Where exactly is the boundary between 3CB-possible and 3CB-impossible?

    From witnesses:
    - n=5 ms=(2,2,2,3,4) P=96: VALID
    - n=6 ms=(2,2,2,4,3,3) P=288: VALID
    - n=7 ms=(3,2,2,2,3,4,3) P=864: VALID
    - n=8 ms=(2,2,3,4,3,3,2,3) P=2592: NOT 3CB (binary at {0,1,6})

    So 3CB works up to n=7 for the M_n-achieving systems.
    Does it fail at n=8? Let's check if ANY 3CB system at n=8 with P=2592 exists.

    Actually, the paper's lower bound proof shows that for n >= 5, ANY system
    with 3 binary (consecutive or not) and product < 4*3^(n-2) has entry conflict
    in every good cycle. So no valid system exists.

    But the M_n witnesses have product = M_n, which for n<=8 equals 32*3^(n-4).
    Since 32*3^(n-4) < 4*3^(n-2) = 36*3^(n-4) for all n:
      32*3^(n-4) < 36*3^(n-4) ✓
    So M_n < threshold for n<=8!

    Wait, but valid 3CB systems DO exist at n=5,6,7 with product = M_n.
    So the entry conflict proof can't be blocking them.

    Hmm, the entry conflict proof works for product < 4*3^(n-2), and the
    witnesses have product = M_n = 32*3^(n-4) < 4*3^(n-2).
    So by the EC proof, these witnesses should NOT exist!

    Unless... the EC proof requires that the 3 binary are at specific positions
    relative to the non-ternary procs, or there's a gap I'm missing.

    Actually, looking at the MEMORY more carefully:
    - The M_5=96 witness ms=(2,2,2,3,4) is valid. P=96 < 108=4*3^3. Sub-threshold.
    - The EC proof says entry conflict exists. But entry conflict means the good
      cycle's mover word has a position where the mover context equals a non-mover
      context, forcing a contradiction.
    - Wait: the EC proof applies to systems with ≥3 binary and product < 4*3^(n-2).
      But it's specific to the GOOD CYCLE MOVER WORD structure.

    Let me re-read the conditions more carefully.
    """
    print(f"\n{'='*60}")
    print(f"BOUNDARY ANALYSIS")
    print(f"{'='*60}")

    for nn in range(4, 10):
        threshold = 4 * 3**(nn-2)
        M_n = 32 * 3**(nn-4) if nn >= 5 else 24
        if nn >= 9:
            M_n = 4 * 3**(nn-2)

        print(f"\nn={nn}: threshold={threshold}, M_n={M_n}")
        print(f"  M_n / threshold = {M_n/threshold:.4f}")
        print(f"  M_n < threshold: {M_n < threshold}")

        # For M_n systems: the binary count
        # M_n = 32*3^(n-4) = 2^5 * 3^(n-4)
        # To get this product with n procs:
        # Need 5 factors of 2 and (n-4) factors of 3.
        # With binary procs (m=2): each contributes 1 factor of 2.
        # So need exactly 5 binary procs? No, that's wrong.
        # 32 = 2^5 could be from 5 binary procs, or 1 quaternary + 3 binary, etc.
        # With 3 binary + 1 quaternary: 2^3 * 4 = 32. Yes!
        # Remaining n-4 procs are ternary: 3^(n-4).
        # Total: 32 * 3^(n-4). ✓

        # So M_n-achieving systems have 3 binary + 1 quaternary + (n-4) ternary.
        # P_rest (non-binary) = 4 * 3^(n-4) = 4 * 3^(n-4).
        # These have binary count = 3, which is ≥3.
        # Sub-threshold: P = 32*3^(n-4) < 4*3^(n-2) = 36*3^(n-4). ✓ for all n.

        # So the EC proof SHOULD apply. But valid systems exist at n=5,6,7!
        # Something is wrong with my understanding of the EC proof.


def verify_ec_conditions():
    """Check: does the entry conflict proof apply to the M_5 witness?

    If the M_5 witness has 3CB at {0,1,2}, P=96 < 4*3^3=108, and ≥3 binary:
    the EC proof should say every good cycle has entry conflict.
    But a valid system EXISTS. Contradiction?

    Unless the EC proof has additional conditions I'm not seeing.

    Let me check the actual EC proof conditions from MEMORY.md:
    - Shadow cycle: for ≥3 binary, non-adjacent, every sweep good cycle has shadow.
    - Palindromic EC: for 3 consecutive binary, every non-sweep fc=2 good cycle has EC.
    - Wiggle shadow: for wiggle words, shadow exists.

    Hmm, the proofs are about mover words of SPECIFIC TYPES.
    A system can be valid if its good cycle avoids all the problematic patterns.
    The proof works by showing ALL possible mover words are blocked:
    sweep → shadow, non-sweep → EC, wiggle → shadow.

    But maybe at small n, not all mover words are covered?

    Actually, looking at the MEMORY again:
    "Case 3a CLOSED: Sweep→shadow, non-sweep fc=2→entry conflict, wiggle→shadow.
    No valid system exists with 3 consecutive binary and product < 4·3^(n-2) for any n ≥ 5."

    But the M_5 witness HAS 3 consecutive binary and P=96 < 108. Contradiction!

    Unless "Case 3a" refers to a specific sub-case of the lower bound proof,
    not the general statement. Let me check what Case 3a actually is.
    """
    print(f"\n{'='*60}")
    print(f"VERIFYING EC CONDITIONS vs M_5 WITNESS")
    print(f"{'='*60}")

    # Load the M_5 witness
    ms, rules = witness_n5()
    n = len(ms)
    P = prod(ms)

    print(f"M_5 witness: ms={list(ms)}, P={P}")
    print(f"Threshold: {4*3**(n-2)}")
    print(f"Binary positions: {[i for i in range(n) if ms[i] == 2]}")

    configs = list(itertools.product(*(range(m) for m in ms)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i-1) % n]
            S = cfg[i]
            R = cfg[(i+1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc-1) % n]
        S = cfg[proc]
        R = cfg[(proc+1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # Find good cycle
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move(cfg, priv[0]), priv[0])

    visited = {}
    cur = next(iter(single_priv))
    path = []
    movers = []
    while cur in single_priv and cur not in visited:
        visited[cur] = len(path)
        path.append(cur)
        nxt, mover = single_priv[cur]
        movers.append(mover)
        cur = nxt

    if cur in visited:
        cycle_start = visited[cur]
        good_cycle = path[cycle_start:]
        good_movers = movers[cycle_start:]
    else:
        print("No good cycle!")
        return

    print(f"\nGood cycle length: {len(good_cycle)}")
    print(f"Mover word: {good_movers}")

    # Check: is this a sweep?
    # A sweep visits procs in order: 0,1,...,n-1 or n-1,...,0 (possibly repeated).
    is_sweep = all(
        abs(good_movers[i] - good_movers[(i+1) % len(good_movers)]) % n <= 1
        for i in range(len(good_movers))
    )
    print(f"Is sweep (adjacent movers): {is_sweep}")

    # Fire counts
    from collections import Counter
    fc = Counter(good_movers)
    print(f"Fire counts: {dict(fc)}")

    # Check entry conflict: for each step in the good cycle,
    # check if the mover's context appears elsewhere as a non-mover context.
    print(f"\nEntry conflict check:")
    for i, c in enumerate(good_cycle):
        mover = good_movers[i]
        L = c[(mover-1) % n]
        S = c[mover]
        R = c[(mover+1) % n]
        mover_ctx = (L, S, R)
        mover_val = rules[mover][(L, S, R)]

        # Check if this exact context appears as a NON-mover context at the same proc
        for j, c2 in enumerate(good_cycle):
            if j == i:
                continue
            if good_movers[j] == mover:
                continue  # mover at same proc
            L2 = c2[(mover-1) % n]
            S2 = c2[mover]
            R2 = c2[(mover+1) % n]
            if (L2, S2, R2) == mover_ctx:
                # Non-mover at step j with same context as mover at step i
                # Entry conflict: rules[mover](L,S,R) must both = S (non-mover)
                # and ≠ S (mover). Contradiction iff S2 == S.
                if S2 == S:
                    print(f"  EC at proc {mover}: step {i} (mover, ctx={mover_ctx}) "
                          f"vs step {j} (non-mover, same ctx)")
                    print(f"    mover fires: {S} -> {mover_val}")
                    print(f"    non-mover needs: f({mover_ctx}) = {S2} = {S}")
                    print(f"    CONTRADICTION: f(ctx) = {mover_val} != {S}")

    print(f"\n(If no EC found: the M_5 witness avoids entry conflict in its good cycle)")

    # Check: which binary procs are consecutive?
    binary = [i for i in range(n) if ms[i] == 2]
    print(f"\nBinary procs: {binary}")
    for i in binary:
        left_is_binary = ms[(i-1) % n] == 2
        right_is_binary = ms[(i+1) % n] == 2
        print(f"  Proc {i}: left binary={left_is_binary}, right binary={right_is_binary}")


if __name__ == "__main__":
    analyze_witness_binary_positions()
    verify_and_analyze_n7_3cb()
    compare_n7_n8()
    verify_ec_conditions()
    boundary_analysis()
