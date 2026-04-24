#!/usr/bin/env python3
"""PA: 3CB Convergence Failure — Part 7.

Carefully classify the M_5 mover word and understand what proof
mechanism should apply to it.

The winding number calculation in Part 6 may be wrong. Let me redo it.
"""

import itertools
from collections import Counter
from math import prod
import sys
sys.path.insert(0, 'gpt/scripts')
from verify_witnesses import witness_n5, witness_n6, witness_n7


def precise_winding_analysis():
    """Precisely compute the winding number and classification of the M_5 mover word."""
    word = [0, 1, 2, 3, 2, 3, 4, 0, 1, 2, 3, 4, 3, 4, 3, 2, 3, 4]
    n = 5
    L = len(word)

    print(f"Mover word: {word}")
    print(f"Length: {L}")
    print(f"Fire counts: {dict(Counter(word))}")

    # Displacement: (word[i+1] - word[i]) mod n, treating as signed
    total_signed = 0
    steps = []
    for i in range(L):
        j = (i + 1) % L
        d = (word[j] - word[i]) % n
        if d > n // 2:
            d -= n  # e.g., 4 -> -1 for n=5
        total_signed += d
        steps.append(d)

    print(f"\nSigned displacements: {steps}")
    print(f"Total signed displacement: {total_signed}")
    print(f"Winding number: {total_signed}/{n} = {total_signed/n}")

    # The winding number should be an integer for a CLOSED walk on the ring.
    # If total_signed / n is not an integer, the walk doesn't close.
    # But the mover word is a good CYCLE, so it returns to the start.

    # Actually, the winding number of a mover word doesn't have to be an integer.
    # The mover word describes WHICH proc fires at each step. The walk on the
    # ring (which proc fires) is a CLOSED walk iff we return to the start proc.
    # But we don't need to return to the start proc -- the cycle is about
    # configurations, not about which proc fires.

    # For a good cycle on n procs: the mover word is a sequence of n-valued
    # labels, not necessarily a walk on a graph. Adjacent movers must be ring-
    # adjacent (since only neighbors' states change).

    # Winding number = total signed displacement / n.
    # If non-integer: the walk is NOT a closed walk on the ring.
    # This is fine for a mover word.

    # But for the shadow cycle proofs, the winding number matters:
    # - winding 2: sweep (Pillar 1)
    # - winding 0: BAF (Pillar 2)
    # - other: ?

    # Let me check: is winding 2 meaningful here?
    print(f"\nNote: total displacement = {total_signed} = {total_signed//n}*{n} + {total_signed%n}")
    print(f"Winding is {'INTEGER' if total_signed % n == 0 else 'NON-INTEGER'}")

    # CW edges (word[i] -> word[i+1] with CW direction):
    cw_count = sum(1 for d in steps if d == 1)
    ccw_count = sum(1 for d in steps if d == -1)
    print(f"\nCW steps: {cw_count}, CCW steps: {ccw_count}")
    print(f"Net: {cw_count - ccw_count}")

    # Edge traversal counts per edge
    edge_cw = Counter()
    edge_ccw = Counter()
    for i in range(L):
        j = (i + 1) % L
        a, b = word[i], word[j]
        if steps[i] == 1:
            edge_cw[(a, (a+1)%n)] += 1
        elif steps[i] == -1:
            edge_ccw[((a-1)%n, a)] += 1

    print(f"\nEdge CW traversals: {dict(edge_cw)}")
    print(f"Edge CCW traversals: {dict(edge_ccw)}")

    # Net edge flow (CW - CCW) for each edge:
    for e in range(n):
        edge = (e, (e+1)%n)
        net = edge_cw.get(edge, 0) - edge_ccw.get(edge, 0)
        print(f"  Edge {edge}: CW={edge_cw.get(edge,0)}, CCW={edge_ccw.get(edge,0)}, net={net}")

    # For a sweep of winding W: each edge is traversed W times net CW.
    # Let's see if the net flow is uniform:
    net_flows = [edge_cw.get((e,(e+1)%n), 0) - edge_ccw.get((e,(e+1)%n), 0) for e in range(n)]
    print(f"\nNet CW flow per edge: {net_flows}")
    print(f"Uniform? {len(set(net_flows)) == 1}")

    if len(set(net_flows)) == 1:
        W = net_flows[0]
        print(f"Winding number W = {W}")
        print(f"This is a {'SWEEP' if abs(W) >= 2 else 'BAF/other'}")
    else:
        print(f"Non-uniform flow: NOT a simple sweep")
        print(f"This is a COMPOUND cycle (mix of sweep and oscillation)")

    # KEY FINDING: the M_5 word has net flow [2, 2, 2, 2, 2].
    # All edges have net CW flow = 2. This IS a sweep of winding 2!
    # Despite having reversals (back-and-forth), the NET flow is uniform.

    # The Shadow Cycle Mirror Theorem (Claim 4.4.1) applies to uniform sweeps.
    # But it's proved for cycles of length EXACTLY 2n (one traverse per direction).
    # The M_5 cycle has length 18, not 2*5=10.

    # Remark 4.4.1a says: "If a sweep has |W| = 2k with k >= 2..."
    # Our sweep has |W| = 2, so k = 1. The remark covers k >= 2.
    # For k = 1: the standard shadow construction applies.

    # But the standard construction produces a shadow of length 2n = 10.
    # The M_5 cycle has length 18 > 10. The shadow construction uses
    # the waterfall form, which assumes the cycle visits each proc
    # exactly twice. But our cycle visits procs 0,1 twice, proc 2 four times,
    # proc 3 six times, proc 4 four times.

    # The waterfall form doesn't apply to cycles longer than 2n!

    # Hmm, but Remark 4.4.1a addresses this: "after every 2n mover steps
    # the same sequence of mover entries recurs." This assumes 2n-periodicity
    # of the mover entries. Let's check if this holds.

    return word, n


def check_waterfall_periodicity():
    """Check if the M_5 cycle has 2n-periodic mover entries (waterfall structure).

    The waterfall form assumes: config g_j has
      g_j[i] = v_i  iff  1 <= ((j - i) mod 2n) <= n
    This requires cycle length = 2n = 10 for n = 5.

    Our cycle has length 18 != 10. So the standard waterfall doesn't apply.

    But maybe we can extract a 2n-periodic "super-cycle" from the actual cycle?
    """
    ms, rules = witness_n5()
    n = len(ms)
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

    cycle_start = visited.get(cur, 0)
    good_cycle = path[cycle_start:]
    good_movers = movers[cycle_start:]
    L = len(good_cycle)

    print(f"\n{'='*60}")
    print(f"WATERFALL PERIODICITY CHECK for M_5")
    print(f"{'='*60}")
    print(f"Cycle length: {L}, 2n = {2*n}")
    print(f"L != 2n: cycle is {L//(2*n)} x 2n + {L%(2*n)} steps long")

    # Check: does the cycle have 2n-periodic mover PATTERNS?
    # I.e., is movers[i] related to movers[i + 2n] for all valid i?
    if L >= 2 * 2 * n:
        print(f"\nPeriodicity check (period 2n={2*n}):")
        for i in range(min(L, 2*n)):
            j = (i + 2*n) % L
            print(f"  Step {i}: mover {good_movers[i]}, Step {j}: mover {good_movers[j]}")

    # Actually, the key issue is: does the Shadow Cycle Mirror Theorem
    # construction work for cycles longer than 2n?

    # Let me check: the theorem constructs shadow configs using a WATERFALL FORM.
    # The waterfall form depends on the cycle length being exactly 2n.
    # If the cycle is longer, the waterfall form doesn't directly apply.

    # HOWEVER: Remark 4.4.1a says "the waterfall profile is still 2n-periodic:
    # after every 2n mover steps the same sequence of mover entries recurs."
    # This is about the ENTRIES used, not the cycle length.

    # For a sweep with winding 2: the mover visits each edge exactly twice net.
    # With non-minimal fire counts (some procs fire more than m_i times),
    # the cycle is longer than 2n, and the waterfall form may not be periodic.

    # Let's check: for each step, compute the mover entry (L, S, R -> new_S).
    # See if these entries repeat every 2n steps.

    print(f"\nMover entries:")
    for i in range(L):
        c = good_cycle[i]
        p = good_movers[i]
        Lv = c[(p-1) % n]
        Sv = c[p]
        Rv = c[(p+1) % n]
        new_S = rules[p][(Lv, Sv, Rv)]
        print(f"  Step {i:2d}: proc {p}, ctx=({Lv},{Sv},{Rv})->{new_S}")

    # The entries are NOT 2n-periodic (L=18 != 2*5=10).
    # So the standard shadow construction doesn't directly apply.

    # But the shadow construction might still work with modifications.
    # Let's try: can we build a shadow cycle from the M_5 good cycle?

    print(f"\n--- Attempting shadow construction ---")
    # Standard shadow: for each proc i, use offset d_i from the good cycle.
    # Shadow config s_k[i] = v_i iff 1 <= ((k + d_i) mod 2n) <= n
    # This only works for 2n-length cycles.

    # For our 18-step cycle: each entry is specific to that step.
    # A shadow would need to use these same entries in a different order.

    # But actually: the shadow construction requires that the good cycle
    # entries DETERMINE the shadow entries. For a longer cycle, there are
    # MORE entries, which give MORE freedom to the transition functions.
    # With more freedom, it's HARDER to force a shadow (fewer constraints).

    # This is the key insight: LONGER CYCLES ARE HARDER TO KILL.
    # The shadow/EC proofs work best for MINIMAL length cycles (2n for sweeps).
    # With super-minimal cycles (length > 2n), the proof may not apply.

    # And the M_5 witness uses a super-minimal cycle (18 > 10).
    # This is how it escapes the shadow construction!

    print(f"\nKEY INSIGHT:")
    print(f"The M_5 good cycle has length {L}, which is {L - 2*n} steps LONGER than")
    print(f"the minimal sweep length 2n={2*n}.")
    print(f"The shadow construction requires minimal-length cycles.")
    print(f"Super-minimal cycles use more entries, giving more freedom to avoid shadows.")
    print(f"The M_5 witness exploits this extra freedom.")


def check_all_witnesses_cycle_length():
    """Check cycle lengths for all witnesses vs 2n minimum."""
    print(f"\n{'='*60}")
    print(f"CYCLE LENGTH vs 2n FOR ALL WITNESSES")
    print(f"{'='*60}")

    witnesses = [
        ("n=5", witness_n5),
        ("n=6", witness_n6),
        ("n=7", witness_n7),
    ]

    for name, wfn in witnesses:
        ms, rules = wfn()
        n = len(ms)
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

        cycle_start = visited.get(cur, 0)
        gc = path[cycle_start:]
        gm = movers[cycle_start:]
        LL = len(gc)

        fc = Counter(gm)
        min_L = sum(ms)

        # Net flow
        net_flows = [0] * n
        for i in range(LL):
            j = (i + 1) % LL
            d = (gm[j] - gm[i]) % n
            if d <= n//2:
                for e in range(min(gm[i], gm[j]), max(gm[i], gm[j])):
                    pass  # This is getting complex
            # Simpler: compute edge counts
        edge_cw = Counter()
        edge_ccw = Counter()
        for i in range(LL):
            j = (i + 1) % LL
            d = (gm[j] - gm[i]) % n
            if d == 1:
                edge_cw[(gm[i], gm[j])] += 1
            elif d == n - 1:
                edge_ccw[(gm[j], gm[i])] += 1

        net = [edge_cw.get((e,(e+1)%n),0) - edge_ccw.get((e,(e+1)%n),0) for e in range(n)]

        binary_pos = [i for i in range(n) if ms[i] == 2]

        print(f"\n{name}: ms={list(ms)}, P={prod(ms)}")
        print(f"  Cycle length: {LL}, min={min_L}, 2n={2*n}")
        print(f"  Fire counts: {dict(sorted(fc.items()))}")
        print(f"  Net edge flow: {net}")
        print(f"  Winding: {net[0] if len(set(net))==1 else 'non-uniform'}")
        print(f"  Binary procs: {binary_pos}")
        print(f"  Excess length: {LL - 2*n}")

        # Check: is the excess at binary or ternary procs?
        excess = {}
        for p in range(n):
            min_fire = ms[p]
            actual = fc[p]
            excess[p] = actual - min_fire
        print(f"  Excess fires per proc: {excess}")


def final_summary():
    """
    SUMMARY OF FINDINGS:

    1. M_5 witness (ms=2,2,2,3,4, P=96) IS a valid 3CB system.
       - Good cycle length 18 (vs minimum 2n=10 for sweeps)
       - Has 6 reversals but winding number 2 (a sweep)
       - NO entry conflict at any proc
       - Avoids shadow construction because cycle is super-minimal

    2. M_6 and M_7 witnesses also have 3CB and are valid.

    3. At n=8, the M_8 witness does NOT have 3CB (binary at {0,1,6}).

    4. The Case 3a proof (Claim 4.4.3 in verification_claims_v2.md) has a gap:
       - It claims all reversals must lie in the ternary arc
       - But reversals at binary procs CAN occur in even numbers
         without violating the even-fire-count constraint
       - The M_5 witness exploits this with 2 binary turnarounds

    5. The Shadow Cycle Mirror Theorem (Claim 4.4.1) only applies to cycles
       of length exactly 2n (uniform sweeps). The M_5 witness avoids this
       by using a longer cycle (18 > 10).

    6. CONCLUSION: The task "prove 3CB forces convergence failure" cannot
       be proved as stated. Valid 3CB systems exist at n=5,6,7.
       The actual theorem (from the paper) is:
       "For n >= 9, M_n = 4*3^(n-2) (not 32*3^(n-4))"
       which means the "3+1+rest" pattern breaks at n=9, NOT because
       3CB fails, but because the PRODUCT needed exceeds the threshold.

    7. At n=8 specifically: the RA data says "ALL 768 constructions" at
       ms=(2,2,2,3,3,3,3,4) fail. This is likely true for THAT specific ms,
       but valid 3CB systems may exist at other ms values with the same product.
       The M_8 witness uses non-consecutive binary, suggesting that at n=8,
       3CB may be genuinely harder but the impossibility is ms-specific.
    """
    print(f"\n{'='*60}")
    print(f"FINAL SUMMARY")
    print(f"{'='*60}")
    print(f"""
FINDING: The task premise "3CB forces convergence failure" is INCORRECT.

EVIDENCE:
- M_5 = 96: ms=(2,2,2,3,4) with 3CB at {{0,1,2}}. Valid system exists.
- M_6 = 288: ms=(2,2,2,4,3,3) with 3CB at {{0,1,2}}. Valid system exists.
- M_7 = 864: ms=(3,2,2,2,3,4,3) with 3CB at {{1,2,3}}. Valid system exists.
- All three are sub-threshold (product < 4*3^(n-2)).

The Case 3a proof (Claim 4.4.3) has a GAP:
- It argues reversals at binary edges force odd fire counts.
- True for 1 reversal, but FALSE for 2+ reversals (even count).
- The M_5 witness has 2 binary turnarounds (even), keeping fire counts even.

The Shadow Cycle Mirror Theorem applies to 2n-length sweep cycles.
The M_5 witness uses an 18-step cycle (vs minimum 10), avoiding the shadow.

For n >= 8 with 3CB: the question remains open.
- M_8 witness uses NON-consecutive binary.
- Whether 3CB at n=8 sub-threshold is impossible requires further investigation.
- The RA data (768 failures at n=8) may be correct but doesn't constitute a proof.
""")


if __name__ == "__main__":
    precise_winding_analysis()
    check_waterfall_periodicity()
    check_all_witnesses_cycle_length()
    final_summary()
