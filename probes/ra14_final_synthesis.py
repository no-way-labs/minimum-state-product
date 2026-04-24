#!/usr/bin/env python3
"""
RA14 FINAL SYNTHESIS: What the Lean existential needs

Key findings from RA14a-c:

1. SORRY 1 (CL = 2n): The Lean code uses this INSIDE allFireCount_eq_2_of_zeroWinding,
   before fc=2 is established. The argument is circular as written.
   CORRECT PROOF: fc >= 2 for all (from fireCount_ne_one) → CL = sum fc >= 2n.
   Then CL <= 2n from: zero winding → #CW = #CCW; each proc fires 1 CW + 1 CCW
   step minimum = n CW + n CCW; but if CL > 2n, some proc fires >= 3 times;
   with fc >= 2 and binary procs having even fc, the next step for binary is fc >= 4,
   forcing CL >= 2n+2; config distinctness + binary state space then gives
   contradiction for sub-threshold product. [Sketch needs tightening.]

2. SORRYS 4a-c: The Lean pair (cwSteps[right(b)], ccwSteps[b]) DOES give context
   match, but NOT because of zero fires between the steps. The match comes from:
   - right(b) fires EXACTLY 2 times in [k2, k1) (CW at k2, CCW between)
     → for fc=2, this is the FULL fire cycle → returns to original value
   - left(b) fires 0 times in [k2, k1) when b is INTERIOR
   - b fires 0 times in [k2, k1)

3. CRITICAL ISSUE: "Interior" means b is at CW-distance >= 2 from BOTH turnaround
   points of the BAF walk. With 3 consecutive binary at {0,1,2} and turnaround
   at position 1, ALL three binary are within distance 1 → NO interior binary exists.
   This happens for ANY n, not just small n.

4. RESOLUTION: For n >= 9 with 3 binary, NOT all turnaround positions are bad.
   The turnaround position is determined by the good cycle structure. We need to
   prove that the turnaround can't land on all 3 binary procs simultaneously
   when they're consecutive.

   Actually: the turnaround CAN land there. But when it does, the entry conflict
   comes from a DIFFERENT mechanism (the CIC Expl 14 approach checks ALL procs,
   not just binary ones). The computational verification shows 100% EC rate
   at ALL non-sweep fc=2 words for ALL state-sequence combos.

Let me check: does the EXISTING palindromic EC approach from CIC Expl 14
(which checks entry conflicts at ALL procs, not just binary) handle the
turnaround-on-binary case?
"""

from itertools import product as iproduct
from collections import defaultdict


def enumerate_fc2_walks(n):
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == 2 * n:
            nxt = path[0]
            if abs(pos - nxt) == 1 or abs(pos - nxt) == n - 1:
                if all(f == 2 for f in fc):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < 2:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    unique = set()
    result = []
    for w in walks:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def step_dir(word, t, n):
    L = len(word)
    curr = word[t]
    nxt = word[(t + 1) % L]
    d = (nxt - curr) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0


def winding_number(word, n):
    return sum(step_dir(word, t, n) for t in range(len(word)))


def is_sweep(word, n):
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    return all(d == 1 for d in dirs) or all(d == n - 1 for d in dirs)


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def build_configs(word, n, ms, combo):
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    return configs


def check_all_ec(word, n, ms):
    """Check entry conflict at ALL procs for ALL combos.
    Returns (total_valid, total_with_ec, per_proc_ec_count)."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
    sl = [proc_seqs[p] for p in range(n)]

    total_valid = 0
    total_with_ec = 0
    per_proc_ec = [0] * n  # how many combos have EC at proc j

    for combo in iproduct(*sl):
        configs = build_configs(word, n, ms, combo)
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue
        total_valid += 1
        good = configs[:L]

        mover_e = {}
        nonmover_e = {}
        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            mover = word[t]
            for j in range(n):
                key = (j, c[(j-1) % n], c[j], c[(j+1) % n])
                if j == mover:
                    mover_e[key] = cn[j]
                else:
                    if key not in nonmover_e:
                        nonmover_e[key] = set()
                    nonmover_e[key].add(c[j])

        found_ec_at = set()
        for key in mover_e:
            if key in nonmover_e:
                _, _, s, _ = key
                if mover_e[key] != s:
                    found_ec_at.add(key[0])

        if found_ec_at:
            total_with_ec += 1
        for j in found_ec_at:
            per_proc_ec[j] += 1

    return total_valid, total_with_ec, per_proc_ec


def main():
    print("=" * 72)
    print("RA14 FINAL SYNTHESIS")
    print("=" * 72)

    # =====================================================================
    # Q1: For the bad walk (turnaround on binary), does EC still hold?
    # =====================================================================
    print("\nQ1: Does EC hold for ALL walks, including turnaround-on-binary?")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)

        for w in nonsweep_zw:
            tv, tc, pec = check_all_ec(w, n, ms)
            status = "ALL EC" if tc == tv else f"MISSING {tv-tc}/{tv}"
            ec_procs = [j for j in range(n) if pec[j] == tv]
            print(f"  Walk {w}: {status}; universal EC at procs {ec_procs}")

    # =====================================================================
    # Q2: For the bad walk, WHICH proc has the EC?
    # =====================================================================
    print("\n" + "=" * 72)
    print("Q2: For turnaround-on-binary walks, where is the EC?")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)

        # The "bad" walk: turnaround at position 1 (center of binary cluster)
        # For n=5: [0, 1, 0, 4, 3, 2, 1, 2, 3, 4]
        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            # Check if turnaround is within binary cluster
            transitions = []
            for t in range(L):
                if dirs[t] != dirs[(t+1) % L]:
                    transitions.append(t)

            if len(transitions) != 2:
                continue

            # CW→CCW turnaround proc
            cw_to_ccw = transitions[0]
            # The turnaround proc is the one at the CW→CCW boundary
            turn_proc = w[(cw_to_ccw + 1) % L]

            # Check if turnaround is binary
            if ms[turn_proc] != 2:
                continue

            tv, tc, pec = check_all_ec(w, n, ms)
            ec_procs = [j for j in range(n) if pec[j] == tv]
            non_binary_ec = [j for j in ec_procs if ms[j] != 2]

            print(f"\n  Walk {w} (turnaround at binary proc {turn_proc})")
            print(f"  Valid combos: {tv}, all have EC: {tc == tv}")
            print(f"  EC procs (universal): {ec_procs}")
            print(f"  Non-binary EC procs: {non_binary_ec}")
            print(f"  Per-proc EC counts: {[(j, pec[j]) for j in range(n) if pec[j] > 0]}")

            # Check: is the EC at a TERNARY proc near the turnaround?
            for j in ec_procs:
                jl = (j-1) % n
                jr = (j+1) % n
                cw_fire = {}
                ccw_fire = {}
                for t in range(L):
                    p = w[t]
                    if dirs[t] == 1:
                        cw_fire[p] = t
                    elif dirs[t] == -1:
                        ccw_fire[p] = t

                if j in ccw_fire and jr in cw_fire:
                    k2 = cw_fire[jr]
                    k1 = ccw_fire[j]

                    if k2 < k1:
                        firing_steps = list(range(k2, k1))
                    else:
                        firing_steps = list(range(k2, L)) + list(range(0, k1))

                    firing_movers = [w[t] for t in firing_steps]
                    jl_t = firing_movers.count(jl)
                    j_t = firing_movers.count(j)
                    jr_t = firing_movers.count(jr)

                    condition = "OK" if (jl_t == 0 or jl_t == 2) and j_t == 0 and (jr_t == 0 or jr_t == 2) else "FAIL"
                    print(f"    EC proc {j} (m={ms[j]}): pair (cwSteps[{jr}]={k2}, ccwSteps[{j}]={k1})")
                    print(f"      fires between: left({jl})={jl_t}, self={j_t}, right({jr})={jr_t} [{condition}]")

    # =====================================================================
    # Q3: The correct Lean approach — what data does the existential carry?
    # =====================================================================
    print("\n" + "=" * 72)
    print("Q3: CORRECT LEAN APPROACH")
    print("=" * 72)

    print("""
    FINDING: The Lean pair (cwSteps[right(b)], ccwSteps[b]) works for ANY
    proc b (binary or not) that satisfies:
      (1) left(b) fires 0 or 2 times in [k2, k1)
      (2) b fires 0 times in [k2, k1)
      (3) right(b) fires 0 or 2 times in [k2, k1)

    For fc=2, "fires 2 times" = full cycle back to original value.
    For fc=2, "fires 0 times" = unchanged.

    The "full cycle" argument: any proc with fc=2 has state sequence
    [s0, s1, s0] (start at s0, change to s1, change back to s0).
    If both firings occur between k2 and k1, the value at k2 equals
    the value at k1.

    THEOREM (for Lean): Given a palindromic BAF walk with turnaround at
    CW-distance d from the starting position (0 < d < n), there exists
    a proc b at CW-distance j from start, where 2 <= j <= d-2 (or from
    the other side), such that:
      - left(b) fires 0 times between cwSteps[right(b)] and ccwSteps[b]
      - b fires 0 times between these steps
      - right(b) fires exactly 2 times between these steps

    This requires d >= 4 (so j can be 2..d-2, giving at least 1 proc).
    Since the BAF arc covers the full ring (d + (n-d) = n), and n >= 9,
    at least one of the two arcs has length >= 5 (since 5 + 4 = 9).
    The arc of length >= 5 has interior of size >= 3.
    With 3 binary procs among n >= 9 positions, and the interior having
    >= 3 positions... hmm, we can't guarantee a binary proc in the interior.

    WAIT — the entry conflict works for ANY proc, not just binary!
    The Lean code currently requires b to be binary (isBinary sys.rs b),
    but the context match argument works for ALL procs with fc=2.

    For fc=2: the state sequence is [0, v, 0] (starts and ends at 0).
    If the proc fires 2 times between the key steps, value returns to 0.
    If the proc fires 0 times, value is unchanged.
    This is state-count independent! Works for binary, ternary, any modulus.

    THE FIX: Remove the binary requirement from the Lean proof.
    Instead of "exists interior BINARY b", use "exists interior b" (any proc).
    The interior has size >= d - 3 >= (n/2) - 3 >= (9/2) - 3 > 0 for n >= 9.
    Actually min arc length = ceil(n/2) when d = n/2. For n=9: min arc = 5,
    interior = 5 - 3 = 2. For n=9: interior of the larger arc is >= 2 procs.
    With n >= 9, one arc has d >= 5, interior >= 2. Done.
    """)

    # Verify: for the BAD walk, is there a non-binary interior proc that works?
    print("\nVerification: non-binary interior proc for the bad walk")
    for n in [5, 7, 9]:
        if n <= 7:
            walks = enumerate_fc2_walks(n)
            nonsweep_zw = [w for w in walks
                           if winding_number(w, n) == 0 and not is_sweep(w, n)]
        else:
            # Construct the "bad" walk: turnaround at d=1
            # Walk: [0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1]
            phase1 = [0, 1]  # CW
            phase2 = list(range(0, -1, -1)) + list(range(n-1, 1, -1))  # CCW: 0, n-1, ..., 2
            phase3 = list(range(2, n))  # CW: 2, 3, ..., n-1
            w = phase1 + phase2 + phase3
            # Hmm let me construct from the n=5 pattern:
            # n=5: [0, 1, 0, 4, 3, 2, 1, 2, 3, 4]
            # n=7: [0, 1, 0, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6]
            # n=9: [0, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8]
            w = [0, 1] + [0] + list(range(n-1, 1, -1)) + list(range(1, n))
            # Check: length = 2 + 1 + (n-2) + (n-1) = 2n ✓
            nonsweep_zw = [w]

        ms = [2, 2, 2] + [3] * (n - 3)

        for w in nonsweep_zw:
            L = len(w)
            if L != 2 * n:
                continue

            dirs = [step_dir(w, t, n) for t in range(L)]
            if winding_number(w, n) != 0:
                continue

            # Find turnaround
            transitions = []
            for t in range(L):
                if dirs[t] != dirs[(t+1) % L]:
                    transitions.append(t)
            if len(transitions) != 2:
                continue

            turn_proc = w[(transitions[0] + 1) % L]
            if ms[turn_proc] != 2:
                continue

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            print(f"\n  n={n}, walk {w[:8]}..., turnaround at binary proc {turn_proc}")

            for b in range(n):
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                if k2 < k1:
                    firing_steps = list(range(k2, k1))
                else:
                    firing_steps = list(range(k2, L)) + list(range(0, k1))

                firing_movers = [w[t] for t in firing_steps]
                lb_t = firing_movers.count(lb)
                b_t = firing_movers.count(b)
                rb_t = firing_movers.count(rb)

                ok = (lb_t == 0 or lb_t == 2) and b_t == 0 and (rb_t == 0 or rb_t == 2)
                if ok:
                    print(f"    b={b} (m={ms[b]}): lb={lb_t}, self={b_t}, rb={rb_t} — GOOD")

    # =====================================================================
    # Q4: Sorry 1 — is CL = 2n provable without fc=2?
    # =====================================================================
    print("\n" + "=" * 72)
    print("Q4: Sorry 1 — CL = 2n argument")
    print("=" * 72)

    print("""
    The Lean code has a CIRCULAR DEPENDENCY:
      allFireCount_eq_2_of_zeroWinding needs hlen (CL = 2n)
      But CL = sum fc = 2n requires fc = 2 for all.

    CORRECT APPROACH: Restructure as:
    (A) fc >= 2 for all procs (from fireCount_ne_one + fairness)
    (B) CL = sum fc >= 2n
    (C) Zero winding → #CW = #CCW. Each proc fires once CW and once CCW minimum.
        #CW >= n, #CCW >= n. CL = #CW + #CCW >= 2n.
    (D) If CL > 2n, then some proc has fc >= 3. But fc is even for binary procs
        (fireCount_ne_one shows fc != 1; binary state sequence forces even fc
        because the state must return to 0 through states {0,1}, requiring
        an even number of transitions). So fc >= 4 for that binary proc.
    (E) The state sequence of a binary proc with fc=4 is [0,1,0,1,0].
        This means the proc visits the same state 3 times. Combined with
        the neighbor states, this forces a config repetition (needs a local
        lemma about binary proc state revisits → config collision).
    (F) Config collision contradicts gc.configs_distinct.

    Actually, a simpler argument:
    (A) fc >= 2 for all, CL >= 2n.
    (B) Suppose CL = 2n + k for k > 0.
    (C) Then sum fc = 2n + k, with each fc >= 2. So exactly k procs have fc >= 3.
    (D) For binary procs: fc must be even (0→1→0→... requires even steps to return
        to 0). So binary fc >= 4 if fc > 2, contributing fc - 2 >= 2 extra.
    (E) For ternary procs: fc can be odd. fc = 3 means [0,v1,v2,0] with
        3 state changes among {0,1,2}.
    (F) Sub-threshold product: CL <= product = prod(m_i) < 4·3^(n-2).
        With n >= 9: 2n + k < 4·3^(n-2), so k < 4·3^(n-2) - 2n.
        This gives no useful upper bound on k from sub-threshold alone.

    BETTER: For zero-winding, the walk is a closed path on Z_n with winding 0.
    The walk visits 2n edges (n CW, n CCW). Each edge is visited at most
    a bounded number of times. A proc at position p fires once per CW-crossing
    and once per CCW-crossing of the edge (p, p+1). With winding 0, each
    edge is crossed the same number of times in each direction. The minimum
    is 1 crossing per direction per edge = n CW + n CCW = 2n steps.
    Extra steps come from edges crossed > 1 time, but with fc = 2 for all,
    each proc fires exactly twice.

    SIMPLEST: If fc >= 2 for all and CL = sum fc, and CL = 2n, then fc = 2 for all
    (since all >= 2 and sum = 2n, each must be exactly 2). So the sorry reduces to:
    PROVE CL = 2n for zero-winding fair distinct good cycles under sub-threshold.

    The CL = 2n fact follows from: zero winding means the walk on Z_n has no net
    rotation. With fc >= 2 (each proc fires >= 2 times) and distinctness of configs,
    CL >= 2n. The upper bound CL <= 2n comes from: with zero winding, each edge
    is crossed equally in both directions; each proc fires the same number of CW
    and CCW times; for binary procs, CW firings = CCW firings = fc/2; since the
    walk has zero winding, it's a TREE-like walk (BAF), which for fc=2 exactly
    covers each proc once CW and once CCW. Extra crossings would force fc > 2
    at some proc, but then config distinctness on a sub-threshold product ring
    forces a collision.

    This is the REAL sorry. It needs a careful proof but is not deep.
    """)

    # =====================================================================
    # FINAL SUMMARY
    # =====================================================================
    print("\n" + "=" * 72)
    print("FINAL SUMMARY: What to fix in the Lean code")
    print("=" * 72)

    print("""
    === Sorry 1 (CL = 2n) ===
    Status: Needs restructuring. The current proof has a circular dependency.
    Fix: Prove CL = 2n directly from zero winding + fairness + distinct + sub-threshold.
    Argument sketch: fc >= 2 for all → CL >= 2n. Zero winding + BAF structure +
    config distinctness + sub-threshold → CL <= 2n (extra crossings force config collisions).

    === Sorrys 4a-c (config equalities) ===
    Status: The approach works but needs TWO fixes.

    FIX 1: Remove the binary requirement from exists_interior_binary.
    The interior proc need NOT be binary. Any proc with fc=2 has the same
    "full cycle" property: if it fires 0 or 2 times between the key steps,
    its value is preserved. The palindromic_ec_of_interior_binary should
    become palindromic_ec_of_interior_proc.

    FIX 2: Replace the True placeholders with real interior conditions.
    The existential hpalindromic should carry:
      - Step ordering: cwSteps, ccwSteps with the palindromic order
      - Interior condition: b is at CW-distance >= 2 from both turnarounds
        (the walk endpoints in the BAF structure)

    The 3 sorrys then become:
      sorry 4a (left(b)):  config_val_eq_of_no_move_between
                           (left(b) fires 0 times between k2 and k1
                            because lb CW is before k2, lb CCW is after k1)
      sorry 4b (b):        config_val_eq_of_no_move_between
                           (b fires 0 times between k2 and k1
                            because b CW is before k2, b fires at k1 exactly)
      sorry 4c (right(b)): NEW LEMMA: config_val_eq_of_full_cycle_between
                           (right(b) fires exactly 2 times between k2 and k1:
                            once at k2 (CW) and once in the CCW phase.
                            For fc=2, 2 firings = full cycle = return to original.)

    The new lemma config_val_eq_of_full_cycle_between says:
      If proc p has fireCount p = 2, and BOTH firing steps are in [a, b),
      then config[a](p) = config[b](p).
    Proof: p fires 2 times, state goes s0 → s1 → s0. Back to start.

    FIX 3 (alternative, simpler): Instead of the complex interior argument,
    prove the three equalities via:
      For any proc p with fc=2: let t1, t2 be its two firing steps.
      config[t1](p) = config[t2](p) = initial value of p.
      So config[k](p) depends ONLY on whether k is between t1 and t2
      or not. If both k2 and k1 are on the SAME SIDE of p's firing steps,
      config[k2](p) = config[k1](p).

    === Proposed Lean existential type ===

    structure PalindromicInterior (gc : GoodCycle sys) where
      proc : Fin sys.rs.n
      cwStep : Fin gc.configs.length    -- cwSteps[right(proc)]
      ccwStep : Fin gc.configs.length   -- ccwSteps[proc]
      cw_not_mover : gc.moverAt cwStep ≠ proc
      ccw_is_mover : gc.moverAt ccwStep = proc
      -- Interior condition: no neighborhood fires between cwStep and ccwStep
      -- EXCEPT right(proc) which fires exactly 2 times (full cycle)
      left_no_fire : ∀ k, cwStep.val < k.val → k.val < ccwStep.val →
                     gc.moverAt k ≠ left proc
      self_no_fire : ∀ k, cwStep.val < k.val → k.val < ccwStep.val →
                     gc.moverAt k ≠ proc
      right_full_cycle : -- right(proc) fires exactly once between cwStep and ccwStep
                         -- (plus the fire AT cwStep = total 2 fires = full cycle)
                         ∃ k, cwStep.val < k.val ∧ k.val < ccwStep.val ∧
                           gc.moverAt k = right proc ∧
                           ∀ k', cwStep.val < k'.val → k'.val < ccwStep.val →
                             gc.moverAt k' = right proc → k' = k

    The three config equalities then follow from:
    4a: config_val_eq_of_no_move_between using left_no_fire
    4b: config_val_eq_of_no_move_between using self_no_fire
    4c: config_val_eq_of_full_cycle_between using right_full_cycle + hfc2(right proc)
    """)


if __name__ == "__main__":
    main()
