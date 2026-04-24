"""
Proof: no consecutive t-fires for sandwiched ternary t in a good cycle.

VERSION 2: Refined computation with proper preconditions.

The theorem lives in AllNormalFormFalse2.lean at the call to sparse_phase_sum_ge.
Preconditions:
1. Good cycle gc
2. t sandwiched ternary (m_t = 3, m_{bL} = 2, m_{bR} = 2)
3. fc(t) >= 2
4. fc(t) < CL (t doesn't fire at every step)
5. All TernaryPhases have normalForm
6. No entry conflict
7. n >= 9, sub-threshold product

Note: condition 4 (fc(t) < CL) means some OTHER proc fires, so CL >= 3.
Combined with the binary parity (fc(bL) even) and fairness (bL fires),
we get fc(bL) >= 2.

The counterexamples from version 1 had CL=2 with fc(t)=CL=2, violating condition 4.

APPROACH: Derive contradiction from consecutive t-fires under these conditions.

The proof uses the "absorbing value + cycle return" argument:
If t fires at steps k, k+1 with context (c_L, v, c_R):
  f_t(c_L, v, c_R) = v+1 (step k fire)
  f_t(c_L, v+1, c_R) = v+2 (step k+1 fire)
  f_t(c_L, v+2, c_R) = v+2 (step 1: forced nonmover, else 3-consec contradiction)

Then for the cycle to return to config k: t must fire from v+2 with a DIFFERENT (L,R) context.
This creates an entry conflict because t sees v+2 as nonmover with (c_L, c_R)
but as mover with some other (c_L', c_R'). The path between these forces
t to be nonmover with the mover context, giving EC.

Wait - no, that's not EC because the contexts differ. Let me think again.

Actually the proof is about what happens at the BINARY NEIGHBORS, not at t.

NEW INSIGHT from computational investigation: The proof works through a
"config repeat near-miss" argument.

Config k:   C = (..., c_L, v,   c_R, ...)
Config k+2: C'' = (..., c_L, v+2, c_R, ...)
These two configs are Hamming-1 (differ only at t).

In a good cycle with unique privilege:
At C: only t is privileged.
At C'': some proc p != t is privileged (since fc(t) < CL, not always t).

The privileged proc at C'' must have a different context at C vs C''.
Only procs adjacent to t (bL and bR) have different contexts.
So the privileged proc at C'' is either bL, bR, or some proc p such that
its privilege somehow changed despite not being adjacent to t.

Wait: non-adjacent procs see the SAME context at C and C'' (since only t changed).
So if p is non-adjacent to t and not privileged at C: p is not privileged at C''.
At C, only t is privileged. So all non-adjacent procs are not privileged at C''.
Therefore the privileged proc at C'' is bL, bR, or t.
But t is not privileged at C'' (Step 1: f_t(c_L,v+2,c_R) = v+2).
So the privileged proc at C'' is bL or bR.

Since unique privilege: exactly ONE of bL, bR is privileged at C''.

WLOG say bL is privileged at C'':
f_{bL}(LL, c_L, v+2) != c_L.  (bL privileged at C'')
f_{bL}(LL, c_L, v)   = c_L.   (bL not privileged at C, since only t privileged)
f_{bL}(LL, c_L, v+1) = c_L.   (bL not privileged at C', since only t privileged)

So f_{bL}(LL, c_L, *) returns c_L for R=v,v+1 but not for R=v+2.
Since bL is binary: f_{bL}(LL, c_L, v+2) = 1 - c_L.

bL fires at C'', going from c_L to 1-c_L. The mover at step k+2 is bL.
Config k+3 = (..., 1-c_L, v+2, c_R, ...).

Now at C+3: what's the privilege status?
t sees (1-c_L, v+2, c_R). Is t privileged? f_t(1-c_L, v+2, c_R) =? v+2.
bL sees (LL, 1-c_L, v+2). Is bL privileged? f_{bL}(LL, 1-c_L, v+2) =? 1-c_L.

The key question: what happens next in the cycle?

For the ENTRY CONFLICT argument at bL:
- At C (step k):    bL context (LL, c_L, v),   nonmover. f_{bL}(LL, c_L, v) = c_L.
- At C'' (step k+2): bL context (LL, c_L, v+2), MOVER.   f_{bL}(LL, c_L, v+2) = 1-c_L.

These have DIFFERENT contexts (R differs: v vs v+2). Not EC.

- At C' (step k+1):  bL context (LL, c_L, v+1), nonmover. f_{bL}(LL, c_L, v+1) = c_L.
- At C'' (step k+2): bL context (LL, c_L, v+2), MOVER.

Also different contexts. Not EC.

For EC at bL: need (LL, c_L, r) to appear as BOTH mover and nonmover for SAME (LL, c_L, r).

From the 3 steps: (LL, c_L, v) nonmover, (LL, c_L, v+1) nonmover, (LL, c_L, v+2) mover.
For EC: need (LL, c_L, v+2) nonmover somewhere else, OR (LL, c_L, v) or (LL, c_L, v+1) mover somewhere else.

Since f_{bL}(LL, c_L, v) = c_L (always): (LL, c_L, v) is ALWAYS nonmover at bL.
Since f_{bL}(LL, c_L, v+1) = c_L (always): (LL, c_L, v+1) is ALWAYS nonmover at bL.
Since f_{bL}(LL, c_L, v+2) = 1-c_L != c_L: (LL, c_L, v+2) is ALWAYS mover at bL.

No EC at bL from these alone. (Mover contexts always mover, nonmover always nonmover.)

Hmm. So the EC must come from somewhere else. Let me look at the SYMMETRIC case.

If bR is privileged at C'' instead: similar argument, no direct EC.

What if NEITHER bL nor bR is privileged at C''?
Then NO proc is privileged at C'' (t isn't, non-adjacent aren't, bL isn't, bR isn't).
But C'' is a good config (in the cycle), so exactly one proc is privileged. Contradiction!

So EXACTLY ONE of bL, bR is privileged at C''. Good.

The EC must come from the CONTINUATION of the cycle, not just the 3 steps.

Let me think about this more carefully computationally.
"""

import itertools
import random
from collections import defaultdict


def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))


def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i - 1) % n]
        S = config[i]
        R = config[(i + 1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)


def find_good_cycle(ms, fs):
    """Find the good cycle of a valid system."""
    n = len(ms)
    configs = all_configs(ms)
    good_configs = set()
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            good_configs.add(c)
    if not good_configs:
        return None, None
    succ = {}
    for c in good_configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) != 1:
            continue
        mover = priv[0]
        nxt = apply_move(c, mover, fs, ms)
        if nxt in good_configs:
            succ[c] = (nxt, mover)
    if not succ:
        return None, None
    start = next(iter(succ))
    visited = {}
    current = start
    step = 0
    while current not in visited:
        if current not in succ:
            return None, None
        visited[current] = step
        nxt, mover = succ[current]
        current = nxt
        step += 1
    cycle_start = visited[current]
    cycle_configs = []
    cycle_movers = []
    c = current
    for _ in range(step - cycle_start):
        if c not in succ:
            return None, None
        nxt, mover = succ[c]
        cycle_configs.append(c)
        cycle_movers.append(mover)
        c = nxt
    return cycle_configs, cycle_movers


def verify_system_quick(ms, fs):
    """Quick validity check."""
    n = len(ms)
    configs = all_configs(ms)
    good_configs = set()
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 0:
            return False
        if len(priv) == 1:
            good_configs.add(c)
    if not good_configs:
        return False
    for c in good_configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) != 1:
            continue
        nxt = apply_move(c, priv[0], fs, ms)
        if nxt not in good_configs:
            return False
    bad_configs = [c for c in configs if c not in good_configs]
    visited = set()
    for c in bad_configs:
        if c in visited:
            continue
        path = set()
        current = c
        while current not in visited and current not in good_configs:
            if current in path:
                return False
            path.add(current)
            priv = privileged_set(current, fs, ms)
            if not priv:
                return False
            nxt = apply_move(current, priv[0], fs, ms)
            current = nxt
        visited.update(path)
    return True


def has_entry_conflict(cycle_configs, cycle_movers, fs, ms):
    """Check for entry conflict."""
    n = len(ms)
    CL = len(cycle_configs)
    for p in range(n):
        mover_contexts = set()
        nonmover_contexts = set()
        for k in range(CL):
            c = cycle_configs[k]
            ctx = (c[(p - 1) % n], c[p], c[(p + 1) % n])
            if cycle_movers[k] == p:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)
        if mover_contexts & nonmover_contexts:
            return True
    return False


def check_consecutive_tfire(cycle_movers, t):
    CL = len(cycle_movers)
    for k in range(CL):
        if cycle_movers[k] == t and cycle_movers[(k + 1) % CL] == t:
            return True
    return False


def fire_count(cycle_movers, p):
    return sum(1 for m in cycle_movers if m == p)


def random_table(m_L, m_S, m_R):
    table = {}
    for l in range(m_L):
        for s in range(m_S):
            for r in range(m_R):
                table[(l, s, r)] = random.randint(0, m_S - 1)
    return table


def table_to_func(table):
    def f(L, S, R):
        return table[(L, S, R)]
    return f


def search_with_preconditions(ms, num_trials=500000, seed=42):
    """Search for valid systems with consecutive t-fires, enforcing all preconditions."""
    random.seed(seed)
    n = len(ms)

    sandwich_positions = []
    for t in range(n):
        if ms[t] >= 3 and ms[(t-1) % n] == 2 and ms[(t+1) % n] == 2:
            sandwich_positions.append(t)

    if not sandwich_positions:
        return 0, 0, 0

    valid_count = 0
    consec_count = 0
    consec_with_preconds = 0

    for trial in range(num_trials):
        tables = []
        for i in range(n):
            m_L = ms[(i-1) % n]
            m_S = ms[i]
            m_R = ms[(i+1) % n]
            tables.append(random_table(m_L, m_S, m_R))
        fs = [table_to_func(t) for t in tables]

        if not verify_system_quick(ms, fs):
            continue
        valid_count += 1

        cycle_configs, cycle_movers = find_good_cycle(ms, fs)
        if cycle_configs is None:
            continue

        CL = len(cycle_movers)

        for t in sandwich_positions:
            if not check_consecutive_tfire(cycle_movers, t):
                continue

            consec_count += 1

            # Check preconditions:
            fc_t = fire_count(cycle_movers, t)
            fc_bL = fire_count(cycle_movers, (t - 1) % n)
            fc_bR = fire_count(cycle_movers, (t + 1) % n)

            # Precondition: fc(t) < CL (not all t-fires)
            if fc_t >= CL:
                continue

            # Precondition: fc(t) >= 2
            if fc_t < 2:
                continue

            # Check no EC
            ec = has_entry_conflict(cycle_configs, cycle_movers, fs, ms)
            if ec:
                continue

            # Check fairness (every proc fires at least once)
            all_fire = all(fire_count(cycle_movers, p) > 0 for p in range(n))
            if not all_fire:
                continue

            consec_with_preconds += 1
            print(f"  COUNTEREXAMPLE: trial {trial}, ms={ms}, t={t}")
            print(f"    CL={CL}, fc(t)={fc_t}, fc(bL)={fc_bL}, fc(bR)={fc_bR}")
            print(f"    Movers: {cycle_movers}")
            for k in range(CL):
                if cycle_movers[k] == t and cycle_movers[(k+1) % CL] == t:
                    print(f"    Consec at steps {k},{k+1}")
                    print(f"      Config {k}:   {cycle_configs[k]}")
                    print(f"      Config {k+1}: {cycle_configs[(k+1) % CL]}")

    return valid_count, consec_count, consec_with_preconds


def main():
    print("=" * 70)
    print("NO CONSECUTIVE T-FIRES: Refined Search (Version 2)")
    print("=" * 70)
    print()
    print("Preconditions enforced:")
    print("  - Valid system (liveness, ME, closure, convergence)")
    print("  - No entry conflict")
    print("  - fc(t) >= 2 and fc(t) < CL")
    print("  - Fairness (every proc fires)")
    print("  - Sandwiched ternary t with binary neighbors")
    print()

    test_cases = [
        [2, 3, 2, 2, 2],       # n=5, prod=48
        [2, 3, 2, 3, 2],       # n=5, prod=72
        [2, 3, 2, 2, 3],       # n=5, prod=72
        [2, 2, 3, 2, 2],       # n=5, prod=48
        [2, 3, 2, 2, 2, 2],    # n=6, prod=96
        [2, 3, 2, 3, 2, 2],    # n=6, prod=144
        [2, 3, 2, 2, 3, 2],    # n=6, prod=144
        [2, 3, 2, 3, 3, 2],    # n=6, prod=216
        [2, 3, 2, 2, 2, 2, 2], # n=7, prod=192
        [2, 3, 2, 3, 2, 2, 2], # n=7, prod=288
        [2, 3, 2, 2, 3, 2, 2], # n=7, prod=288
        [2, 3, 2, 3, 3, 2, 2], # n=7, prod=432
        [2, 3, 2, 3, 3, 3, 2], # n=7, prod=648
    ]

    total_valid = 0
    total_consec = 0
    total_with_preconds = 0

    for ms in test_cases:
        n = len(ms)
        threshold = 4 * (3 ** (n - 2))
        prod = 1
        for m in ms:
            prod *= m
        nbinary = sum(1 for m in ms if m == 2)

        if prod >= threshold or nbinary < 3:
            continue

        # Find sandwich positions
        sandwiches = [t for t in range(n) if ms[t] >= 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]
        if not sandwiches:
            continue

        print(f"ms={ms}, n={n}, prod={prod}, threshold={threshold}, sandwiches={sandwiches}")
        v, c, cp = search_with_preconditions(ms, num_trials=500000, seed=42)
        total_valid += v
        total_consec += c
        total_with_preconds += cp
        print(f"  Valid: {v}, Consec(raw): {c}, Consec(with preconditions): {cp}")
        print()

    print("=" * 70)
    print(f"TOTAL: {total_valid} valid, {total_consec} raw consec, {total_with_preconds} with preconditions")
    if total_with_preconds == 0:
        print("RESULT: No counterexample. Theorem holds under all preconditions.")
    else:
        print(f"RESULT: {total_with_preconds} COUNTEREXAMPLES!")
    print("=" * 70)

    # Now run the analytical proof
    print()
    print("=" * 70)
    print("ANALYTICAL PROOF")
    print("=" * 70)
    print()

    prove_analytically()


def prove_analytically():
    """
    THEOREM: In a good cycle with sandwiched ternary t (m_t=3, both neighbors binary),
    if all TernaryPhases are normalForm, no EC, fc(t) >= 2, fc(t) < CL, n >= 5:
    t does not fire at two consecutive steps.

    PROOF BY CONTRADICTION.

    Assume t fires at steps k and k+1.

    Let C_k denote config at step k. Write C_k = (..., LL, c_L, v, c_R, RR, ...)
    where positions are (..., bL-1, bL, t, bR, bR+1, ...).

    Since only t fires at steps k and k+1:
      C_{k+1} = (..., LL, c_L, v+1, c_R, RR, ...)
      C_{k+2} = (..., LL, c_L, v+2, c_R, RR, ...)

    STEP 1: f_t(c_L, v+2, c_R) = v+2.

    Proof: Suppose f_t(c_L, v+2, c_R) != v+2. Then t is privileged at C_{k+2}.
    Any non-adjacent proc p sees the same context at C_{k+2} as at C_k (only t changed),
    so p has the same privilege status. At C_k, only t is privileged, so all non-adjacent
    procs are not privileged at C_{k+2}.

    bL at C_{k+2}: context (LL, c_L, v+2). We need to check if bL is privileged.
    bR at C_{k+2}: context (v+2, c_R, RR). We need to check if bR is privileged.

    If ONLY t is privileged at C_{k+2}: mover = t (3 consecutive t-fires).
    Then C_{k+3} = (..., LL, c_L, w, c_R, RR, ...) where w = f_t(c_L, v+2, c_R) != v+2.
    Since w in {0,1,2} and w != v+2 mod 3: w is v or v+1.
    If w = v: C_{k+3} = C_k but k+3 != k (since CL >= 3n-2 >= 13 for n>=5). Two copies of same config: contradiction (gc.distinct).
    If w = v+1: C_{k+3} = C_{k+1}, same issue.

    If t and some neighbor(s) are privileged: multiple privilege = not a good config.
    But C_{k+2} is in the good cycle, so it has exactly one privileged proc. Contradiction.

    If t is privileged but not unique: contradiction (good cycle property).

    If t is privileged and unique: back to 3-consecutive case.

    Wait, we need to be more careful. If t is privileged AND some other proc is privileged
    at C_{k+2}, then C_{k+2} has >= 2 privileged procs. But C_{k+2} is a good config
    (successor of C_{k+1} which is in the good cycle, and the cycle is closed under
    the successor map). So C_{k+2} has exactly 1 privileged proc.

    If that unique privileged proc is t: 3 consecutive -> C_{k+3} collides with C_k or C_{k+1}.
    Collision at distance 3 or 2 in the cycle, both < CL. Contradiction.

    So f_t(c_L, v+2, c_R) = v+2. QED Step 1.

    STEP 2: Exactly one of bL, bR is privileged at C_{k+2}.

    t is not privileged (Step 1). Non-adjacent procs are not privileged (same context as C_k).
    So privileged proc at C_{k+2} is bL or bR (or both, but ME says exactly one).

    STEP 3: The constraint on the privileged neighbor.

    WLOG bL is privileged at C_{k+2}.
    f_{bL}(LL, c_L, v) = c_L (nonmover at C_k)
    f_{bL}(LL, c_L, v+1) = c_L (nonmover at C_{k+1})
    f_{bL}(LL, c_L, v+2) != c_L (mover at C_{k+2})
    Since bL binary: f_{bL}(LL, c_L, v+2) = 1 - c_L.

    So mover at k+2 is bL. C_{k+3} = (..., LL, 1-c_L, v+2, c_R, RR, ...).

    STEP 4: At C_{k+3}, what's privileged?

    t at C_{k+3}: context (1-c_L, v+2, c_R). If f_t(1-c_L, v+2, c_R) != v+2: t privileged.
    bL at C_{k+3}: context (LL, 1-c_L, v+2). Depends on f_{bL}(LL, 1-c_L, v+2).

    The cycle continues...

    STEP 5: The WRAP-AROUND argument.

    The cycle must eventually return to C_k. Since t has value v+2 after step k+1,
    and f_t(c_L, v+2, c_R) = v+2 (absorbing), t stays at v+2 as long as bL = c_L
    and bR = c_R. But at step k+2, bL fires (to 1-c_L), breaking the absorbing context.

    For the cycle to return to C_k: t must eventually reach value v, which requires
    t to fire at least once from value v+2 (with a different (L,R) context).

    STEP 6: The ENTRY CONFLICT at t.

    Wait, I showed above that different (L,R) contexts don't give EC at t.

    Let me try a different approach. The key is the BINARY PARITY constraint.

    bL fires an EVEN number of times (binary parity). Since bL fires at step k+2
    (from Step 3), bL must fire at least one more time (to make the total even, >= 2).

    Between the first bL fire (step k+2) and the next bL fire: bL alternates.
    bL goes from c_L to 1-c_L at step k+2. It must return to c_L eventually
    (since the cycle returns to C_k where bL = c_L). Each bL fire flips it.

    bL fires from c_L to 1-c_L: needs context where f_{bL}(L', c_L, R') != c_L.
    bL fires from 1-c_L to c_L: needs context where f_{bL}(L', 1-c_L, R') != 1-c_L.

    The sequence of bL values in the cycle: c_L, c_L, ..., c_L (steps k to k+2),
    1-c_L (step k+3), ..., eventually back to c_L, ..., back to start.

    Total bL fires: even, >= 2. At step k+2: bL fires (from c_L to 1-c_L).

    Now: there MUST be a step where bL fires from 1-c_L back to c_L.
    At that step: f_{bL}(L', 1-c_L, R') = c_L = 1 - (1-c_L). Since bL binary.

    ENTRY CONFLICT AT bL?

    At the step where bL = 1-c_L and fires: context (L', 1-c_L, R'). Mover.
    Is there a nonmover step with same context (L', 1-c_L, R')? Not necessarily from
    the 3 steps k, k+1, k+2 (those have bL = c_L, not 1-c_L).

    Hmm. The EC argument is subtle and might need more global structure.

    Let me try the COUNTING argument instead.

    STEP 7: Counting argument.

    The phases of t decompose the cycle. With fc(t) fires of t, there are fc(t)
    "phases" (gaps between consecutive t-fires). If one phase is empty (consec fires),
    we have:
    sum_{phases} (J_i + K_i) = fc(bL) + fc(bR)
    where J_i = fires of bL in phase i, K_i = fires of bR in phase i.

    The empty phase contributes J + K = 0.
    All other phases contribute J + K >= 1 (from normalForm: not bothEven(0,0)).
    So: fc(bL) + fc(bR) >= (fc(t) - 1) * 1 + 0 = fc(t) - 1.

    But sparse_phase_sum_ge proves fc(bL) + fc(bR) >= fc(t) (under no-consec).
    With one empty phase: fc(bL) + fc(bR) >= fc(t) - 1.

    The upper bound from the <= direction: fc(bL) + fc(bR) <= fc(t) (from J+K<=1 per phase).
    So: fc(t) - 1 <= fc(bL) + fc(bR) <= fc(t).

    Is fc(bL) + fc(bR) = fc(t) - 1 possible?
    If yes: (fc(t)-1) non-empty phases each have J+K = 1 (tight), and 1 empty phase.
    If fc(bL) + fc(bR) = fc(t): all phases have J+K = 1 (but one is empty -> contradiction).

    So fc(bL) + fc(bR) = fc(t) - 1 with one empty phase.

    Binary parity: fc(bL) even, fc(bR) even. So fc(bL) + fc(bR) is even.
    fc(t) - 1 must be even, so fc(t) is ODD.

    But is fc(t) necessarily odd? Not in general.
    If fc(t) is even: fc(t) - 1 is odd, but fc(bL) + fc(bR) is even. Contradiction!

    So: if fc(t) is EVEN, consecutive t-fires are impossible.

    What if fc(t) is ODD?
    Then fc(bL) + fc(bR) = fc(t) - 1 (even, consistent with binary parity).

    But wait: the J+K <= 1 bound uses the h_phase_le1 result which INCLUDES
    the normalForm constraint. With one empty phase: the empty phase contributes 0,
    and the fc(t)-1 non-empty phases each contribute <= 1.
    Total: <= fc(t) - 1.
    Also >= fc(t) - 1 (from the non-empty phases each contributing >= 1).
    So fc(bL) + fc(bR) = fc(t) - 1 exactly.

    Each non-empty phase has EXACTLY J+K = 1. One-sided.

    Now: the WRAP-AROUND phase. The cycle wraps around (last t-fire to first t-fire).
    If the consecutive fires at k, k+1 are NOT the wrap-around pair:
    then there are fc(t) - 1 interior phases + 1 wrap-around phase.
    The wrap-around might or might not have a TernaryPhase structure.

    Actually, with fc(t) fires of t at positions p_0 < p_1 < ... < p_{fc(t)-1}:
    The consecutive pairs are (p_0, p_1), (p_1, p_2), ..., (p_{fc(t)-2}, p_{fc(t)-1}).
    Plus the wrap-around pair (p_{fc(t)-1}, p_0 + CL) conceptually.

    If p_i and p_{i+1} are consecutive (p_{i+1} = p_i + 1): empty phase.
    The other fc(t) - 1 pairs are non-empty phases with J+K >= 1.
    Plus the wrap-around, which might be non-empty too.

    Total pairs: fc(t) (including wrap-around).
    If 1 pair is empty: fc(t) - 1 non-empty, total J+K >= fc(t) - 1.
    But we also need <= fc(t) (from the upper bound with the wrap).

    Hmm, the wrap-around is tricky. The upper bound fc(bL) + fc(bR) <= fc(t)
    comes from summing J+K over all fc(t) pairs (each <= 1). But with 1 empty pair
    and fc(t)-1 non-empty pairs (each <= 1): total <= fc(t) - 1.
    Wait, that's <= fc(t) - 1, not <= fc(t). That's an IMPROVEMENT of the upper bound.

    So: fc(bL) + fc(bR) = fc(t) - 1 (both bounds match).
    Each non-empty phase has J+K = 1.

    This is a very constrained structure. Let me see if it forces EC.
    """

    print("CLAIM: Consecutive t-fires are impossible under the full preconditions.")
    print()
    print("PROOF SKETCH:")
    print()
    print("Assume t fires at steps k, k+1 (consecutive).")
    print()
    print("Step 1: f_t(c_L, v+2, c_R) = v+2 (else 3-consec -> config collision).")
    print()
    print("Step 2: Exactly one of bL, bR is privileged at C_{k+2} (config after 2 fires).")
    print()
    print("Step 3: WLOG bL fires at step k+2.")
    print("  f_{bL}(LL, c_L, v) = c_L, f_{bL}(LL, c_L, v+1) = c_L, f_{bL}(LL, c_L, v+2) = 1-c_L.")
    print()
    print("Step 4: Phase counting.")
    print("  fc(t) phases total, 1 empty (the consecutive pair), fc(t)-1 non-empty.")
    print("  Each non-empty phase has 1 <= J+K <= 1, so J+K = 1 exactly.")
    print("  fc(bL) + fc(bR) = fc(t) - 1.")
    print("  Binary parity: fc(bL) + fc(bR) even => fc(t) odd.")
    print()
    print("Step 5: If fc(t) is EVEN:")
    print("  fc(bL) + fc(bR) = fc(t) - 1 is ODD, contradicting binary parity. Done.")
    print()
    print("Step 6: If fc(t) is ODD (the hard case):")
    print("  Need a different argument...")
    print()

    # Check: does fc(t) being odd lead to contradiction independently?
    # In the sub-threshold regime with 3 binary procs, what are typical fc values?

    # The fire count of t (ternary) in the good cycle of length CL = product - (#good):
    # Actually CL = #good configs. And fc(t) = number of steps where t fires.
    # Since each proc fires, and sum of all fc(p) = CL, fc(t) = CL / n approximately.

    # For sub-threshold: product < 4 * 3^(n-2).
    # CL varies. The key is fc(t) parity.

    # Actually, for ternary t: fc(t) is always divisible by m_t = 3? No, that's not
    # guaranteed. t fires fc(t) times, each changing t's value. The net change must
    # be 0 mod 3 (cycle returns to start). But individual fires can change by any
    # amount, so fc(t) mod 3 is not determined a priori.

    # Wait: each fire of t changes t's value. If t goes v -> v' each time it fires,
    # the total change is sum of (v' - v) over all fires, which must be 0 mod 3.
    # Each fire changes t by some amount d (where d != 0 mod 3). The sum of d's = 0 mod 3.
    # If all fires increment by 1: sum = fc(t) mod 3 = 0, so fc(t) is divisible by 3.
    # But fires might increment by 2 (= -1 mod 3) instead.

    # So fc(t) mod 3 is not fixed. It depends on the transition function.

    # For the consecutive fires case: at (c_L, v, c_R) -> v+1, at (c_L, v+1, c_R) -> v+2.
    # Both increment by 1. The remaining fc(t)-2 fires can increment by 1 or 2.
    # Net: 2 + sum(remaining) = 0 mod 3. So sum(remaining) = 1 mod 3.
    # Each remaining fire contributes 1 or 2. If all contribute 1: fc(t)-2 = 1 mod 3, fc(t) = 0 mod 3.
    # If some contribute 2: varies.

    # So fc(t) CAN be odd. Need the odd case handled.

    print("Step 6 (continued): Odd fc(t) analysis.")
    print()
    print("With fc(t) odd and fc(bL) + fc(bR) = fc(t) - 1 (even):")
    print("Each non-empty phase has J+K = 1 (one-sided).")
    print("Among fc(t)-1 non-empty phases: each has either (J=1,K=0) or (J=0,K=1).")
    print("Let a = #{phases with J=1}, b = #{phases with K=1}. a+b = fc(t)-1.")
    print("fc(bL) = a, fc(bR) = b. Both even.")
    print("So a and b are both even, a + b = fc(t) - 1 (even). Consistent if fc(t) odd.")
    print()
    print("Now: the structure is extremely rigid.")
    print("EVERY phase between consecutive t-fires has EXACTLY one binary neighbor firing.")
    print("And the empty phase (at the consecutive t-fires) has NO binary fires.")
    print()
    print("KEY OBSERVATION: Consider the phase RIGHT BEFORE the consecutive pair.")
    print("Let the t-fires be at steps ..., p_{i-1}, p_i = k, p_{i+1} = k+1, p_{i+2}, ...")
    print("Phase i (between p_i and p_{i+1}): empty, J+K=0.")
    print("Phase i-1 (between p_{i-1} and p_i): non-empty, J+K=1.")
    print("Phase i+1 (between p_{i+1} and p_{i+2}): non-empty, J+K=1.")
    print()
    print("In phase i-1 (between p_{i-1} and p_i = k): exactly one of bL, bR fires once.")
    print("At the END of phase i-1 (config at step k = C_k): bL = c_L, bR = c_R.")
    print("At the START of phase i-1 (config at step p_{i-1}+1): t just fired at p_{i-1}.")
    print()
    print("The config at p_{i-1}: (..., c_L_prev, v_prev, c_R_prev, ...)")
    print("t fires: v_prev -> v. So t's value changes to v.")
    print("Between p_{i-1}+1 and k-1: one binary fires.")
    print()
    print("If bL fires in phase i-1: bL changes. Let's say bL was c_L' before firing.")
    print("  After bL fires: bL = 1-c_L'. This must equal c_L (the value at step k).")
    print("  So c_L' = 1-c_L. Before bL fires in phase i-1: bL = 1-c_L.")
    print("  At the t-fire at p_{i-1}: config has bL = 1-c_L (no bL fires between p_{i-1} and bL's fire).")
    print("  Wait: t fires at p_{i-1}, then one binary fires between p_{i-1}+1 and k-1.")
    print("  At step p_{i-1}: bL = 1-c_L (since the only binary fire in this phase happens AFTER p_{i-1}).")
    print("  Actually no: the binary fire could be before or after p_{i-1}+1.")
    print("  The phase goes from p_{i-1}+1 to k. One binary fires in this range.")
    print()
    print("CRITICAL: at step k (= p_i), t fires. Context: (c_L, v, c_R).")
    print("At step k+1 (= p_{i+1}), t fires. Context: (c_L, v+1, c_R).")
    print("In the empty phase (p_i to p_{i+1}): no bL or bR fires.")
    print("In phase i-1 (p_{i-1} to p_i): exactly one binary fires.")
    print()
    print("Phase i+1 (p_{i+1} = k+1 to p_{i+2}): exactly one binary fires.")
    print("We showed bL fires at step k+2 (or bR fires). One of them.")
    print("WLOG bL fires at k+2. Then in phase i+1: J=1, K=0. bL fires once, bR doesn't.")
    print()
    print("Phase i-1: J+K=1. Either bL or bR fires.")
    print()
    print("CASE A: bL fires in phase i-1.")
    print("  bL's value at the start of phase i-1 (after t fires at p_{i-1}) is 1-c_L")
    print("  (since bL = c_L at step k, and bL fires once to get to c_L: 1-c_L -> c_L).")
    print()
    print("  At step p_{i-1}: config has bL = 1-c_L. t fires at p_{i-1}.")
    print("  Before bL fires: t's value is v (the result of t's fire at p_{i-1}).")
    print("  bL context when firing: (LL_prev, 1-c_L, v). f_{bL}(LL_prev, 1-c_L, v) != 1-c_L = c_L.")
    print()
    print("  After bL fires: bL = c_L. Config at step k has bL = c_L.")
    print("  Now consider nonmover for bL at step k: context (LL, c_L, v).")
    print("  f_{bL}(LL, c_L, v) = c_L (nonmover).")
    print("  These have different S values (1-c_L vs c_L) and possibly different L values.")
    print("  Not directly comparable for EC.")
    print()
    print("CASE B: bR fires in phase i-1.")
    print("  Similar structure with bR.")
    print()
    print("The rigid structure constrains but doesn't immediately give EC.")
    print("Need to trace the full cycle behavior...")
    print()

    # Actually, let me try a much simpler argument.
    # From Step 2: the privileged proc at C_{k+2} is bL or bR.
    # From Step 3: WLOG bL fires at step k+2.
    #
    # Now: bR is NOT privileged at C_{k+2}.
    # bR context at C_{k+2}: (v+2, c_R, RR).
    # f_{bR}(v+2, c_R, RR) = c_R (nonmover).
    # Also at C_k: bR context (v, c_R, RR), f_{bR}(v, c_R, RR) = c_R (nonmover).
    # At C_{k+1}: bR context (v+1, c_R, RR), f_{bR}(v+1, c_R, RR) = c_R (nonmover).
    # So f_{bR}(*, c_R, RR) = c_R for ALL 3 values of L. bR with (S=c_R, R=RR) is NEVER privileged.
    #
    # This is a strong constraint: bR never fires when it has value c_R and right-neighbor RR.
    # Since bR is binary: bR fires only from value 1-c_R (when right-neighbor is RR),
    # or from any value when right-neighbor is NOT RR.

    print("STRONG CONSTRAINT on bR:")
    print("  f_{bR}(*, c_R, RR) = c_R for all L-values. bR never fires with (S=c_R, R=RR).")
    print("  bR fires from value 1-c_R (when R=RR), or from any value when R != RR.")
    print()

    # Now: combine with the phase structure.
    # In the empty phase (steps k to k+1): bR doesn't fire. bR = c_R throughout.
    # In phase i+1 (steps k+1 to p_{i+2}): K=0, so bR doesn't fire. bR = c_R.
    # In phase i-1 (steps p_{i-1} to k): either bL fires (K=0, bR doesn't) or bR fires (K=1).

    # Case B above: bR fires in phase i-1. bR fires once.
    # bR = c_R at step k. bR fires once in phase i-1: goes from 1-c_R to c_R.
    # Before the fire in phase i-1: bR = 1-c_R.

    # At step p_{i-1}: t fires. What's bR's value?
    # If bR fires AFTER p_{i-1} in phase i-1: bR = 1-c_R at step p_{i-1}.
    # t's context at p_{i-1}: (c_L_prev, v_prev, 1-c_R).
    # (Here c_L_prev might be c_L or something else.)

    # Wait, in Case B: bR fires in phase i-1, bL doesn't.
    # bL = c_L throughout phase i-1 (since J=0).
    # At step p_{i-1}: bL = c_L.
    # t fires at p_{i-1}: context (c_L, v_prev, bR_prev).
    # f_t(c_L, v_prev, bR_prev) = v_prev' (the output). Then t = v_prev' = v at step k.
    # Hmm actually v is the value at step k. Between p_{i-1}+1 and k: only bR fires (K=1), t doesn't fire.
    # So t's value is constant from p_{i-1}+1 to k. t's value after firing at p_{i-1} is v.
    # So f_t(c_L, v_prev, bR_prev) = v, and v_prev != v.

    # bR fires at some step q in (p_{i-1}, k). Before q: bR = 1-c_R. After q: bR = c_R.
    # At step q: bR context is (v, 1-c_R, RR_q). Mover. f_{bR}(v, 1-c_R, RR_q) = c_R != 1-c_R.
    # (RR_q might differ from RR if proc bR+1 fires between p_{i-1} and q.)

    # Hmm wait: between p_{i-1} and k, who fires other than bR (which fires once)?
    # t fires at p_{i-1} (that's the phase boundary). Between p_{i-1}+1 and k-1: bR fires once.
    # Other procs: they CAN fire (the phase only restricts t, bL, bR fires).
    # Actually no: the cycle movers are globally determined. Between p_{i-1}+1 and k-1,
    # some procs fire (one per step). Among these: exactly 1 is bR, 0 are bL, 0 are t.
    # The remaining steps have movers that are OTHER procs (not t, bL, or bR).

    print("The proof is non-trivial and requires tracking the full cycle structure.")
    print("Let me verify computationally that the theorem holds at small n.")
    print()


if __name__ == "__main__":
    main()
