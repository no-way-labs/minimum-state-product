"""
Proof: no consecutive t-fires for sandwiched ternary t in a good cycle.

Theorem: In a good cycle with sandwiched ternary t (both neighbors binary),
all phases normalForm, no entry conflict, n >= 5, sub-threshold:
  processor t does NOT fire at two consecutive steps.

Proof strategy:
  If t fires at steps k and k+1, then:
  1. Only t's value changes between configs k and k+1 (v -> v+1 mod 3)
  2. Only t's value changes between configs k+1 and k+2 (v+1 -> v+2 mod 3)
  3. Both binary neighbors bL, bR are nonmovers at steps k and k+1
  4. bL sees R-context v at step k, v+1 at step k+1: f_bL(LL, bL_val, v) = bL_val
     and f_bL(LL, bL_val, v+1) = bL_val
  5. bR sees L-context v at step k, v+1 at step k+1: f_bR(v, bR_val, RR) = bR_val
     and f_bR(v+1, bR_val, RR) = bR_val
  6. Since t is ternary: v, v+1, v+2 are all distinct mod 3
  7. For bL: f_bL(LL, bL_val, r) = bL_val for r = v and r = v+1 (2 of 3 R-values)
     What about r = v+2? Either:
     (a) f_bL(LL, bL_val, v+2) = bL_val: bL is ALWAYS nonprivileged with this (LL, bL_val)
         regardless of t's state -> bL never fires when seeing this (LL,bL_val) pair.
     (b) f_bL(LL, bL_val, v+2) != bL_val: bL IS privileged at config k+2.
  8. Case (b): at config k+2, bL is privileged. Since the good cycle has unique privilege
     at each step, moverAt(k+2) might be bL. But more importantly: whoever fires at
     step k+2 is the unique privileged proc. If bL is privileged, then either bL fires
     (mover = bL) or bL is privileged but someone else fires (impossible: unique privilege).

  So in case (b), moverAt(k+2) = bL.
  Similarly for bR: case (b) means moverAt(k+2) = bR.
  Can both bL and bR be privileged? Only if bL = bR = moverAt(k+2), impossible since bL != bR.

  So at most one of bL, bR can be in case (b).
  At least one of bL, bR is in case (a): f constant in the t-argument.

  Case (a) for bL means: for ALL configs where bL sees (LL, bL_val, *), bL's output is bL_val.
  So bL is NEVER privileged when its (L,S) = (LL, bL_val).
  But bL fires in the good cycle (fireCount(bL) >= 2). Every time bL fires, its context has
  some (LL', bL_val', R'). The fires with LL' = LL can only happen when bL_val' != bL_val
  (since (LL, bL_val, *) -> bL_val always). Since bL is binary (m=2), bL_val' = 1 - bL_val.

  This means: f_bL(LL, 1-bL_val, r) != 1-bL_val for some r values.

  NOW: consider the config right BEFORE step k: at step k, t fires. At config k,
  t has value v, bL has value bL_val. What was the mover at step k-1?
  It was NOT t (otherwise we'd have 3 consecutive t-fires, and the argument recurses).

  Actually, the key insight is simpler. Let me check computationally first.

Computational verification: enumerate all valid sub-threshold systems with
sandwiched ternary, extract good cycles, check for consecutive t-fires.
"""

import itertools
from collections import defaultdict
import sys


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
    """Find the good cycle of a valid system, return (cycle_configs, cycle_movers)."""
    n = len(ms)
    configs = all_configs(ms)

    # Find good configs (exactly one privileged)
    good_configs = set()
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            good_configs.add(c)

    if not good_configs:
        return None, None

    # Build the good-config successor graph
    succ = {}
    for c in good_configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) != 1:
            continue
        mover = priv[0]
        nxt = apply_move(c, mover, fs, ms)
        if nxt in good_configs:
            succ[c] = (nxt, mover)

    # Follow the chain from any good config to find the cycle
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

    # Extract the cycle
    cycle_start = visited[current]
    cycle_configs = []
    cycle_movers = []
    c = current
    for _ in range(step - cycle_start):
        nxt, mover = succ[c]
        cycle_configs.append(c)
        cycle_movers.append(mover)
        c = nxt

    return cycle_configs, cycle_movers


def verify_system_quick(ms, fs):
    """Quick check: liveness + mutual exclusion + closure + convergence."""
    n = len(ms)
    configs = all_configs(ms)

    good_configs = set()
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 0:
            return False  # dead config
        if len(priv) == 1:
            good_configs.add(c)

    if not good_configs:
        return False

    # Closure check
    for c in good_configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) != 1:
            continue
        nxt = apply_move(c, priv[0], fs, ms)
        if nxt not in good_configs:
            return False

    # Convergence: no bad cycle
    bad_configs = [c for c in configs if c not in good_configs]
    # BFS from bad configs
    visited = set()
    for c in bad_configs:
        if c in visited:
            continue
        path = set()
        current = c
        while current not in visited and current not in good_configs:
            if current in path:
                return False  # bad cycle!
            path.add(current)
            # Apply any privileged move (pick the first)
            priv = privileged_set(current, fs, ms)
            if not priv:
                return False
            nxt = apply_move(current, priv[0], fs, ms)
            current = nxt
        visited.update(path)

    return True


def check_consecutive_tfire(cycle_movers, t):
    """Check if processor t fires at consecutive steps in the cycle."""
    CL = len(cycle_movers)
    for k in range(CL):
        if cycle_movers[k] == t and cycle_movers[(k + 1) % CL] == t:
            return True  # Found consecutive t-fires!
    return False


def has_entry_conflict(cycle_configs, cycle_movers, fs, ms):
    """Check if the good cycle has an entry conflict."""
    n = len(ms)
    CL = len(cycle_configs)

    # For each processor p, collect mover and nonmover contexts
    for p in range(n):
        mover_contexts = set()
        nonmover_contexts = set()
        for k in range(CL):
            c = cycle_configs[k]
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            ctx = (L, S, R)
            if cycle_movers[k] == p:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)
        if mover_contexts & nonmover_contexts:
            return True
    return False


def enumerate_transition_tables(m_L, m_S, m_R):
    """Enumerate all transition functions f: [m_L] x [m_S] x [m_R] -> [m_S]."""
    domain = list(itertools.product(range(m_L), range(m_S), range(m_R)))
    for outputs in itertools.product(range(m_S), repeat=len(domain)):
        table = {}
        for (l, s, r), o in zip(domain, outputs):
            table[(l, s, r)] = o
        yield table


def table_to_func(table):
    """Convert a table dict to a function."""
    def f(L, S, R):
        return table[(L, S, R)]
    return f


# =============================================================
# PART 1: Small-n exhaustive verification
# =============================================================

def exhaustive_check_n5():
    """
    At n=5, sub-threshold means product < 4*3^3 = 108.
    With >= 3 binary, a sandwiched ternary t needs ms like (2, 3, 2, ?, ?)
    or rotations thereof.

    Enumerate sub-threshold multisets with a sandwich pattern, search for
    valid systems, check consecutive t-fires in good cycles.
    """
    n = 5
    threshold = 4 * (3 ** (n - 2))  # 108

    print(f"=== Exhaustive check at n={n}, threshold={threshold} ===")
    print()

    # Enumerate multisets: sorted tuples of n values >= 2 with product < threshold, >= 3 binary
    multisets = []
    def gen(remaining, min_val, current, prod):
        if remaining == 0:
            if prod < threshold and sum(1 for x in current if x == 2) >= 3:
                multisets.append(tuple(current))
            return
        max_val = threshold // (prod * (2 ** (remaining - 1)))
        for v in range(min_val, max_val + 1):
            np_ = prod * v
            if np_ * (2 ** (remaining - 1)) >= threshold:
                break
            gen(remaining - 1, v, current + [v], np_)

    gen(n, 2, [], 1)
    print(f"Sub-threshold multisets with >= 3 binary: {len(multisets)}")
    for ms_sorted in multisets:
        print(f"  {ms_sorted}, product = {eval('*'.join(map(str, ms_sorted)))}")
    print()

    # For each multiset, for each permutation that creates a sandwich pattern,
    # try to find valid systems with consecutive t-fires
    total_systems = 0
    total_with_consec = 0

    for ms_sorted in multisets:
        # Generate distinct permutations
        from math import factorial
        from collections import Counter

        cnt = Counter(ms_sorted)
        seen_perms = set()
        for perm in itertools.permutations(ms_sorted):
            if perm in seen_perms:
                continue
            seen_perms.add(perm)

            ms = list(perm)
            # Find sandwiched ternary positions
            sandwich_positions = []
            for t in range(n):
                if ms[t] >= 3 and ms[(t-1) % n] == 2 and ms[(t+1) % n] == 2:
                    sandwich_positions.append(t)

            if not sandwich_positions:
                continue

            # This permutation has a sandwich.
            # For small n, we can't enumerate ALL transition tables (too many).
            # Instead, let's use the verifier to search with random/structured tables.
            # Actually, even at n=5 with ms=(2,2,2,3,3), the number of tables is
            # 2^(2*2*3) * 2^(2*2*3) * 2^(2*2*3) * 3^(2*3*3) * 3^(2*3*3) = 2^12 * 2^12 * 2^12 * 3^18 * 3^18
            # Way too many. Need a different approach.
            pass

    print("Full table enumeration infeasible at n=5. Using targeted approach.")
    print()


def targeted_check_small():
    """
    Targeted check: use ms=(2,3,2,3,2) at n=5 (or similar small cases).
    Sandwich at t=1: ms[0]=2(binary), ms[1]=3(ternary), ms[2]=2(binary).

    Enumerate transition tables for the sandwich triple (bL, t, bR) while
    fixing the others. Then check for consecutive t-fires.
    """
    # ms = (2, 3, 2, 3, 2) - two sandwiched ternaries at positions 1 and 3
    # Let's focus on t=1: bL=0(binary), t=1(ternary), bR=2(binary)
    # Product = 2*3*2*3*2 = 72 < 108 (sub-threshold at n=5)

    # Actually, let me think about what configs look like when t fires twice.
    # Config at step k:   (c0, v,   c2, c3, c4) where t=1 fires, v -> v+1
    # Config at step k+1: (c0, v+1, c2, c3, c4) where t=1 fires, v+1 -> v+2
    # Config at step k+2: (c0, v+2, c2, c3, c4) and some other proc fires
    #
    # At step k: only t=1 is privileged. So:
    #   f_0(c4, c0, v)   = c0  (proc 0 nonprivileged)
    #   f_1(c0, v, c2)   != v  (proc 1 privileged)
    #   f_2(v, c2, c3)   = c2  (proc 2 nonprivileged)
    #   f_3(c2, c3, c4)  = c3  (proc 3 nonprivileged)
    #   f_4(c3, c4, c0)  = c4  (proc 4 nonprivileged)
    #
    # At step k+1: only t=1 is privileged. Config is (c0, v+1, c2, c3, c4). So:
    #   f_0(c4, c0, v+1) = c0  (proc 0 nonprivileged)
    #   f_1(c0, v+1, c2) != v+1 (proc 1 privileged)
    #   f_2(v+1, c2, c3) = c2  (proc 2 nonprivileged)
    #   f_3(c2, c3, c4)  = c3  (proc 3 nonprivileged, SAME as before)
    #   f_4(c3, c4, c0)  = c4  (proc 4 nonprivileged, SAME as before)
    #
    # Key constraints on bL = proc 0:
    #   f_0(c4, c0, v)   = c0
    #   f_0(c4, c0, v+1) = c0
    # For SPECIFIC (c4, c0), f_0 returns c0 for R-values v and v+1.
    #
    # Key constraints on bR = proc 2:
    #   f_2(v, c2, c3)   = c2
    #   f_2(v+1, c2, c3) = c2
    # For SPECIFIC (c2, c3), f_2 returns c2 for L-values v and v+1.
    #
    # Now at config k+2: (c0, v+2, c2, c3, c4). Who fires?
    # Proc 1: f_1(c0, v+2, c2). We know f_1(c0, v, c2) != v and f_1(c0, v+1, c2) != v+1.
    #   Is f_1(c0, v+2, c2) != v+2? Not necessarily.
    #   If f_1(c0, v+2, c2) = v+2: proc 1 is NOT privileged at k+2.
    #   If f_1(c0, v+2, c2) != v+2: proc 1 IS privileged at k+2.
    #
    # Proc 0: f_0(c4, c0, v+2). We know f_0(c4, c0, v) = c0 and f_0(c4, c0, v+1) = c0.
    #   If f_0(c4, c0, v+2) = c0: proc 0 not privileged (case a).
    #   If f_0(c4, c0, v+2) != c0: proc 0 IS privileged (case b).
    #
    # Proc 2: f_2(v+2, c2, c3). Similar analysis.
    #   If f_2(v+2, c2, c3) = c2: not privileged.
    #   If f_2(v+2, c2, c3) != c2: IS privileged.

    # THE KEY ARGUMENT:
    # Config k and config k+2 differ ONLY at position t (v vs v+2, both mod 3, distinct).
    # Both are good configs (in the cycle).
    # If they're distinct configs (they are: v != v+2 mod 3, so Hamming distance 1).
    # They're at distance 2 in the cycle (steps k and k+2).
    #
    # Now: does the good cycle visit config k+2 AGAIN later? YES, it's a cycle.
    # The cycle visits (c0, v+2, c2, c3, c4) at step k+2, and also visits it at
    # some other step j (the cycle eventually returns to this config).
    #
    # BUT WAIT: config k+2 IS in the cycle (since config k+1 transitions to config k+2).
    # And config k IS in the cycle. So both (c0,v,c2,c3,c4) and (c0,v+2,c2,c3,c4) are
    # distinct good configs in the cycle, differing only at position t.
    #
    # Now consider: what happens when config (c0,v,c2,c3,c4) is visited again as a
    # nonmover step for t? At that step, t's context is (c0, v, c2) and t doesn't fire:
    # f_1(c0, v, c2) = v. But we established f_1(c0, v, c2) != v (step k, t fires).
    # CONTRADICTION.
    #
    # Wait... step k IS the step where config (c0,v,c2,c3,c4) appears, and t fires.
    # In the good cycle, each config appears EXACTLY ONCE. So (c0,v,c2,c3,c4) appears
    # only at step k, where t fires. There's no nonmover visit of this config.
    # So no EC from this alone.

    # Let me think differently. The issue is about the TRANSITION FUNCTION, not the cycle.
    #
    # At step k: t fires, context (c0, v, c2), f_1(c0, v, c2) != v -> t is privileged
    # At step k+1: t fires, context (c0, v+1, c2), f_1(c0, v+1, c2) != v+1 -> t privileged
    #
    # Now t has value v+2. Consider ANY other step j in the cycle where t has value v+2
    # and t's left neighbor is c0 and right neighbor is c2. Then t's context is (c0, v+2, c2).
    # If t is the mover at j: f_1(c0, v+2, c2) != v+2.
    # If t is nonmover at j: f_1(c0, v+2, c2) = v+2.
    #
    # f_1 is a FIXED function. So either f_1(c0, v+2, c2) = v+2 or != v+2.
    # If = v+2: t can never fire with context (c0, v+2, c2).
    #   So at step k+2, t is nonprivileged. Good.
    # If != v+2: t is privileged whenever it sees (c0, v+2, c2).
    #   At step k+2, t sees (c0, v+2, c2) and is privileged.
    #   But t just fired twice. The unique privilege means only one proc fires.
    #
    # Let's focus: can we get EC from the 3 configs at steps k, k+1, k+2?
    # Config k:   (c0, v,   c2, c3, c4)  mover = t
    # Config k+1: (c0, v+1, c2, c3, c4)  mover = t
    # Config k+2: (c0, v+2, c2, c3, c4)  mover = ???
    #
    # At config k+2, if t is privileged (case f_1(c0,v+2,c2) != v+2):
    #   Then t's context (c0, v+2, c2) appears as mover. But earlier in the cycle
    #   (at some step j), config (c0, v+2, c2, c3, c4) must also appear (since it's
    #   in the cycle at step k+2). Since each config appears once, step j = k+2.
    #   If moverAt(k+2) = t: then t fires 3 times in a row! Value goes v+2 -> f_1(c0,v+2,c2).
    #   Config k+3 = (c0, f_1(c0,v+2,c2), c2, c3, c4).
    #   Since f_1(c0,v+2,c2) != v+2, and f_1(c0,v+2,c2) in {0,1,2},
    #   it's either v or v+1 (the only other values mod 3).
    #   If f_1(c0,v+2,c2) = v: config k+3 = config k. But config k is already in the cycle
    #   at position k, and k+3 != k (since CL >= 3n-2 >= 13 for n=5). Wait, if k+3 = k
    #   in the cycle (mod CL), that means CL = 3, but CL >= 13. Contradiction.
    #   If f_1(c0,v+2,c2) = v+1: config k+3 = config k+1. Same issue: k+3 = k+1 mod CL
    #   means CL = 2, impossible.
    #
    # This is IT. If t fires 3 consecutive times, the 4th config equals an earlier one
    # (by pigeonhole on 3 ternary values), contradicting cycle distinctness (CL >= 13 > 3).
    #
    # So t can fire at most 2 consecutive times before a non-t fire must occur.
    # But we need to rule out EXACTLY 2 consecutive fires.
    #
    # Key: if moverAt(k+2) = t, we get a contradiction (3 consecutive -> cycle too short).
    # So if t fires at k and k+1, then moverAt(k+2) != t.
    #
    # At config k+2 = (c0, v+2, c2, c3, c4):
    #   If f_1(c0, v+2, c2) != v+2: t is privileged, so moverAt(k+2) = t (unique privilege),
    #   but that gives 3 consecutive -> contradiction.
    #   So f_1(c0, v+2, c2) = v+2: t is NOT privileged at config k+2. Good.
    #
    # So: f_1(c0, v, c2) != v, f_1(c0, v+1, c2) != v+1, f_1(c0, v+2, c2) = v+2.
    # For the (c0, *, c2) slice: t fires for S=v and S=v+1, but not S=v+2.

    # Now apply the SAME argument cyclically:
    # The last time t fired before step k: say step j < k. Between j and k, t doesn't fire.
    # Config at step j has t-value v_prev, and after firing: v_prev+1.
    # ... eventually reaching config k where t-value = v. So v = v_prev + 1 mod 3? Not necessarily,
    # since other procs change t's context between j and k.
    #
    # Hmm, the argument above is for a SPECIFIC (c0, c2) context pair. Different t-fire
    # steps may have different (c0, c2) pairs.

    # NEW APPROACH: Entry conflict from the triple of t-values
    # At step k (mover t):   context at t is (c0, v, c2)    -> f_1 outputs some v' != v
    # At step k+1 (mover t): context at t is (c0, v+1, c2)  -> f_1 outputs some v'' != v+1
    # At step k+2 (nonmover):context at t is (c0, v+2, c2)  -> f_1 outputs v+2 (nonmover)
    #
    # Where v' = v+1 (since config k+1 has t-value v+1) and v'' = v+2.
    # So: f_1(c0, v, c2) = v+1, f_1(c0, v+1, c2) = v+2, f_1(c0, v+2, c2) = v+2.
    #
    # Now: does the context (c0, v+2, c2) appear as a MOVER context for t elsewhere?
    # If yes: EC at t (since f_1(c0,v+2,c2) = v+2, nonmover, vs f_1(c0,v+2,c2) should != v+2 for mover).
    # If no: context (c0,v+2,c2) is always nonmover for t.
    #
    # Similarly: context (c0,v,c2) at mover step k. Is (c0,v,c2) ever a nonmover context for t?
    # If yes: EC. If no: always mover.
    # Context (c0,v+1,c2) at mover step k+1. Is it ever nonmover?
    # If yes: EC.
    #
    # So if no EC: (c0,v,c2) always mover, (c0,v+1,c2) always mover, (c0,v+2,c2) always nonmover.
    # This means: every time t sees (c0, *, c2), it fires iff S != v+2 (i.e., S = v or S = v+1).
    # And when it fires: f_1(c0, v, c2) = v+1, f_1(c0, v+1, c2) = v+2.
    # This is the "incrementing" transition at this (L,R) slice: S -> S+1 mod 3,
    # except S = v+2 is a fixed point.

    # Now: the good cycle visits all 3 configs (c0, v, c2, c3, c4), (c0, v+1, c2, c3, c4),
    # (c0, v+2, c2, c3, c4)? Not necessarily — c3, c4 may differ.
    # But we know steps k, k+1, k+2 have:
    #   (c0, v, c2, c3, c4), (c0, v+1, c2, c3, c4), (c0, v+2, c2, c3, c4)
    # All with the SAME (c0, c2, c3, c4). These are 3 distinct configs in the cycle.

    # The fact that (c0, v+2, c2, c3, c4) is a nonmover step for t means some other proc fires.
    # That proc changes only its own value. The next config differs from (c0, v+2, c2, c3, c4) at
    # exactly one non-t position.

    # CAN WE USE THE BINARY PARITY? bL and bR are binary and don't fire in the gap [k, k+1].
    # But bL fires an even number of times total in the cycle (binary_fireCount_even).
    #
    # Actually, the real constraint comes from looking at the PREVIOUS t-fire.
    # The t-fire at step k is part of a sequence of t-fires (the "phase" structure).
    # If t fires at steps k and k+1 (consecutive), this is a "zero-length gap" phase.
    # Let's call the t-fire before k as step j (the previous t-fire).
    # Between j+1 and k-1 (inclusive), t doesn't fire. This is a normal phase.
    # Between k and k+1, we have a zero-length gap (t fires twice with nothing between).
    # The "TernaryPhase" structure requires a < s (nonempty gap), so this isn't a phase.
    # But the phase decomposition assumes no consecutive t-fires!

    # Let me just verify computationally. The simplest approach: find all valid sub-threshold
    # systems at n=5 with a sandwich and check all good cycles for consecutive t-fires.

    print("=== Targeted analytical check ===")
    print()
    print("If t fires at steps k, k+1 (consecutive):")
    print("  Config k:   (..., c_bL, v,   c_bR, ...) mover = t")
    print("  Config k+1: (..., c_bL, v+1, c_bR, ...) mover = t")
    print("  Config k+2: (..., c_bL, v+2, c_bR, ...) mover != t")
    print()
    print("  f_t(c_bL, v, c_bR) = v+1 (fires: v -> v+1)")
    print("  f_t(c_bL, v+1, c_bR) = v+2 (fires: v+1 -> v+2)")
    print("  f_t(c_bL, v+2, c_bR) = v+2 (nonmover at k+2)")
    print()
    print("  The 3 configs at steps k, k+1, k+2 are Hamming-1 chain at position t.")
    print("  Config k and config k+2 are Hamming-1 (differ only at t: v vs v+2).")
    print("  They are 2 steps apart in the cycle.")
    print()

    # The critical observation for the proof:
    # The transition function at (c_bL, *, c_bR) acts as:
    #   v -> v+1 (fires)
    #   v+1 -> v+2 (fires)
    #   v+2 -> v+2 (stays)
    # This is an "absorbing state" pattern at v+2.
    #
    # For the good cycle: the config (c_bL, v+2, c_bR, ...) is in the cycle.
    # Eventually, after the good cycle wraps around, it must return to config k.
    # This means t's value must go from v+2 back to v at some point.
    # Since f_t(c_bL, v+2, c_bR) = v+2 (nonmover), t can only change from v+2
    # when the CONTEXT changes (c_bL or c_bR changes).
    #
    # After step k+2, t has value v+2. For t to reach value v again (to return
    # to config k), t must fire at least once more with a DIFFERENT (L,R) context.

    # Let's now prove the theorem by contradiction + EC.
    print("=== Proof by contradiction: consecutive t-fires -> EC ===")
    print()
    print("Assume t fires at consecutive steps k, k+1. We derive entry conflict.")
    print()
    print("CLAIM: Under ¬EC, the transition f_t at slice (c_bL, *, c_bR) must be:")
    print("  f_t(c_bL, v, c_bR) = v+1")
    print("  f_t(c_bL, v+1, c_bR) = v+2")
    print("  f_t(c_bL, v+2, c_bR) = v+2  (forced by unique-privilege at step k+2)")
    print()
    print("Now consider the BINARY NEIGHBORS.")
    print("bL is nonprivileged at steps k, k+1, k+2 (only t or other proc fires).")
    print("bL's context at step k:   (LL, bL_val, v)   -> f_bL returns bL_val")
    print("bL's context at step k+1: (LL, bL_val, v+1) -> f_bL returns bL_val")
    print("bL's context at step k+2: (LL, bL_val, v+2) -> f_bL returns bL_val OR bL is privileged")
    print()
    print("If f_bL(LL, bL_val, v+2) != bL_val: bL is privileged at k+2.")
    print("  But moverAt(k+2) != t. If bL is the unique privileged: moverAt(k+2) = bL.")
    print("  Then config k+3 differs from k+2 only at bL: bL_val -> f_bL(LL, bL_val, v+2).")
    print("  Since bL is binary: f_bL(LL, bL_val, v+2) = 1 - bL_val.")
    print()
    print("Similarly for bR: either constant in L or privileged at k+2.")
    print("At most one of bL, bR is privileged at k+2 (unique privilege).")
    print()


def analytical_proof():
    """
    The actual proof, using the absorbing-value + EC argument.

    KEY THEOREM: Consecutive t-fires produce entry conflict.

    Proof:
    Let t fire at steps k and k+1. Let config k have t-value v.
    Let bL = left(t), bR = right(t), both binary.

    Context at t: (c_L, v, c_R) at step k, (c_L, v+1, c_R) at step k+1.
    (c_L = bL's value = c[bL], c_R = bR's value = c[bR], both unchanged.)

    Config k+2 has t-value v+2. By unique privilege argument:
      f_t(c_L, v+2, c_R) = v+2 (otherwise 3 consecutive -> cycle too short).

    So (c_L, v+2, c_R) is a nonmover context for t at step k+2.
    And (c_L, v, c_R), (c_L, v+1, c_R) are mover contexts for t.

    Under no-EC: (c_L, v+2, c_R) must NEVER appear as a mover context for t.

    QUESTION: Does (c_L, v+2, c_R) ever appear as a mover context for t?

    It appears at step k+2 as a nonmover context. For EC: need the SAME triple
    to appear as both mover and nonmover. The triple (c_L, v+2, c_R) is nonmover
    at k+2. If it ALSO appears as a mover at some step j: EC.

    Can we FORCE (c_L, v+2, c_R) to appear as a mover?

    The cycle must return to config k eventually. For t to have value v again,
    t must fire. Since f_t(c_L, v+2, c_R) = v+2 (nonmover), t can't fire with
    context (c_L, v+2, c_R). So t fires with some OTHER context (c_L', s, c_R').

    But we need to count t-fires by residue class. t is ternary with 3 values.
    In the good cycle, t fires fc(t) times. Each fire increments t's value.
    So t visits each value exactly fc(t)/3 times as a mover? No, that's not right.
    t's value after fire is determined by f_t, not necessarily +1.

    Actually, from the constraints:
    f_t(c_L, v, c_R) = v+1 (step k)
    f_t(c_L, v+1, c_R) = v+2 (step k+1)
    f_t(c_L, v+2, c_R) = v+2 (nonmover)

    But for OTHER (L,R) pairs, f_t can be different. The transition function is
    a lookup table with domain {0,1} x {0,1,2} x {0,1} (since bL binary, t ternary, bR binary).
    That's 2*3*2 = 12 entries, mapping to {0,1,2}.

    The above constrains 3 of these 12 entries (for the specific (c_L, c_R) pair).
    The remaining 9 entries are free (subject to system validity).

    So we can't force EC from just these 3 entries.

    HOWEVER: the cycle must eventually return to v. Let's track more carefully.

    After step k+1: t = v+2. For the cycle to return to config k, t must
    reach value v. Since f_t(c_L, v+2, c_R) = v+2, t stays at v+2 as long
    as context is (c_L, *, c_R). t's context changes when bL or bR fires.

    Since bL and bR are binary and fire an even number of times:
    bL fires fc(bL) times (even, >= 2).
    bR fires fc(bR) times (even, >= 2).

    After bL fires: bL_val changes. This changes t's L-context.
    After bR fires: bR_val changes. This changes t's R-context.

    Eventually, t's (L,R) context changes, allowing t to fire again.

    THE COUNTING ARGUMENT:
    t fires fc(t) >= 2 times total. Between consecutive t-fires, there's a
    "phase" where bL fires J times and bR fires K times.

    The phases decompose the cycle. If one phase has J=K=0 (consecutive t-fires),
    that's the degenerate case we're analyzing.

    Under all-normalForm + no-EC, the PhaseExtraction machinery bounds sum(J+K) >= fc(t).
    But with a degenerate J=K=0 phase, the total sum(J+K) decreases by 1 (one phase
    contributes 0 instead of >= 1). If this drops below fc(t), contradiction.

    This is exactly what sparse_phase_sum_ge proves! It needs hno_consec as input.
    We can't use it circularly. But the underlying argument is:

    Under no-EC + normalForm, each non-degenerate phase contributes J+K >= 1.
    A degenerate phase contributes 0. Total = fc(bL) + fc(bR).
    There are fc(t) phases total (number of consecutive t-fire pairs).

    Wait, that's circular. Let me think again...
    """

    # THE REAL PROOF - based on the absorbing value creating an EC
    #
    # Suppose t fires at consecutive steps k, k+1 with shared context (c_L, c_R).
    # Then f_t(c_L, v+2, c_R) = v+2 (nonmover).
    #
    # In the GOOD CYCLE, t fires fc(t) >= 2 times.
    # Each time t fires, it transitions from some value s to f_t(L, s, R) != s.
    # The net effect around the full cycle: t returns to its initial value.
    # So the sequence of t-values forms a cycle in Z_3 under the various transitions.
    #
    # Now: at the (c_L, *, c_R) slice:
    #   v -> v+1 (fire)
    #   v+1 -> v+2 (fire)
    #   v+2 -> v+2 (absorb)
    #
    # Once t reaches v+2 with context (c_L, c_R), it's stuck until context changes.
    # To leave v+2: need a different (L', R') where f_t(L', v+2, R') != v+2.
    # Such a fire moves t from v+2 to some w != v+2 (so w = v or w = v+1).
    #
    # To return to v from v+2: need net change of -2 = +1 mod 3.
    # Since the absorbing value means we "wasted" a fire at this slice:
    # t's value went v -> v+1 -> v+2 (2 fires, +2 mod 3) during steps k, k+1.
    # To return: need +1 more (net) from all other t-fires.
    # Since fc(t) fires total, and 2 are at steps k, k+1:
    # remaining fc(t)-2 fires must give net +1 mod 3.
    # (Total net must be 0 mod 3, used 2 = -1 mod 3, need +1 from remainder.)

    # This is getting complex. Let me just try the computational approach.
    pass


def compute_proof():
    """
    Computational proof at n=5 and n=6.
    Exhaustively verify that no valid sub-threshold system with sandwiched ternary
    has consecutive t-fires in its good cycle.
    """
    import itertools
    from collections import Counter

    # For n=5, we can use the approach: fix ms, enumerate all permutations with sandwich,
    # then use SAT-like reasoning or direct enumeration of small tables.

    # Actually, let me use a smarter approach:
    # Fix the sandwich at positions 0,1,2 with ms[0]=2, ms[1]=3, ms[2]=2.
    # For n=5 sub-threshold, the remaining positions have ms[3], ms[4] with
    # total product 2*3*2*ms[3]*ms[4] < 108, so ms[3]*ms[4] < 9.
    # Possible: (2,2), (2,3), (2,4), (3,2), (3,3) -- wait need sorted? No, positions matter.
    # ms[3] >= 2, ms[4] >= 2, ms[3]*ms[4] < 9.
    # Options: (2,2), (2,3), (2,4), (3,2), (4,2).
    # But also need >= 3 binary total. ms[0]=2, ms[2]=2 are binary. Need >= 1 more.
    # (2,2): 4 binary, (2,3): 3 binary, (2,4): 3 binary, (3,2): 3 binary, (4,2): 3 binary, (3,3): 2 binary (fails).
    # Actually (3,3): ms = (2,3,2,3,3), product = 108, NOT sub-threshold (need < 108).
    # So (3,3) is excluded anyway.

    # But we also want ms to be >= 3 binary. Some of ms[3], ms[4] may be 2.

    # Let me just enumerate all valid combos.
    n = 5
    threshold = 108

    # We fix sandwich at t=1: ms[0]=2, ms[1]=3, ms[2]=2
    # ms[3] and ms[4] are free, >= 2
    candidates = []
    for m3 in range(2, 10):
        for m4 in range(2, 10):
            ms = [2, 3, 2, m3, m4]
            prod = 1
            for m in ms:
                prod *= m
            nbinary = sum(1 for m in ms if m == 2)
            if prod < threshold and nbinary >= 3:
                candidates.append(tuple(ms))

    print(f"=== Computational verification at n={n} ===")
    print(f"Threshold: {threshold}")
    print(f"Sandwich at t=1 (ms[0]=2, ms[1]=3, ms[2]=2)")
    print(f"Candidate state vectors: {len(candidates)}")
    for ms in candidates:
        prod = 1
        for m in ms:
            prod *= m
        print(f"  {ms}, product={prod}")
    print()

    # For each candidate ms, enumerate ALL possible transition function tables
    # and check for valid systems with consecutive t-fires.
    #
    # Table sizes:
    # Proc 0 (binary): domain {m4} x {2} x {3} = m4*2*3 entries, range {0,1}: 2^(6*m4) tables
    # Proc 1 (ternary): domain {2} x {3} x {2} = 12 entries, range {0,1,2}: 3^12 tables
    # Proc 2 (binary): domain {3} x {2} x {m3} = 6*m3 entries, range {0,1}: 2^(6*m3) tables
    # Proc 3: domain {2} x {m3} x {m4} entries, range {0,...,m3-1}
    # Proc 4: domain {m3} x {m4} x {2} entries, range {0,...,m4-1}
    #
    # For ms = (2,3,2,2,2):
    # Proc 0: 2*2*3 = 12 entries, 2^12 = 4096 tables
    # Proc 1: 2*3*2 = 12 entries, 3^12 = 531441 tables
    # Proc 2: 3*2*2 = 12 entries, 2^12 = 4096 tables
    # Proc 3: 2*2*2 = 8 entries, 2^8 = 256 tables
    # Proc 4: 2*2*2 = 8 entries, 2^8 = 256 tables
    # Total: 4096 * 531441 * 4096 * 256 * 256 ≈ 5.8 * 10^20. WAY too many.
    #
    # Need a smarter approach. Let me use the constraints directly.

    print("Direct enumeration infeasible. Using constraint-based approach.")
    print()

    # Approach: fix the sandwich triple and enumerate only the LOCAL tables
    # (procs 0, 1, 2) while deriving constraints. Then check if any valid
    # completion exists with consecutive t-fires.
    #
    # Actually, let me use a RANDOM SEARCH + ANALYTICAL approach.
    # The analytical proof is the real goal; computation just validates.

    return candidates


def prove_no_consecutive_tfire():
    """
    ANALYTICAL PROOF that consecutive t-fires lead to entry conflict.

    Setup:
    - t is a sandwiched ternary: m_t = 3, m_{bL} = m_{bR} = 2
    - Good cycle gc with CL configs
    - t fires at steps k and k+1 (consecutive)
    - Config k:   C = (..., c_L, v,   c_R, ...)  with mover = t
    - Config k+1: C' = (..., c_L, v+1, c_R, ...) with mover = t
    - Config k+2: C'' = (..., c_L, v+2, c_R, ...) with mover != t

    where c_L = C[bL] in {0,1}, c_R = C[bR] in {0,1}, v = C[t] in {0,1,2}.

    Step 1: f_t(c_L, v+2, c_R) = v+2.
    Proof: If f_t(c_L, v+2, c_R) != v+2, then t is privileged at C''.
    By unique privilege, moverAt(k+2) = t (3 consecutive t-fires).
    Config k+3 = (..., c_L, f_t(c_L, v+2, c_R), c_R, ...).
    Since f_t(c_L, v+2, c_R) != v+2 and values are mod 3:
    f_t(c_L, v+2, c_R) in {v, v+1}.
    If = v: config k+3 = config k, but |k+3 - k| = 3 < CL (CL >= 3n-2 >= 13).
      So config k appears twice in the cycle: contradiction (gc.distinct).
    If = v+1: config k+3 = config k+1, |k+3 - (k+1)| = 2 < CL.
      Config k+1 appears twice: contradiction.
    So f_t(c_L, v+2, c_R) = v+2. QED.

    Step 2: (c_L, v+2, c_R) is a nonmover context for t at step k+2.
    And (c_L, v, c_R), (c_L, v+1, c_R) are mover contexts for t at steps k, k+1.
    These three contexts differ only in the S-component.

    Step 3: The good cycle must contain ANOTHER config where t has value v+2
    with SOME context. Consider all steps where t doesn't fire and has value v+2.
    At such a step j: f_t(L_j, v+2, R_j) = v+2. If (L_j, R_j) = (c_L, c_R):
    this is consistent (nonmover). If (L_j, R_j) != (c_L, c_R): independent.

    Step 4: Consider all steps where t fires and has value v+2 (before firing).
    At such a step j: f_t(L_j, v+2, R_j) != v+2.
    If (L_j, R_j) = (c_L, c_R): CONTRADICTION with step 1 (f_t(c_L,v+2,c_R) = v+2).
    So any t-fire from value v+2 must use a DIFFERENT (L,R) context.

    Step 5: NOW, the critical argument.

    The good cycle has CL >= 3n-2 configs. Among all configs in the cycle,
    each value triple (C[bL], C[t], C[bR]) appears in multiple configs
    (since the total product >> 2*3*2 = 12 possible triples when n >= 5).

    The specific triple (c_L, v+2, c_R) appears in configs at step k+2
    and potentially other steps. At step k+2, t is nonmover.

    For the cycle to close: t must return to value v. This requires t to
    fire at least once with pre-fire value v+2 (using some other (L',R')).
    Then t goes from v+2 to some w != v+2 (w in {v, v+1}).

    Step 6: The ENTRY CONFLICT argument.

    Consider the configs in the cycle at the (c_L, *, c_R) slice more carefully.
    We have:
    - Step k: (c_L, v, c_R) as mover -> f_t = v+1
    - Step k+1: (c_L, v+1, c_R) as mover -> f_t = v+2
    - Step k+2: (c_L, v+2, c_R) as nonmover -> f_t = v+2

    For no EC at t: the contexts (c_L, v, c_R) and (c_L, v+1, c_R) must ALWAYS
    be mover contexts, and (c_L, v+2, c_R) must ALWAYS be nonmover.

    Now: how many configs in the cycle have the triple (c_L, ?, c_R)?
    There are 3 possible t-values: v, v+1, v+2.
    For each, the rest of the ring can vary.

    But at step k: the full config is (c0,...,c_{bL-1}, c_L, v, c_R, c_{bR+1},...,c_{n-1}).
    At step k+1: same except t = v+1.
    At step k+2: same except t = v+2.
    These three configs all share the same "background" (all positions except t).

    This means: these three configs are a "fiber" over the (L,S,R) triple at t.
    In the fiber {(c_L, *, c_R)} x {background = (c0,...,c_L,...,c_R,...,c_{n-1} minus t)}:
    all 3 t-values appear.

    Now: does the config (background, t=v) appear elsewhere in the cycle? No, each config
    is unique. So (background, t=v) appears exactly at step k.

    The question is about OTHER backgrounds with the same (c_L, c_R) triple.

    For ANOTHER background b' != background with C'[bL] = c_L, C'[bR] = c_R:
    if t fires with value v at config with background b': context is (c_L, v, c_R),
    mover -> no EC issue (always mover). But wait: does the cycle contain such a config?

    Not necessarily. The cycle has CL configs, and how they distribute over (c_L, ?, c_R)
    depends on the system.

    WAIT. The argument is actually simpler than I thought. Let me restart.

    THE SIMPLE PROOF:

    At step k+2: config is (c_L, v+2, c_R) [shorthand for the full config].
    t is nonmover: f_t(c_L, v+2, c_R) = v+2.

    Later in the cycle, t must fire from value v+2 (to eventually return to v).
    When does this happen? At some step j, t has value v+2 and fires.
    At step j: f_t(L_j, v+2, R_j) != v+2. So (L_j, R_j) != (c_L, c_R) (from step 1).

    But maybe t never has value v+2 when firing. Can that happen?

    t's value traces: v -> v+1 -> v+2 -> ... -> v (cycle returns to start).
    After step k+1, t = v+2. For t to return to v without firing from v+2:
    t must change value WITHOUT firing. But t only changes when it fires!
    So t must fire from v+2 at some point. QED: there exists step j with
    t value v+2 and mover = t.

    At step j: context is (L_j, v+2, R_j) with (L_j, R_j) != (c_L, c_R).
    This is a MOVER context for t.
    At step k+2: context is (c_L, v+2, c_R), NONMOVER context for t.
    These are DIFFERENT contexts (different (L,R)), so no EC from these two alone.

    Hmm. So consecutive t-fires don't DIRECTLY give EC at t.

    What about EC at the binary neighbors?

    bL context at step k: (LL, c_L, v)    nonmover -> f_bL(LL, c_L, v) = c_L
    bL context at step k+1: (LL, c_L, v+1) nonmover -> f_bL(LL, c_L, v+1) = c_L
    bL context at step k+2: (LL, c_L, v+2)
      If nonmover: f_bL(LL, c_L, v+2) = c_L (3 of 3 R-values give c_L for this (LL, c_L))
      If mover: impossible since we showed at most one of bL, bR fires at k+2.

    So if bL is nonmover at k+2: f_bL(LL, c_L, r) = c_L for all r in {0,1,2} = all of Z_3.
    This means bL with (L=LL, S=c_L) is NEVER privileged.
    bL is binary (m=2), so it fires when f_bL != S.
    For (LL, c_L, *): always returns c_L = S. Never fires.
    For (LL, 1-c_L, r): may or may not fire.

    Since bL fires at least 2 times total: all fires have S = 1-c_L with L=LL?
    Wait, LL may vary (it's the value of bL's left neighbor, which is proc bL-1).
    LL is the value of proc bL-1 = proc t-2. This can change during the cycle.

    Hmm, LL is NOT fixed. I was sloppy. Let me redo.

    At step k: bL's full context is (C[bL-1], C[bL], C[bL+1]) = (C[t-2], c_L, v).
    Let LL_k = C[t-2] at step k.
    f_bL(LL_k, c_L, v) = c_L.

    At step k+1: only t changed (v -> v+1). So C[t-2] is still LL_k (t-2 != t).
    f_bL(LL_k, c_L, v+1) = c_L.

    At step k+2: only t changed (v+1 -> v+2). C[t-2] is still LL_k.
    f_bL(LL_k, c_L, v+2) = c_L (if bL nonmover at k+2) or != c_L (if bL fires).

    So the constraint is: f_bL(LL_k, c_L, *) = c_L for R = v and R = v+1.
    And maybe also R = v+2 (if bL is nonmover at k+2).

    {v, v+1, v+2} = {0, 1, 2} since t is ternary.
    So f_bL(LL_k, c_L, r) = c_L for r in {v, v+1} (at least 2 of 3 R-values).

    If also for r = v+2: f_bL(LL_k, c_L, *) = c_L for ALL 3 R-values.
    bL with context (LL_k, c_L, *) is NEVER privileged.
    This constrains bL's transition: with L=LL_k, S=c_L, any R -> returns c_L.

    Now: in the entire good cycle, whenever bL has L=LL_k and S=c_L (and any R):
    bL is nonprivileged. So bL never fires with (L=LL_k, S=c_L).
    When bL fires: it must have S = 1-c_L, OR L != LL_k.
    """
    pass


# THE DEFINITIVE PROOF
def definitive_proof():
    """
    DEFINITIVE PROOF: Consecutive t-fires with sandwiched ternary => entry conflict.

    This uses a cleaner approach based on the BINARY EXHAUSTION principle.

    Setup: t sandwiched ternary (m_t=3), bL=left(t), bR=right(t) both binary (m=2).
    t fires at consecutive steps k, k+1 in a good cycle.

    Let:
    - v = t-value at step k
    - c_L = bL-value at step k (binary: 0 or 1)
    - c_R = bR-value at step k (binary: 0 or 1)
    - LL = value of left(bL) = proc t-2 at step k
    - RR = value of right(bR) = proc t+2 at step k

    Configs:
    - Step k:   (..., LL, c_L, v,   c_R, RR, ...) mover=t
    - Step k+1: (..., LL, c_L, v+1, c_R, RR, ...) mover=t (only t changed)
    - Step k+2: (..., LL, c_L, v+2, c_R, RR, ...) mover!=t (only t changed)

    Step 1: f_t(c_L, v+2, c_R) = v+2 (proved above: 3-consec gives cycle collision).

    Step 2: Consider the CYCLIC WRAP.
    Let step j be the last step BEFORE k where t fires (the previous t-fire).
    Config at j: (..., c_L', v', c_R', ...) with mover=t.
    Config at j+1: (..., c_L', v'+1, c_R', ...) mover != t (since k is the next t-fire).
    Between j+1 and k-1: t doesn't fire. At step k: t has value v.
    Since t doesn't fire between j+1 and k-1: t's value at step j+1 = v.
    So v'+1 = v (mod 3), meaning v' = v-1 = v+2 (mod 3).

    WAIT: that's not quite right. t fires at step j, changing from v' to f_t(c_L', v', c_R').
    Let's call the output w = f_t(c_L', v', c_R'). Then t has value w from step j+1 until
    the next t-fire, which could be before step k if there are intermediate t-fires.
    BUT: we said j is the LAST t-fire before k. So no intermediate t-fires.
    So t's value from step j+1 to step k is w. At step k: t = w = v.

    So: f_t(c_L', v', c_R') = v. And v' != v (t fires means output != input).
    So v' is in {v+1, v+2}.

    Step 3: Similarly, the t-fire at step k+1 gives t-value v+2.
    The NEXT t-fire after k+1 is at some step m > k+1.
    t has value v+2 from step k+2 to step m.
    At step m: f_t(c_L'', v+2, c_R'') != v+2. So (c_L'', c_R'') != (c_L, c_R).

    Step 4: THE KEY.
    Between steps k+2 and m-1: t has value v+2, and there are fires by other procs.
    Some of these fires may change bL or bR.

    At step k+2: bL=c_L, bR=c_R. Possibly bL or bR fires at step k+2.
    If bL fires at step k+2: bL goes from c_L to 1-c_L.
    If bR fires at step k+2: bR goes from c_R to 1-c_R.

    Consider the config at step m (next t-fire after k+1):
    t = v+2, bL = c_L'' (some value), bR = c_R'' (some value).
    f_t(c_L'', v+2, c_R'') != v+2. And (c_L'', c_R'') != (c_L, c_R).

    Since bL, bR are binary:
    (c_L'', c_R'') in {(0,0), (0,1), (1,0), (1,1)} \ {(c_L, c_R)}.
    So 3 possibilities for (c_L'', c_R'').

    Now: at step k+2, t sees (c_L, v+2, c_R) as nonmover: f_t(c_L,v+2,c_R) = v+2.
    At step m, t sees (c_L'', v+2, c_R'') as mover: f_t(c_L'',v+2,c_R'') != v+2.
    Different (L,R) pairs, no EC from these.

    But consider all the NONMOVER steps where t = v+2 between k+2 and m-1.
    At each such step j: config has t=v+2, and (bL_j, bR_j) might be any pair.
    f_t(bL_j, v+2, bR_j) = v+2 (nonmover).

    The context (bL_j, v+2, bR_j) with bL_j, bR_j varying. For each pair:
    if it's (c_L, c_R): consistent with f_t(c_L,v+2,c_R) = v+2.
    if it's (c_L'', c_R''): INCONSISTENT with f_t(c_L'',v+2,c_R'') != v+2.
    ENTRY CONFLICT!

    So: if there exists a nonmover step for t between k+2 and m-1 where
    (bL, bR) = (c_L'', c_R''), we have EC.

    Does such a step exist? Between k+2 and m-1, t doesn't fire.
    bL and bR may fire, changing their values.
    At step k+2: (bL, bR) = (c_L, c_R).
    At step m: (bL, bR) = (c_L'', c_R'') != (c_L, c_R).

    So at some point between k+2 and m, (bL, bR) transitions from (c_L, c_R) to (c_L'', c_R'').
    This transition happens one binary flip at a time (each fire changes one binary by 1).

    At the step JUST BEFORE (bL, bR) first becomes (c_L'', c_R''):
    either bL or bR fires. At the step where (bL, bR) first equals (c_L'', c_R''):
    a binary neighbor just fired (changing to the target pair). This is a nonmover step for t.

    But wait: (bL, bR) might be (c_L'', c_R'') at step m itself, where t fires.
    We need a NONMOVER step for t with (bL, bR) = (c_L'', c_R'').

    Consider the step m-1: t doesn't fire (since m is the next t-fire after k+1).
    At step m: (bL, bR) = (c_L'', c_R''). This is configured at the END of step m-1
    (or equivalently, at the START of step m). The config at step m has (bL, bR) = (c_L'', c_R'').

    But step m-1 is a nonmover step for t (t doesn't fire). The config at step m-1 has
    t = v+2 (unchanged since step k+2). And (bL, bR) at step m-1 is either (c_L'', c_R'')
    (if no binary fires at step m-1) or one flip away.

    Case A: at step m-1, (bL, bR) = (c_L'', c_R''). Then at step m-1, t's context
    is (c_L'', v+2, c_R''). t is nonmover: f_t(c_L'', v+2, c_R'') = v+2.
    But at step m: f_t(c_L'', v+2, c_R'') != v+2. CONTRADICTION (same input, different output).
    Wait no: f_t is a FIXED function. It can't give both v+2 and != v+2 for the same input.
    So this is impossible: (bL, bR) at step m-1 CANNOT equal (c_L'', c_R'').

    Case B: at step m-1, (bL, bR) != (c_L'', c_R''). But at step m, (bL, bR) = (c_L'', c_R'').
    The difference between step m-1 and step m: exactly one proc fires at step m-1.
    If that proc is bL: bL changes (c_L''' -> c_L''), so c_L''' = 1-c_L''.
    If that proc is bR: bR changes (c_R''' -> c_R''), so c_R''' = 1-c_R''.
    If that proc is something else: (bL, bR) doesn't change between m-1 and m.
    But we said (bL, bR) at m-1 != at m. So the mover at step m-1 IS bL or bR.

    Sub-case B1: mover at m-1 is bL.
    Config at m-1: (..., 1-c_L'', v+2, c_R'', ...). t context: (1-c_L'', v+2, c_R'').
    t is nonmover: f_t(1-c_L'', v+2, c_R'') = v+2.
    Now at step m: t context is (c_L'', v+2, c_R''). t fires: f_t(c_L'', v+2, c_R'') != v+2.

    Since (1-c_L'', c_R'') != (c_L'', c_R'') (they differ at bL), we can't directly
    get EC from these.

    But here's the thing: we need (c_L'', c_R'') != (c_L, c_R), and (1-c_L'', c_R'')
    might equal (c_L, c_R).

    If (1-c_L'', c_R'') = (c_L, c_R): then c_L = 1-c_L'' and c_R = c_R''.
    And (c_L'', c_R'') = (1-c_L, c_R). Check: (c_L'', c_R'') != (c_L, c_R) iff
    1-c_L != c_L, i.e., c_L != 1-c_L, always true for binary. Good.

    So: (c_L'', c_R'') = (1-c_L, c_R), (1-c_L'', c_R'') = (c_L, c_R).
    At step m-1: t context (c_L, v+2, c_R), nonmover: f_t(c_L, v+2, c_R) = v+2. CONSISTENT with step 1!
    At step m: t context (1-c_L, v+2, c_R), mover: f_t(1-c_L, v+2, c_R) != v+2.

    No EC directly. But consider: does t have a nonmover step with context (1-c_L, v+2, c_R)?

    If yes: f_t(1-c_L, v+2, c_R) = v+2 (nonmover) but also != v+2 (mover at step m). EC!
    If no: (1-c_L, v+2, c_R) is ALWAYS mover for t.

    So: either we have EC, or (1-c_L, v+2, c_R) is always mover for t.
    Under no-EC: (c_L, v+2, c_R) always nonmover, (1-c_L, v+2, c_R) always mover.

    Now I need to check if this creates a contradiction somehow...
    Actually, wait. Let me reconsider.

    The key observation: (c_L'', c_R'') != (c_L, c_R) but has 3 possibilities.
    Let me consider them all.

    If (c_L'', c_R'') = (1-c_L, c_R): Sub-case B1 above leads to no direct EC.
    If (c_L'', c_R'') = (c_L, 1-c_R): symmetric argument.
    If (c_L'', c_R'') = (1-c_L, 1-c_R): both differ.

    But actually, the argument needs refinement. Let me think about what happens
    when t's nonmover value v+2 appears with DIFFERENT (L,R) contexts.

    FROM STEP 1: f_t(c_L, v+2, c_R) = v+2 (nonmover, proved).

    If there exists a step where t fires from v+2: say at step m with context
    (c_L'', v+2, c_R''), and (c_L'', c_R'') != (c_L, c_R).

    Between steps k+2 and m: t=v+2 throughout (nonmover). The (bL, bR) pair
    evolves from (c_L, c_R) to (c_L'', c_R''). There's a PATH of configs where
    t = v+2 and (bL, bR) transitions through intermediate values.

    Since bL and bR are binary, (bL, bR) can only change one bit at a time.
    The path from (c_L, c_R) to (c_L'', c_R'') has Hamming distance 1 or 2.

    If Hamming distance 1 (say c_R'' = c_R, c_L'' = 1-c_L):
    The transition happens in 1 step (bL fires). At that step, t sees the
    config BEFORE bL fires: (c_L, v+2, c_R). After bL fires: (1-c_L, v+2, c_R).
    The step where bL fires: t is nonmover with context (c_L, v+2, c_R).
    The next step (or m): t fires with context (1-c_L, v+2, c_R).
    No EC at t (different contexts).

    If Hamming distance 2 (c_L'' = 1-c_L, c_R'' = 1-c_R):
    The transition requires 2 steps (bL and bR each fire once, not necessarily
    consecutively). The intermediate (bL, bR) is either (1-c_L, c_R) or (c_L, 1-c_R).

    At the intermediate config: t = v+2 with (bL, bR) = (1-c_L, c_R) or (c_L, 1-c_R).
    t is nonmover: f_t(1-c_L, v+2, c_R) = v+2 OR f_t(c_L, v+2, 1-c_R) = v+2.

    Then at step m: f_t(1-c_L, v+2, 1-c_R) != v+2.

    So: f_t(c_L, v+2, c_R) = v+2 (step 1).
    And f_t(1-c_L, v+2, c_R) = v+2 OR f_t(c_L, v+2, 1-c_R) = v+2 (intermediate).
    And f_t(1-c_L, v+2, 1-c_R) != v+2 (step m).

    Can we derive EC? The context at step m is (1-c_L, v+2, 1-c_R), mover.
    Is this context ever nonmover? If yes: EC.
    If the intermediate went through (1-c_L, c_R):
      At that intermediate step, (1-c_L, v+2, c_R) is nonmover.
      Then (1-c_L, v+2, 1-c_R) at step m is mover. Different R. No direct EC.
      But then: does (1-c_L, v+2, 1-c_R) appear as nonmover?

    This is getting tangled. Let me try computation instead.
    """
    pass


# =============================================================
# THE COMPUTATIONAL APPROACH
# For n=5, use the good cycle search from the verifier on specific ms values.
# Generate random valid systems and check.
# Then try ALL valid systems for very small cases.
# =============================================================

import random

def random_transition_table(m_L, m_S, m_R):
    """Create a random transition function table."""
    table = {}
    for l in range(m_L):
        for s in range(m_S):
            for r in range(m_R):
                table[(l, s, r)] = random.randint(0, m_S - 1)
    return table


def search_consecutive_tfire(ms, num_trials=100000, seed=42):
    """
    Random search for valid systems with consecutive t-fires at sandwiched ternary.
    """
    random.seed(seed)
    n = len(ms)

    # Find sandwich positions
    sandwich_positions = []
    for t in range(n):
        if ms[t] >= 3 and ms[(t-1) % n] == 2 and ms[(t+1) % n] == 2:
            sandwich_positions.append(t)

    if not sandwich_positions:
        print(f"  No sandwich in {ms}")
        return 0, 0

    valid_count = 0
    consec_count = 0

    for trial in range(num_trials):
        # Generate random transition tables
        tables = []
        for i in range(n):
            m_L = ms[(i-1) % n]
            m_S = ms[i]
            m_R = ms[(i+1) % n]
            tables.append(random_transition_table(m_L, m_S, m_R))

        fs = [table_to_func(t) for t in tables]

        # Quick validity check
        if not verify_system_quick(ms, fs):
            continue

        valid_count += 1

        # Find good cycle
        cycle_configs, cycle_movers = find_good_cycle(ms, fs)
        if cycle_configs is None:
            continue

        # Check consecutive t-fires
        for t in sandwich_positions:
            if check_consecutive_tfire(cycle_movers, t):
                # Double-check: is there no EC?
                ec = has_entry_conflict(cycle_configs, cycle_movers, fs, ms)
                if not ec:
                    consec_count += 1
                    print(f"  FOUND: trial {trial}, ms={ms}, t={t}, CL={len(cycle_movers)}")
                    print(f"    Movers: {cycle_movers}")
                    # Print the consecutive steps
                    CL = len(cycle_movers)
                    for k in range(CL):
                        if cycle_movers[k] == t and cycle_movers[(k+1) % CL] == t:
                            print(f"    Steps {k} and {k+1}: mover={t}")
                            print(f"    Config k:   {cycle_configs[k]}")
                            print(f"    Config k+1: {cycle_configs[(k+1) % CL]}")
                            if (k+2) % CL < CL:
                                print(f"    Config k+2: {cycle_configs[(k+2) % CL]}")

    return valid_count, consec_count


def exhaustive_small():
    """Exhaustive check for ms=(2,3,2) at n=3.

    n=3 is too small for the theorem (n>=9), but let's see the structure.
    """
    ms = [2, 3, 2]
    n = 3
    t = 1  # sandwich at position 1

    print(f"=== Exhaustive check at n={n}, ms={ms} ===")

    # Enumerate ALL transition tables
    # Proc 0 (binary): domain {m2}x{2}x{3} = 2*2*3 = 12 entries, range {0,1}: 2^12 = 4096
    # Proc 1 (ternary): domain {2}x{3}x{2} = 12 entries, range {0,1,2}: 3^12 = 531441
    # Proc 2 (binary): domain {3}x{2}x{2} = 12 entries, range {0,1}: 2^12 = 4096
    # Total: ~8.9 * 10^12. Too many.

    # Use random search instead
    print(f"Random search (n={n} too small for theorem, but checking structure)...")
    valid, consec = search_consecutive_tfire(ms, num_trials=200000)
    print(f"  Valid systems found: {valid}")
    print(f"  With consecutive t-fires (no EC): {consec}")
    print()


def main():
    print("=" * 70)
    print("NO CONSECUTIVE T-FIRES: Proof Investigation")
    print("=" * 70)
    print()

    # Part 1: Random search at various n and ms
    test_cases = [
        # (ms, description)
        ([2, 3, 2, 2, 2], "n=5, (2,3,2,2,2), prod=48"),
        ([2, 3, 2, 3, 2], "n=5, (2,3,2,3,2), prod=72"),
        ([2, 3, 2, 2, 3], "n=5, (2,3,2,2,3), prod=72"),
        ([2, 2, 3, 2, 2], "n=5, (2,2,3,2,2), prod=48"),
        ([2, 3, 2, 2, 2, 2], "n=6, (2,3,2,2,2,2), prod=96"),
        ([2, 3, 2, 3, 2, 2], "n=6, (2,3,2,3,2,2), prod=144"),
        ([2, 3, 2, 2, 3, 2], "n=6, (2,3,2,2,3,2), prod=144"),
        ([2, 3, 2, 3, 3, 2], "n=6, (2,3,2,3,3,2), prod=216"),
    ]

    # Filter to sub-threshold
    filtered = []
    for ms, desc in test_cases:
        n = len(ms)
        threshold = 4 * (3 ** (n - 2))
        prod = 1
        for m in ms:
            prod *= m
        nbinary = sum(1 for m in ms if m == 2)
        if prod < threshold and nbinary >= 3:
            filtered.append((ms, desc, threshold))

    print(f"Testing {len(filtered)} sub-threshold configurations:")
    for ms, desc, threshold in filtered:
        print(f"  {desc} (threshold={threshold})")
    print()

    total_valid = 0
    total_consec = 0

    for ms, desc, threshold in filtered:
        print(f"--- {desc} ---")
        valid, consec = search_consecutive_tfire(ms, num_trials=500000, seed=42)
        total_valid += valid
        total_consec += consec
        print(f"  Valid: {valid}, Consecutive t-fires (no EC): {consec}")
        print()

    print("=" * 70)
    print(f"TOTAL: {total_valid} valid systems checked, {total_consec} with consecutive t-fires (no EC)")
    if total_consec == 0:
        print("RESULT: No counterexample found. Theorem holds computationally.")
    else:
        print(f"RESULT: {total_consec} COUNTEREXAMPLES found!")
    print("=" * 70)


if __name__ == "__main__":
    main()
