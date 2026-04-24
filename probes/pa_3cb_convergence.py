#!/usr/bin/env python3
"""PA: 3CB Convergence Failure Investigation.

Investigate WHY 3 consecutive binary processors (3CB) at sub-threshold product
forces recurrent bad SCCs to exist, preventing convergence.

Key question: What structural feature makes n>=8 impossible while n<=7 works?

APPROACH:
1. For proc 1 (middle binary, both neighbors binary), enumerate all 16 possible
   privilege sets M (subsets of {0,1}^3 with toggle pairing constraint).
2. Count configs where proc 1 is privileged vs. total configs.
3. Analyze the "privilege persistence" mechanism: when far procs fire, proc 1's
   context is unchanged, so its privilege persists.
4. Show that the ratio of bad-with-proc1-privileged configs to good configs
   forces bad SCCs.
"""

import itertools
from collections import defaultdict, deque
from math import prod

# ============================================================
# SECTION 1: Proc 1 privilege set enumeration
# ============================================================

def enumerate_proc1_privilege_sets():
    """Enumerate all valid privilege sets M for proc 1 (middle binary).

    Context space: {0,1}^3 = 8 triples (L,S,R) where L=c[0], S=c[1], R=c[2].
    Toggle constraint: (a,b,c) in M implies (a,1-b,c) NOT in M.
    (Because if (a,b,c) is privileged, then f(a,b,c) != b, so f(a,b,c) = 1-b.
    Then for (a,1-b,c): f(a,1-b,c) could be b (privileged) or 1-b (not privileged).
    Wait - there's no constraint that forces the toggle pair to be non-privileged.
    Actually for binary S, f maps {0,1} -> {0,1}, so f(a,b,c) is either b (not priv)
    or 1-b (priv). So we just need a consistent f: for each (a,c) pair,
    f(a,0,c) and f(a,1,c) are independently chosen from {0,1}.)

    Actually, the toggle constraint says: if (a,0,c) in M then f(a,0,c)=1,
    if (a,1,c) in M then f(a,1,c)=0. Both can be in M simultaneously
    (meaning f(a,0,c)=1 AND f(a,1,c)=0, i.e., f always outputs 1-S for this (a,c)).

    For each (a,c) pair, there are 4 possibilities:
    - Neither (a,0,c) nor (a,1,c) in M: f(a,0,c)=0, f(a,1,c)=1 (identity)
    - Only (a,0,c) in M: f(a,0,c)=1, f(a,1,c)=1 (always output 1)
    - Only (a,1,c) in M: f(a,0,c)=0, f(a,1,c)=0 (always output 0)
    - Both in M: f(a,0,c)=1, f(a,1,c)=0 (toggle/complement)

    So there are 4^4 = 256 possible transition functions for proc 1,
    giving 256 possible privilege sets.

    Wait, but we need to be more careful. The 4 (a,c) pairs for binary neighbors
    are: (0,0), (0,1), (1,0), (1,1). For each, 4 choices. Total: 4^4 = 256.
    """
    contexts = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]
    ac_pairs = [(0,0), (0,1), (1,0), (1,1)]

    results = []
    for choices in itertools.product(range(4), repeat=4):
        # choices[i] for ac_pairs[i]:
        # 0: neither, 1: only (a,0,c), 2: only (a,1,c), 3: both
        M = set()
        f_table = {}
        for idx, (a, c) in enumerate(ac_pairs):
            ch = choices[idx]
            if ch == 0:  # identity
                f_table[(a, 0, c)] = 0
                f_table[(a, 1, c)] = 1
            elif ch == 1:  # always 1
                f_table[(a, 0, c)] = 1
                f_table[(a, 1, c)] = 1
                M.add((a, 0, c))
            elif ch == 2:  # always 0
                f_table[(a, 0, c)] = 0
                f_table[(a, 1, c)] = 0
                M.add((a, 1, c))
            else:  # toggle
                f_table[(a, 0, c)] = 1
                f_table[(a, 1, c)] = 0
                M.add((a, 0, c))
                M.add((a, 1, c))
        results.append((frozenset(M), f_table, choices))

    return results

# ============================================================
# SECTION 2: Counting argument
# ============================================================

def analyze_3cb_counting(n, ms=None):
    """Analyze the counting argument for 3CB at given n.

    3CB at positions {0,1,2}: m_0=m_1=m_2=2.
    Remaining positions: m_j for j=3..n-1.

    For sub-threshold: product(m_i) < 4*3^(n-2).
    """
    if ms is None:
        # Default sub-threshold: (2,2,2,3,...,3) with minimal non-binary
        ms = [2, 2, 2] + [3] * (n - 3)

    P_total = prod(ms)
    P_rest = prod(ms[3:])  # product of non-{0,1,2} state counts
    threshold = 4 * 3**(n-2)

    print(f"\n{'='*60}")
    print(f"n={n}, ms={ms}")
    print(f"P_total = {P_total}, threshold = {threshold}")
    print(f"P_rest = {P_rest}")
    print(f"Sub-threshold: {P_total < threshold} (ratio: {P_total/threshold:.4f})")
    print(f"{'='*60}")

    # For each possible privilege set M of proc 1:
    priv_sets = enumerate_proc1_privilege_sets()

    # Group by |M|
    by_size = defaultdict(list)
    for M, f_table, choices in priv_sets:
        by_size[len(M)].append((M, f_table, choices))

    print(f"\nPrivilege set sizes: {dict((k, len(v)) for k, v in sorted(by_size.items()))}")

    # For each |M|, compute:
    # - Total configs where proc 1 is privileged: |M| * P_rest
    #   (for each context (a,b,c) in M, there are P_rest assignments to procs 3..n-1)
    # - Maximum good configs where proc 1 fires: |M| * P_rest
    #   (but only those where proc 1 is the UNIQUE privileged proc)
    # - In a good cycle, proc 1 fires exactly m_1 = 2 times per cycle.
    #   So at most 2 good configs have proc 1 privileged.

    # Wait -- that's not quite right. In the good cycle, every proc fires
    # at least m_i times (specifically, exactly m_i times in a minimal cycle
    # of length sum(m_i)). For proc 1 binary: fires exactly 2 times.

    # So there are exactly 2 good configs where proc 1 is privileged.
    # But |M| * P_rest configs total have proc 1 privileged.
    # The remaining |M| * P_rest - 2 have proc 1 privileged AND are bad.

    # Actually: the good cycle has L = sum(ms) - n configs? No.
    # In a valid system, the good cycle has some length L.
    # Each proc fires exactly m_i times. So L = sum of fire counts.
    # But fire count for proc i must be a multiple of m_i (to return to start).
    # Minimum: each fires m_i times. So L >= sum(m_i).
    # Actually L = sum(m_i) for a minimal good cycle? Not necessarily.
    # The cycle length = number of distinct good configs.

    # Let's just compute the expected good cycle length from CUP-2 data:
    # For CUP-2 with ms=(2,3,...,3,2): L = 3n-2, good = (n+2)(n+3)/2 - 5
    # For general ms=(2,2,2,3,...,3): L = 3(n-3) + 3*2 = 3n-3?
    # Actually, for the good cycle each proc fires m_i times, so the cycle
    # visits sum(m_i) configs where exactly one proc is privileged.
    # But the cycle length could be different from sum(m_i) since
    # after firing, the config must have exactly one new privileged proc.

    # For our counting: the key point is that the number of good configs
    # where proc 1 is privileged = (number of times proc 1 fires in good cycle)
    # = some multiple of m_1 = 2. At minimum, exactly 2.

    # Configs where proc 1 is privileged:
    for M_size in sorted(by_size.keys()):
        if M_size == 0:
            continue
        proc1_priv_total = M_size * P_rest
        proc1_priv_good = 2  # minimum: fires m_1 = 2 times
        proc1_priv_bad = proc1_priv_total - proc1_priv_good

        # Total configs
        total_configs = P_total

        print(f"\n|M|={M_size}:")
        print(f"  Configs where proc 1 is privileged: {proc1_priv_total}")
        print(f"  Good configs with proc 1 firing: {proc1_priv_good}")
        print(f"  BAD configs with proc 1 privileged: {proc1_priv_bad}")
        print(f"  Ratio bad_priv/total: {proc1_priv_bad/total_configs:.4f}")
        print(f"  Ratio bad_priv/P_rest: {proc1_priv_bad/P_rest:.2f}")

    return P_total, P_rest, threshold


def privilege_persistence_analysis(n, ms=None):
    """Analyze privilege persistence: how many procs are 'far' from proc 1.

    When a far proc fires, proc 1's context (c[0], c[1], c[2]) is unchanged.
    So proc 1's privilege status is unchanged.

    'Far' procs: those at distance >= 2 from {0,1,2} on the ring.
    Proc j is far if j not in {0,1,2} AND j not in {n-1} (neighbor of 0)
    AND j not in {3} (neighbor of 2).
    Wait: proc n-1's state affects proc 0's context (as left neighbor).
    Proc 3's state affects proc 2's context (as right neighbor).
    But proc 1's context is (c[0], c[1], c[2]), and only procs 0, 1, 2 affect it.

    So ANY proc j >= 3 (and j <= n-1) can fire without changing proc 1's context!
    That's n-3 procs.

    For procs 0 and 2: firing changes c[0] or c[2], which is in proc 1's context.
    For proc 1: firing changes c[1], which is in proc 1's context.
    """
    if ms is None:
        ms = [2, 2, 2] + [3] * (n - 3)

    far_procs = list(range(3, n))  # procs whose fire doesn't change proc 1's context
    near_procs = [0, 2]  # firing these changes proc 1's L or R

    print(f"\nn={n}: {len(far_procs)} far procs ({far_procs}), {len(near_procs)} near ({near_procs})")
    print(f"  When a far proc fires, proc 1's privilege status is INVARIANT.")
    print(f"  Far procs control {prod(ms[j] for j in far_procs)} state combinations.")
    print(f"  These {prod(ms[j] for j in far_procs)} configs can 'cycle' among themselves")
    print(f"  while proc 1 stays stuck privileged.")

    # Key insight: if we fix c[0], c[1], c[2] to some (a,b,c) in M,
    # the far procs have P_rest = prod(ms[3:]) states among them.
    # Of these, only 2/|M| have proc 1 as the UNIQUE privileged proc (good configs).
    # The rest have proc 1 privileged AND at least one far proc also privileged.

    # Wait -- having proc 1 privileged doesn't mean some far proc is also privileged.
    # A config could have proc 1 privileged and NO other proc privileged: impossible!
    # If proc 1 is the only privileged proc, that's a good config.
    # If it's bad, then either 0 procs privileged (impossible by liveness) or 2+.
    # But a config where only proc 1 is privileged IS a good config (1 privileged).
    # So "proc 1 privileged and bad" means "proc 1 privileged AND at least 1 other
    # proc also privileged" (2+ total privileged).

    # How many of the |M|*P_rest configs have proc 1 as unique privileged?
    # That depends on the far procs' transition functions.
    # For each fixed (a,b,c) in M and each assignment to procs 3..n-1:
    #   - Proc 0 is privileged iff f_0(c[n-1], c[0], c[1]) != c[0]
    #     But c[n-1] depends on the far procs' states. Complex dependency.
    #   - Proc 2 is privileged iff f_2(c[1], c[2], c[3]) != c[2]
    #     c[3] is a far proc state.
    #   - For each far proc j: f_j(c[j-1], c[j], c[j+1]) != c[j]

    # The critical question: can we always arrange transitions so that
    # in EVERY config where proc 1 is privileged, at most 1 total is privileged?
    # If not, we get bad configs with proc 1 privileged.

    return far_procs, near_procs


# ============================================================
# SECTION 3: Full system construction + verification (small n)
# ============================================================

def build_and_verify_3cb(n, ms=None, verbose=False):
    """Try ALL possible transition functions for 3CB at given n.
    Count how many produce valid systems (no bad SCCs).

    Only feasible for small n (n=4,5 with limited state counts).
    """
    if ms is None:
        ms = [2, 2, 2] + [3] * (n - 3)

    P_total = prod(ms)
    if P_total > 500:
        print(f"n={n}, P_total={P_total}: too large for exhaustive search")
        return None

    print(f"\nn={n}, ms={ms}, P_total={P_total}")
    print(f"Exhaustive system construction...")

    # Generate all configs
    configs = list(itertools.product(*(range(m) for m in ms)))

    # For each proc, enumerate all possible transition functions
    # Proc i: f_i(L,S,R) -> value in range(ms[i])
    # Context space: ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
    # Number of functions: ms[i]^(context_space_size)

    context_sizes = []
    for i in range(n):
        cs = ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
        nf = ms[i] ** cs
        context_sizes.append((i, cs, nf))
        if verbose:
            print(f"  Proc {i}: context_size={cs}, #functions={nf}")

    total_systems = prod(nf for _, _, nf in context_sizes)
    print(f"  Total possible systems: {total_systems}")

    if total_systems > 10**8:
        print(f"  Too many to enumerate exhaustively")
        return None

    return context_sizes


# ============================================================
# SECTION 4: Bad SCC structure analysis (n=8 data-driven)
# ============================================================

def analyze_bad_scc_structure(n, ms=None):
    """Analyze the structure of bad SCCs for 3CB systems.

    For n=8, ms=(2,2,2,3,3,3,3,4), P_total=2592:
    - ALL 768 constructions produce 384-528 recurrent bad states
    - 0 valid systems

    We want to understand WHY: what's the mechanism?
    """
    if ms is None:
        ms = [2, 2, 2] + [3] * (n - 3)

    P_total = prod(ms)
    P_rest = prod(ms[3:])
    threshold = 4 * 3**(n-2)

    print(f"\n{'='*60}")
    print(f"BAD SCC STRUCTURE ANALYSIS")
    print(f"n={n}, ms={ms}, P_total={P_total}, threshold={threshold}")
    print(f"{'='*60}")

    # Key counting:
    # In ANY valid system, the good cycle has some length L.
    # Each proc fires at least m_i times. Sum of fires = L (each step, one fires).
    # So L >= sum(ms).
    #
    # For CUP-2: L = 3n-2. For ms=(2,3,...,3,2): sum(ms) = 2+3(n-2)+2 = 3n-2.
    # For ms=(2,2,2,3,...,3): sum(ms) = 6 + 3(n-3) = 3n-3.
    # So minimum cycle length = 3n-3 for all-ternary rest.
    # But cycle length could be longer.

    min_cycle_len = sum(ms)

    # Each proc fires exactly m_i times per cycle (minimum).
    # Proc 1 fires 2 times. In those 2 steps, proc 1 is THE unique privileged proc.

    # Now: how many configs have proc 1 privileged? |M| * P_rest.
    # But only 2 of those are good. So |M|*P_rest - 2 are bad.

    # For |M|=1: P_rest - 2 bad with proc 1 privileged.
    # For |M|=2: 2*P_rest - 2 bad with proc 1 privileged.
    # For |M|=4: 4*P_rest - 2 bad with proc 1 privileged.

    print(f"\nMin cycle length (sum ms): {min_cycle_len}")
    print(f"P_rest = {P_rest}")
    print(f"Total configs: {P_total}")

    print(f"\nConfigs where proc 1 is privileged:")
    for M_size in [1, 2, 3, 4]:
        priv1 = M_size * P_rest
        bad_priv1 = priv1 - 2
        print(f"  |M|={M_size}: {priv1} total, {bad_priv1} bad, ratio to P_total: {bad_priv1/P_total:.3f}")

    # KEY INSIGHT: Privilege persistence.
    # Fix context (a,b,c) in M. Among the P_rest configs with this context,
    # exactly 1 is good (proc 1 is unique privileged, fires in good cycle).
    # Wait -- "exactly 1" isn't right either. Among these P_rest configs,
    # the number that have proc 1 as UNIQUE privileged depends on how many
    # of the other procs are also privileged.

    # Let's think about it differently.
    # Define N_bad1(a,b,c) = #{configs with c[0]=a, c[1]=b, c[2]=c where
    #   proc 1 is privileged AND at least one other proc is too}.
    # Then: N_bad1(a,b,c) = P_rest - #{configs with c[0]=a,c[1]=b,c[2]=c where
    #   proc 1 is unique privileged}.

    # For proc 1 to be unique privileged:
    # - Proc 0 not privileged: f_0(c[n-1],a,b) == a
    # - Proc 2 not privileged: f_2(b,c,c[3]) == c
    # - For j=3..n-1: proc j not privileged: f_j(c[j-1],c[j],c[j+1]) == c[j]

    # The far procs (j>=3) are constrained: their transition at this particular
    # state must be the identity. For each far proc, the probability of this
    # (for a random transition function) is 1/m_j.

    # Expected number of "good" configs per context in M:
    # = sum over (c[3],...,c[n-1]) of Pr[proc 0 not priv] * Pr[proc 2 not priv] *
    #   prod_{j=3}^{n-1} Pr[proc j not priv]

    # This is complex. Let's think about it from the far procs' perspective.
    # Each far proc j has context (c[j-1], c[j], c[j+1]).
    # Proc j is not privileged iff f_j(c[j-1],c[j],c[j+1]) = c[j].
    # For proc j to be not privileged in ALL configs where proc 1 is privileged,
    # we need f_j to be identity on a large fraction of its context space.
    # But then proc j fires rarely, which conflicts with needing it to fire
    # m_j times in the good cycle.

    # THIS IS THE CORE TENSION!
    # The good cycle requires each proc to fire m_j times.
    # The far procs can fire without affecting proc 1's privilege.
    # But: for convergence, bad configs must drain to the good cycle.
    # If proc j has many privileged contexts, it creates many bad configs
    # where proc 1 is ALSO privileged (privilege persistence).
    # These bad configs can cycle among themselves (proc j and other far
    # procs fire back and forth while proc 1 stays stuck privileged).

    print(f"\nCORE TENSION:")
    print(f"  Good cycle requires each far proc to fire ≥ m_j times.")
    print(f"  This means each far proc has ≥ m_j privileged contexts.")
    print(f"  But these create bad configs where proc 1 is also privileged.")
    print(f"  Far proc fires don't change proc 1's context: PERSISTENCE.")

    # Quantitative: how many bad configs with proc 1 privileged?
    # Lower bound: at least |M| * P_rest - L (where L is good cycle length).
    # Because at most L good configs have proc 1 privileged.
    # Actually: proc 1 fires exactly 2 times per good cycle, so exactly 2
    # good configs have proc 1 privileged.
    # So: >= |M| * P_rest - 2 bad configs with proc 1 privileged.

    # In these bad configs, proc 1 is privileged + at least 1 other proc.
    # When a far proc fires in such a config, proc 1 stays privileged.
    # The successor config also has proc 1 privileged.
    # If the successor has another far proc privileged, we can fire that too.
    # This chain continues as long as some far proc is privileged.

    # For the chain to eventually reach a good config, proc 1 must become
    # the unique privileged proc. But proc 1's privilege doesn't change when
    # far procs fire! So the chain NEVER reaches a good config where proc 1
    # is the unique privileged proc through far proc fires alone.

    # The chain can only reach a good config where some OTHER proc is the
    # unique privileged proc. But for that, proc 1 must become NOT privileged.
    # How? Only by firing proc 0 or proc 2 (near procs) to change proc 1's context.
    # Or by firing proc 1 itself (but then proc 1 toggles, possibly becoming
    # not privileged... but the result may not be good).

    # Wait -- let's be precise. If proc 1 is privileged with context (a,b,c),
    # and we fire proc 1, the new state is (a,1-b,c). In this new config,
    # is proc 1 privileged? That depends on whether (a,1-b,c) is in M.
    # If yes: proc 1 is still privileged. If no: proc 1 is not privileged.

    # Key: the toggle pair. If both (a,0,c) and (a,1,c) are in M (toggle),
    # then firing proc 1 keeps it privileged! Bad cycle through proc 1:
    # config -> fire proc 1 -> new config -> fire proc 1 -> original config?
    # No, because other procs' states don't change. So the configs are different
    # only in c[1]. But c[1] alternates. This is a 2-cycle: bad!

    # Unless one of the two configs is good (unique privileged). But then
    # the other has at least 2 privileged (proc 1 + whoever was also privileged
    # to make the first one not-unique in the first config... wait, that's
    # circular).

    # Let me think about this more carefully with actual computation.

    return P_total, P_rest, min_cycle_len


# ============================================================
# SECTION 5: The drain bottleneck argument
# ============================================================

def drain_bottleneck(n, ms=None):
    """
    The drain bottleneck argument:

    In the transition graph on ALL configs, each config has out-degree 1
    (deterministic: fire some privileged proc, by some scheduling policy).
    Wait -- actually, the transition is nondeterministic: we can fire ANY
    privileged proc. So each config with k privileged procs has out-degree k.

    For convergence: we need that from every bad config, SOME sequence of
    (fire any privileged proc) choices leads to the good cycle.
    Equivalently: the bad configs, under ALL possible firing choices, must
    have no recurrent SCC (every cycle must be escapable).

    Actually, the Dijkstra model requires convergence under ANY fair scheduler:
    from any bad config, every fair execution eventually reaches a good config.
    This is equivalent to: NO bad SCC exists in the nondeterministic graph
    (where from each config we can fire any privileged proc).

    Wait -- it's even stronger. "No bad SCC" means: there is no set of bad
    configs S such that from every config in S, firing any privileged proc
    stays in S. One escape suffices.

    Actually, the standard definition is: from every bad config, under EVERY
    fair scheduling, you reach a good config. This requires: no bad config
    has all successors in a bad SCC. I.e., for every bad config, there exists
    at least one privileged proc whose firing leads toward the good cycle.
    This is equivalent to: no bad SCC exists in the nondeterministic graph.

    OK so: we need to show that the nondeterministic graph on bad configs
    has at least one SCC.
    """
    if ms is None:
        ms = [2, 2, 2] + [3] * (n - 3)

    P_total = prod(ms)
    P_rest = prod(ms[3:])
    threshold = 4 * 3**(n-2)

    print(f"\n{'='*60}")
    print(f"DRAIN BOTTLENECK ARGUMENT")
    print(f"n={n}, ms={ms}")
    print(f"{'='*60}")

    # Key fact: proc 1's context changes ONLY when proc 0, 1, or 2 fires.
    # Procs 3..n-1 are "far" from proc 1.

    # Define the "proc 1 privileged zone" Z1 = {configs where proc 1 is privileged}.
    # |Z1| = |M| * P_rest.

    # Within Z1, consider firing a far proc j (3 <= j <= n-1).
    # The result is still in Z1 (proc 1's context unchanged, privilege preserved).
    # So the subgraph of Z1 under far-proc fires is CLOSED.

    # Within Z1, consider firing proc 0 or proc 2.
    # This changes proc 1's context (L or R changes).
    # The result may or may not be in Z1.

    # Within Z1, consider firing proc 1.
    # This changes c[1] to 1-c[1]. The result has context (c[0], 1-c[1], c[2]).
    # If (c[0], 1-c[1], c[2]) is in M: result is still in Z1.
    # If not: result leaves Z1.

    # So: the exits from Z1 are:
    # 1. Firing proc 0 to change c[0], possibly making (c[0]', c[1], c[2]) not in M.
    # 2. Firing proc 2 to change c[2], possibly making (c[0], c[1], c[2]') not in M.
    # 3. Firing proc 1 when (c[0], 1-c[1], c[2]) not in M.

    # Exit 3 is interesting: it requires that the toggle pair is NOT in M.
    # For toggle choices (both in M), exit 3 is impossible!

    # For each (a,c) pair:
    # - Choice 0 (neither): (a,*,c) not in M, no issue.
    # - Choice 1 (only (a,0,c)): (a,0,c) in M, fire proc 1 -> (a,1,c) not in M. Exit!
    # - Choice 2 (only (a,1,c)): (a,1,c) in M, fire proc 1 -> (a,0,c) not in M. Exit!
    # - Choice 3 (both): both in M, fire proc 1 -> stays in M. STUCK!

    # So: if all 4 (a,c) pairs use choice 3 (all toggle), |M|=8, and
    # firing proc 1 never leaves Z1. This means Z1 is closed under proc 1 fires.
    # Combined with closure under far fires: Z1 is closed under all fires except
    # proc 0 and proc 2.

    # But |M|=8 means proc 1 is privileged at ALL contexts. This means every
    # config has proc 1 privileged. Only 2 of these are good. And P_total - 2
    # are bad. With Z1 = all configs closed under proc 1 + far fires, the only
    # exits are through proc 0 and proc 2.

    # But proc 0 and proc 2 are also binary. Their fire only changes one state.
    # After firing proc 0: c[0] -> 1-c[0]. Proc 1's context changes.
    # But proc 1 is STILL privileged (since M = all 8 contexts).
    # So Z1 = all configs, and it's closed under ALL fires. No escape!

    # Hmm, but this means every config is bad except 2, and the bad configs
    # form one giant SCC. This is trivially invalid.

    # OK so |M|=8 is clearly bad. What about smaller |M|?

    # Let's focus on the case where some (a,c) pairs are toggle (choice 3).
    # For those pairs, firing proc 1 from (a,b,c) in M leads to (a,1-b,c) also in M.
    # So within that (a,c) subspace, proc 1 firing creates a 2-cycle in c[1].

    # For the 2-cycle to be a bad SCC: both configs must be bad (2+ privileged).
    # Config C has c[1]=b, proc 1 privileged. Fire proc 1: c[1]=1-b, proc 1 still privileged.
    # Are there other privileged procs in both C and C'?
    # In C: procs 0,2 might be privileged (depends on c[0],c[1],c[2],c[n-1],c[3]).
    # In C': procs 0,2 might be privileged (c[0],1-c[1],c[2],c[n-1],c[3]).

    # Key: procs 0 and 2 are binary and have proc 1's state in their context.
    # Proc 0: context is (c[n-1], c[0], c[1]). When c[1] changes, proc 0's
    #   privilege may change.
    # Proc 2: context is (c[1], c[2], c[3]). When c[1] changes, proc 2's
    #   privilege may change.

    # So the 2-cycle (fire proc 1 back and forth) affects procs 0 and 2's privilege.
    # They might alternate privileged/not-privileged.

    # For the 2-cycle to be a bad SCC, we need:
    # - In C: at least 1 proc besides proc 1 is privileged (so C is bad).
    # - In C': at least 1 proc besides proc 1 is privileged (so C' is bad).
    # - From C: can we escape? Only by firing the other privileged proc(s).
    #   If only proc 1 is privileged: C is good (not bad). Contradiction.
    #   So some other proc q is also privileged. Fire q: new config C''.
    #   If C'' is in the SCC: cycle. If C'' is outside: escape.

    # This is getting complex. Let's compute directly for small n.

    return P_total, P_rest


# ============================================================
# SECTION 6: Direct computation for n=4,5,6,7 vs n=8,9
# ============================================================

def compute_3cb_systems(n, ms=None):
    """For small n with 3CB, try to find valid systems or prove none exist.

    For n=4: ms=(2,2,2,3), P=24.
    For n=5: ms=(2,2,2,3,3), P=108.
    """
    if ms is None:
        ms = [2, 2, 2] + [3] * (n - 3)

    P_total = prod(ms)
    threshold = 4 * 3**(n-2)

    print(f"\n{'='*60}")
    print(f"DIRECT COMPUTATION: n={n}, ms={ms}")
    print(f"P_total={P_total}, threshold={threshold}, sub={P_total < threshold}")
    print(f"{'='*60}")

    configs = list(itertools.product(*(range(m) for m in ms)))

    # For small n, enumerate over transition functions for proc 1 only.
    # For each proc 1 transition function, count:
    # - privilege set M
    # - configs where proc 1 is privileged
    # - fraction of those that must be bad

    contexts_1 = [(a, b, c) for a in range(ms[0]) for b in range(ms[1]) for c in range(ms[2])]
    # = [(a,b,c) for a in {0,1} for b in {0,1} for c in {0,1}] = 8 contexts

    # For each context, f_1 can output 0 or 1.
    # 2^8 = 256 possible functions.

    results = []
    for f1_bits in range(2**len(contexts_1)):
        f1 = {}
        M = set()
        for idx, ctx in enumerate(contexts_1):
            val = (f1_bits >> idx) & 1
            f1[ctx] = val
            if val != ctx[1]:  # privileged iff f != S
                M.add(ctx)

        if len(M) == 0:
            continue  # proc 1 is never privileged -- can't fire in good cycle

        priv_total = len(M) * prod(ms[3:])

        # Check: how many good configs can have proc 1 privileged?
        # In the good cycle, proc 1 fires m_1 = 2 times.
        # So exactly 2 good configs have proc 1 privileged.
        # (Unless cycle length is a larger multiple of m_1.)
        # For minimal cycle: exactly 2.

        bad_priv1 = priv_total - 2  # at least this many

        # Check toggle pairs
        toggle_pairs = 0
        for a in range(2):
            for c in range(2):
                if (a, 0, c) in M and (a, 1, c) in M:
                    toggle_pairs += 1

        results.append({
            '|M|': len(M),
            'priv_total': priv_total,
            'bad_priv1': bad_priv1,
            'toggle_pairs': toggle_pairs,
            'M': frozenset(M),
        })

    # Summarize
    from collections import Counter
    size_dist = Counter(r['|M|'] for r in results)
    print(f"\n|M| distribution: {dict(sorted(size_dist.items()))}")

    for M_size in sorted(size_dist.keys()):
        subset = [r for r in results if r['|M|'] == M_size]
        toggle_dist = Counter(r['toggle_pairs'] for r in subset)
        print(f"\n|M|={M_size}: {len(subset)} functions")
        print(f"  Toggle pair distribution: {dict(sorted(toggle_dist.items()))}")
        print(f"  priv_total = {subset[0]['priv_total']}")
        print(f"  bad_priv1 >= {subset[0]['bad_priv1']}")
        print(f"  Ratio bad_priv1/P_total = {subset[0]['bad_priv1']/P_total:.4f}")

    return results


# ============================================================
# SECTION 7: The n=7 vs n=8 comparison
# ============================================================

def n7_vs_n8():
    """Compare n=7 (where 3CB CAN work) vs n=8 (where it CAN'T).

    n=7: ms=(2,2,2,3,3,3,4), P=864 = 4*3^5*... wait.
    Actually for n=7: threshold = 4*3^5 = 972.
    ms=(2,2,2,3,3,3,4) has P=8*108=864 < 972. Sub-threshold.
    But does a valid system exist? The key result says M_7 = 32*3^3 = 864.
    So ms=(2,2,2,3,3,3,4) is AT the threshold for 32*3^(n-4).
    Wait: 32*3^(7-4) = 32*27 = 864. Yes. And threshold = 4*3^5 = 972.
    So P=864 < 972 is sub-threshold for the general theorem.

    But does a valid 3CB system at P=864 exist?
    M_7 = 864, so SOME system with P=864 exists. But does it have 3CB?
    The known witness for M_7 is ms=(2,2,2,3,3,3,4) or some rotation.

    Actually, the key result says M_n = 32*3^(n-4) for 5<=n<=8.
    For n=7: M_7 = 864. The achieving ms must have product 864 = 8*108.
    With 3 binary: 2^3 * product_rest = 8 * product_rest = 864,
    so product_rest = 108 = 4*27 = 4*3^3. So ms_rest has product 108
    from n-3=4 procs. Options: (3,3,3,4), (3,3,12), etc.
    Most likely: ms=(2,2,2,3,3,3,4) or rotation.

    n=8: threshold for 32*3^(n-4) = 32*81 = 2592 = M_8.
    ms=(2,2,2,3,3,3,3,4), P=8*324=2592. This IS at the threshold.
    But the task says ALL 768 constructions fail. So 3CB at n=8 DOESN'T work!

    What changes between n=7 and n=8?
    """
    for n in [4, 5, 6, 7, 8, 9]:
        threshold_general = 4 * 3**(n-2)
        threshold_small = 32 * 3**(n-4) if n >= 4 else None

        # For 3CB with all-ternary rest:
        ms_pure = [2, 2, 2] + [3] * (n - 3)
        P_pure = prod(ms_pure)
        P_rest_pure = 3**(n-3)

        # Ratio: bad configs with proc 1 privileged / total configs
        # For |M|=1: P_rest - 2 bad configs with proc 1 priv
        ratio_M1 = (P_rest_pure - 2) / P_pure

        # For |M|=2: 2*P_rest - 2
        ratio_M2 = (2*P_rest_pure - 2) / P_pure

        # Drain bottleneck: to drain Z1 to good cycle, need to change proc 1's context.
        # Only procs 0, 1, 2 can do this. But they're binary!
        # Each has 2 states, so limited ability to "route" configs.

        # Number of "routes" out of Z1 per step:
        # Firing proc 0 changes c[0] (2 options), proc 1 changes c[1], proc 2 changes c[2].
        # But they're binary, so each fire is deterministic: c[i] -> 1-c[i].
        # So there are only 3 possible exits per config (fire proc 0, 1, or 2).
        # But these exits only help if they lead to a context NOT in M.

        # For a random M with |M|=k, expected fraction of exits that leave Z1:
        # (8-k)/8 for proc 1 fires, varies for proc 0 and 2.

        print(f"\nn={n}: P_pure={P_pure}, P_rest={P_rest_pure}, thresh_gen={threshold_general}")
        print(f"  Ratio P_pure/thresh: {P_pure/threshold_general:.4f}")
        print(f"  |M|=1: {P_rest_pure-2} bad w/ proc1 priv, ratio={ratio_M1:.4f}")
        print(f"  |M|=2: {2*P_rest_pure-2} bad w/ proc1 priv, ratio={ratio_M2:.4f}")
        print(f"  P_rest / (min_cycle_len={sum(ms_pure)}): {P_rest_pure/sum(ms_pure):.2f}")

        # KEY METRIC: configs per good cycle step.
        # If P_rest >> cycle length, then there are many more configs with
        # proc 1 privileged than good cycle steps. The excess must drain.
        # The drain must go through the 3 binary procs (bottleneck).

        # Drain capacity per binary context:
        # From context (a,b,c) in M, we can reach (1-a,b,c), (a,1-b,c), (a,b,1-c)
        # by firing procs 0, 1, 2 respectively.
        # If the target is not in M: we left Z1 (potential drainage).
        # But the target might be another bad config!
        # The question is: does the drainage chain eventually reach a good config?

        # Drainage chain: the near procs (0,1,2) form a 3-bit binary system.
        # From any 3-bit state, we can flip any bit.
        # This is a hypercube graph on {0,1}^3 = 8 vertices.
        # From any context in M, we can reach any other context in 3 flips.
        # But each flip fires a binary proc, which must be privileged!
        # And each config along the way must have proc 0/1/2 privileged.


def ratio_analysis():
    """The critical ratio analysis.

    Key question: at what n does the drain bottleneck become impossible?

    Hypothesis: the bottleneck is the ratio P_rest / good_cycle_length.
    When this ratio exceeds a threshold, bad SCCs are forced.
    """
    print(f"\n{'='*60}")
    print(f"RATIO ANALYSIS: P_rest vs good cycle length")
    print(f"{'='*60}")

    for n in range(4, 13):
        ms = [2, 2, 2] + [3] * (n - 3)
        P_total = prod(ms)
        P_rest = prod(ms[3:])
        threshold = 4 * 3**(n-2)

        # Good cycle length: at minimum sum(ms) = 3n-3
        min_gcl = sum(ms)
        # Proc 1 fires 2 times in good cycle
        # Bad configs with proc 1 priv (|M|=1): P_rest - 2

        # Total good configs: unknown exactly, but bounded.
        # For CUP-2: good = (n+2)(n+3)/2 - 5 (but that's for different ms)
        # For ms=(2,2,2,3,...,3): good >= min_gcl = 3n-3

        # The key ratio: how many bad configs per good config?
        bad_total = P_total - min_gcl
        ratio = bad_total / min_gcl

        # More importantly: configs where proc 1 is priv but bad
        bad_priv1 = P_rest - 2  # for |M|=1

        # Drain rate: from Z1 bad configs, how fast can they drain?
        # Each drain step fires a near proc (0,1,2), changing context.
        # But the near proc must be privileged to fire!
        # Each near proc fire changes 1 bit of (c[0],c[1],c[2]).
        # After the fire, we might be in a non-M context (left Z1)
        # or in another M context (still in Z1).

        # For |M|=1: only 1 context triggers proc 1.
        # The 7 non-M contexts don't have proc 1 privileged.
        # From the M context, we can flip any bit to reach a non-M context.
        # So Z1 is easy to exit (if a near proc is privileged).

        # But the problem is: after exiting Z1, where do we go?
        # The config now has some other procs privileged.
        # Those procs fire, possibly re-entering Z1!

        # The IN-OUT flow:
        # Configs enter Z1 when a near proc fires and changes context back to M.
        # Configs exit Z1 when a near proc fires and changes context away from M.
        # For convergence: the net flow must be out of Z1.
        # But in steady state (SCC), in-flow = out-flow. So there's no net drainage.
        # This means: if Z1 is large enough, it can support a bad SCC that
        # includes both Z1 and non-Z1 configs.

        print(f"n={n}: P={P_total}, P_rest={P_rest}, gcl={min_gcl}, "
              f"bad_priv1={bad_priv1}, bad/good={ratio:.1f}")


# ============================================================
# SECTION 8: Full simulation at n=5 (small enough for exhaustive)
# ============================================================

def simulate_3cb_n5():
    """For n=5 with ms=(2,2,2,3,3), P=108, threshold=108.

    Wait: threshold = 4*3^3 = 108. So P=108 is AT threshold, not below.
    Sub-threshold means P < 108. With 3 binary and 2 ternary: P = 8*9 = 72.
    That's sub-threshold. But ms=(2,2,2,3,3) has P=72? No: 2*2*2*3*3 = 72.
    Wait: 2*2*2*3*3 = 72, not 108. Let me recalculate.

    threshold = 4*3^(5-2) = 4*27 = 108.
    ms=(2,2,2,3,3): P = 72 < 108. Sub-threshold!

    But M_5 = 96. The achieving ms is (2,2,2,3,4) or rotation.
    So ms=(2,2,2,3,3) with P=72 < 96 = M_5 should have NO valid system.

    ms=(2,2,2,3,4) with P = 8*12 = 96 = M_5 IS valid (at the minimum).

    Let's check n=5, ms=(2,2,2,3,3) exhaustively.
    """
    n = 5
    ms = [2, 2, 2, 3, 3]
    P_total = prod(ms)

    print(f"\n{'='*60}")
    print(f"EXHAUSTIVE CHECK: n={n}, ms={ms}, P={P_total}")
    print(f"M_5=96, threshold=108. P={P_total} < 96 so NO valid system should exist.")
    print(f"{'='*60}")

    configs = list(itertools.product(*(range(m) for m in ms)))

    # Try a sample of transition function combinations.
    # For proc 1 (context {0,1}^3 = 8 triples): 2^8 = 256 functions.
    # For proc 3 (context {0,1}*{0,1,2}*{0,1,2} = 2*3*3 = 18 triples): 3^18 ~ 387M. Too many.

    # Instead: let's focus on the COUNTING argument.
    # For n=5, ms=(2,2,2,3,3):
    # P_rest = 3*3 = 9
    # Min good cycle length = sum(ms) = 2+2+2+3+3 = 12
    # |M|=1: proc 1 priv at 1*9 = 9 configs, 2 good, 7 bad.
    # |M|=2: proc 1 priv at 2*9 = 18 configs, 2 good, 16 bad.

    # Total bad configs: P - good_cycle_length >= 72 - 12 = 60.
    # Bad configs with proc 1 priv (|M|=1): 7. Out of 60 total bad: modest.
    # Bad configs with proc 1 priv (|M|=2): 16. Out of 60: significant.

    P_rest = prod(ms[3:])
    min_gcl = sum(ms)

    print(f"\nP_rest = {P_rest}")
    print(f"Min good cycle length = {min_gcl}")
    print(f"|M|=1: {P_rest} priv, 2 good, {P_rest-2} bad. Ratio to total: {(P_rest-2)/P_total:.3f}")
    print(f"|M|=2: {2*P_rest} priv, 2 good, {2*P_rest-2} bad. Ratio: {(2*P_rest-2)/P_total:.3f}")
    print(f"Total bad configs >= {P_total - min_gcl}. Total good = {min_gcl}")

    # At n=5, the ratio is manageable. Bad configs are 60/72 = 83%.
    # But there are only 7-16 bad configs with proc 1 privileged.
    # These can potentially drain to the good cycle.

    # At n=9, ms=(2,2,2,3,3,3,3,3,3):
    n9 = 9
    ms9 = [2, 2, 2] + [3] * 6
    P9 = prod(ms9)
    P_rest9 = prod(ms9[3:])
    min_gcl9 = sum(ms9)

    print(f"\nComparison with n=9, ms={ms9}, P={P9}:")
    print(f"  P_rest = {P_rest9}")
    print(f"  Min good cycle length = {min_gcl9}")
    print(f"  |M|=1: {P_rest9-2} bad w/ proc1 priv. Ratio: {(P_rest9-2)/P9:.3f}")
    print(f"  Total bad >= {P9 - min_gcl9}. Ratio bad/good: {(P9-min_gcl9)/min_gcl9:.1f}")

    # The growth rate:
    # P_rest grows as 3^(n-3), good cycle length grows as 3n-3.
    # Ratio P_rest / gcl ~ 3^(n-3) / (3n) = 3^(n-4) / n.
    # For n=5: 9/12 = 0.75
    # For n=9: 729/24 = 30.4
    # For n=12: 19683/33 = 596.5
    # This ratio EXPLODES. As n grows, there are exponentially more bad
    # configs per good cycle step.

    print(f"\nRatio P_rest / min_gcl (bad configs per good step):")
    for n in range(4, 15):
        ms_n = [2, 2, 2] + [3] * (n - 3)
        r = prod(ms_n[3:]) / sum(ms_n)
        print(f"  n={n}: {r:.1f}")


# ============================================================
# SECTION 9: Direct SCC check for n=5 with specific constructions
# ============================================================

def direct_scc_check_n5():
    """Build actual 3CB systems at n=5 and check for bad SCCs.

    n=5, ms=(2,2,2,3,3), P=72.
    We'll try a few hand-crafted transition functions.
    """
    n = 5
    ms = [2, 2, 2, 3, 3]
    P_total = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"DIRECT SCC CHECK: n={n}, ms={ms}, P={P_total}")
    print(f"{'='*60}")

    # We'll systematically try ALL proc 1 functions (256)
    # and for each, try a few proc 0, 2 functions.
    # For procs 3, 4: use incrementing (Dijkstra-style).

    # Proc 0: context (c[4], c[0], c[1]) in {0,1,2}*{0,1}*{0,1}
    # Wait: c[4] is in {0,1,2} (ternary proc 4 has 3 states). But wait,
    # ms[4]=3, so c[4] in {0,1,2}. Proc 0 context: (c[n-1], c[0], c[1])
    # = (c[4], c[0], c[1]). Context space: 3*2*2 = 12. Output: {0,1}.
    # 2^12 = 4096 functions.

    # Proc 2: context (c[1], c[2], c[3]) in {0,1}*{0,1}*{0,1,2}
    # Context space: 2*2*3 = 12. Output: {0,1}. 2^12 = 4096 functions.

    # Proc 3: context (c[2], c[3], c[4]) in {0,1}*{0,1,2}*{0,1,2}
    # Context space: 2*3*3 = 18. Output: {0,1,2}. 3^18 ~ 387M. Too many.

    # Let's use Dijkstra-style incrementing for procs 3, 4:
    # f_3(L,S,R) = (S+1) % 3 if L != S else S
    # f_4(L,S,R) = (S+1) % 3 if L != S else S
    # (privileged when L != S)

    def make_dijkstra(mi):
        """Dijkstra-style: privileged when L != S, fire to (S+1)%m."""
        def f(L, S, R):
            if L != S:
                return (S + 1) % mi
            return S
        return f

    def make_from_table(table, mi):
        """Make function from lookup table."""
        def f(L, S, R):
            return table.get((L, S, R), S)
        return f

    valid_count = 0
    bad_scc_count = 0
    total_tried = 0

    # Try a representative sample of proc 1 functions
    # and a few options for procs 0, 2

    # For procs 3, 4: use incrementing
    f3 = make_dijkstra(3)
    f4 = make_dijkstra(3)

    # For proc 0: try Dijkstra-style and a few variants
    # Proc 0 context: (c[4], c[0], c[1]). Privileged when L!=S means c[4]!=c[0].
    # But c[4] in {0,1,2} and c[0] in {0,1}. So L!=S when c[4] != c[0].
    # c[4]=2 always triggers (since c[0] in {0,1}).
    # c[4]=1 triggers when c[0]=0. c[4]=0 triggers when c[0]=1.

    def f0_dijkstra(L, S, R):
        if L != S:
            return (S + 1) % 2
        return S

    def f2_dijkstra(L, S, R):
        if L != S:
            return (S + 1) % 2
        return S

    # Try all 256 proc 1 functions
    contexts_1 = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]

    for f1_bits in range(256):
        f1_table = {}
        for idx, ctx in enumerate(contexts_1):
            f1_table[ctx] = (f1_bits >> idx) & 1

        f1 = make_from_table(f1_table, 2)
        fs = [f0_dijkstra, f1, f2_dijkstra, f3, f4]

        # Compute privilege map
        priv_map = {}
        for c in configs:
            priv = []
            for i in range(n):
                L = c[(i-1) % n]
                S = c[i]
                R = c[(i+1) % n]
                if fs[i](L, S, R) != S:
                    priv.append(i)
            priv_map[c] = priv

        # Check liveness
        dead = [c for c in configs if len(priv_map[c]) == 0]
        if dead:
            continue

        # Find good configs (exactly 1 privileged)
        good = {c for c in configs if len(priv_map[c]) == 1}
        bad = {c for c in configs if len(priv_map[c]) >= 2}

        if not good:
            continue

        # Check closure: from each good config, firing the unique privileged proc
        # must lead to another good config.
        good_cycle = True
        for c in good:
            p = priv_map[c][0]
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            new_s = fs[p](L, S, R)
            nc = list(c)
            nc[p] = new_s
            nc = tuple(nc)
            if nc not in good:
                good_cycle = False
                break

        if not good_cycle:
            continue

        # Check for bad SCCs: build nondeterministic graph on bad configs
        # and look for SCCs.
        bad_succ = defaultdict(set)
        for c in bad:
            for p in priv_map[c]:
                L = c[(p-1) % n]
                S = c[p]
                R = c[(p+1) % n]
                new_s = fs[p](L, S, R)
                nc = list(c)
                nc[p] = new_s
                nc = tuple(nc)
                bad_succ[c].add(nc)

        # Check: can every bad config reach a good config?
        # BFS from good configs backwards in the full graph.
        # A bad config is "drainable" if some successor is good or drainable.

        # Forward BFS from each bad config
        can_reach_good = set()
        queue = deque()
        for c in bad:
            for nc in bad_succ[c]:
                if nc in good:
                    can_reach_good.add(c)
                    queue.append(c)
                    break

        # BFS: if c can reach good, then any bad config that can reach c
        # can also reach good.
        # We need the reverse graph.
        bad_pred = defaultdict(set)
        for c in bad:
            for nc in bad_succ[c]:
                if nc in bad:
                    bad_pred[nc].add(c)

        while queue:
            c = queue.popleft()
            for pred in bad_pred[c]:
                if pred not in can_reach_good:
                    can_reach_good.add(pred)
                    queue.append(pred)

        stuck = bad - can_reach_good
        total_tried += 1

        if stuck:
            bad_scc_count += 1
        else:
            valid_count += 1
            M = {ctx for ctx in contexts_1 if f1_table[ctx] != ctx[1]}
            print(f"  VALID! f1_bits={f1_bits}, |M|={len(M)}, M={M}")
            print(f"    good={len(good)}, bad={len(bad)}")

    print(f"\nResults: {total_tried} tried, {valid_count} valid, {bad_scc_count} with bad SCCs")
    print(f"  (using Dijkstra-style procs 0,2,3,4)")

    return valid_count, bad_scc_count


def direct_scc_check_n5_full():
    """More comprehensive: try multiple proc 0/2 functions too."""
    n = 5
    ms = [2, 2, 2, 3, 3]
    P_total = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"COMPREHENSIVE SCC CHECK: n={n}, ms={ms}, P={P_total}")
    print(f"{'='*60}")

    # For procs 3, 4: Dijkstra-style (incrementing when L!=S)
    def make_dijkstra(mi):
        def f(L, S, R):
            return (S + 1) % mi if L != S else S
        return f

    f3 = make_dijkstra(3)
    f4 = make_dijkstra(3)

    # For proc 0: context (c[4], c[0], c[1]). c[4] in {0,1,2}, c[0],c[1] in {0,1}.
    # 12 contexts, binary output. 2^12 = 4096 functions.
    # Too many. Let's sample intelligently.

    # For proc 0, try a few rule types:
    # 1. Dijkstra: priv when L!=S, fire to (S+1)%2
    # 2. Right-compare: priv when S!=R, fire to (S+1)%2
    # 3. Both-compare: priv when L!=S and S!=R, fire to (S+1)%2
    # 4. L-match: priv when L==S, fire to (S+1)%2

    f0_variants = []

    # Dijkstra left
    def f0_dijk_left(L, S, R):
        return (S + 1) % 2 if L != S else S
    f0_variants.append(("dijk_left", f0_dijk_left))

    # Dijkstra right
    def f0_dijk_right(L, S, R):
        return (S + 1) % 2 if S != R else S
    f0_variants.append(("dijk_right", f0_dijk_right))

    # Toggle always
    def f0_toggle(L, S, R):
        return 1 - S
    f0_variants.append(("toggle", f0_toggle))

    # Match left
    def f0_match_L(L, S, R):
        return L % 2 if L % 2 != S else S  # priv when L%2 != S
    f0_variants.append(("match_L", f0_match_L))

    # Similar for proc 2: context (c[1], c[2], c[3]). c[1] in {0,1}, c[2] in {0,1}, c[3] in {0,1,2}.
    f2_variants = []

    def f2_dijk_left(L, S, R):
        return (S + 1) % 2 if L != S else S
    f2_variants.append(("dijk_left", f2_dijk_left))

    def f2_dijk_right(L, S, R):
        return (S + 1) % 2 if S != R else S
    f2_variants.append(("dijk_right", f2_dijk_right))

    def f2_toggle(L, S, R):
        return 1 - S
    f2_variants.append(("toggle", f2_toggle))

    def f2_match_R(L, S, R):
        return R % 2 if R % 2 != S else S
    f2_variants.append(("match_R", f2_match_R))

    # Now try all combinations
    contexts_1 = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]

    valid_count = 0
    bad_scc_count = 0
    total_tried = 0

    for f0_name, f0 in f0_variants:
        for f2_name, f2 in f2_variants:
            for f1_bits in range(256):
                f1_table = {}
                for idx, ctx in enumerate(contexts_1):
                    f1_table[ctx] = (f1_bits >> idx) & 1

                def f1(L, S, R, _t=f1_table):
                    return _t.get((L, S, R), S)

                fs = [f0, f1, f2, f3, f4]

                # Compute privilege map
                priv_map = {}
                for c in configs:
                    priv = []
                    for i in range(n):
                        L = c[(i-1) % n]
                        S = c[i]
                        R = c[(i+1) % n]
                        if fs[i](L, S, R) != S:
                            priv.append(i)
                    priv_map[c] = priv

                # Check liveness
                if any(len(priv_map[c]) == 0 for c in configs):
                    continue

                # Find good/bad
                good = {c for c in configs if len(priv_map[c]) == 1}
                bad = {c for c in configs if len(priv_map[c]) >= 2}

                if not good:
                    continue

                # Check closure
                good_closed = True
                for c in good:
                    p = priv_map[c][0]
                    nc = list(c)
                    nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                    nc = tuple(nc)
                    if nc not in good:
                        good_closed = False
                        break

                if not good_closed:
                    continue

                # Check fairness: good cycle visits all procs
                visited_procs = set()
                start = next(iter(good))
                c = start
                for _ in range(len(good) + 1):
                    p = priv_map[c][0]
                    visited_procs.add(p)
                    nc = list(c)
                    nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                    c = tuple(nc)
                    if c == start:
                        break

                if len(visited_procs) < n:
                    continue

                # Check bad SCCs
                can_reach_good = set()
                bad_succ = defaultdict(set)
                for c in bad:
                    for p in priv_map[c]:
                        nc = list(c)
                        nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                        nc = tuple(nc)
                        bad_succ[c].add(nc)
                        if nc in good:
                            can_reach_good.add(c)

                bad_pred = defaultdict(set)
                for c in bad:
                    for nc in bad_succ[c]:
                        if nc in bad:
                            bad_pred[nc].add(c)

                queue = deque(can_reach_good)
                while queue:
                    c = queue.popleft()
                    for pred in bad_pred[c]:
                        if pred not in can_reach_good:
                            can_reach_good.add(pred)
                            queue.append(pred)

                stuck = bad - can_reach_good
                total_tried += 1

                if stuck:
                    bad_scc_count += 1
                else:
                    valid_count += 1
                    M = {ctx for ctx in contexts_1 if f1_table[ctx] != ctx[1]}
                    print(f"  VALID! f0={f0_name}, f2={f2_name}, |M|={len(M)}")

    print(f"\nResults: {total_tried} tried, {valid_count} valid, {bad_scc_count} with bad SCCs")
    return valid_count, bad_scc_count


# ============================================================
# SECTION 10: The core theorem argument
# ============================================================

def core_theorem_argument():
    """
    THEOREM (3CB Convergence Failure):
    For n >= 8, any system with 3 consecutive binary processors at positions
    {0,1,2} and product < 4*3^(n-2) has recurrent bad SCCs.

    PROOF SKETCH:

    1. SETUP:
       Let M ⊆ {0,1}^3 be proc 1's privileged set (|M| >= 1 for liveness).
       Let P_rest = ∏_{j≥3} m_j.
       Sub-threshold: 8 * P_rest < 4*3^(n-2), so P_rest < 3^(n-2)/2.
       With all-ternary rest: P_rest = 3^(n-3) < 3^(n-2)/2 = 3^(n-3)*3/2. ✓

    2. PRIVILEGE COUNTING:
       - Proc 1 is privileged at |M| * P_rest configs (each M-context with each rest-state).
       - Good cycle has proc 1 firing exactly 2 times (binary), so 2 good configs with proc 1 privileged.
       - Bad configs with proc 1 privileged: |M| * P_rest - 2.

    3. PRIVILEGE PERSISTENCE:
       - Any proc j ∈ {3,...,n-1} can fire without changing (c[0],c[1],c[2]).
       - So proc 1's privilege status is invariant under far-proc fires.
       - If config B is bad with proc 1 privileged and far proc q also privileged:
         Fire q → B'. Proc 1 still privileged in B'. If B' is bad: chain continues.

    4. DRAIN BOTTLENECK:
       - To exit the "proc 1 privileged zone" Z1, must fire proc 0, 1, or 2.
       - These are binary: each fire flips one bit of (c[0],c[1],c[2]).
       - For the config to leave Z1, the new context must be outside M.
       - But the new config might have ANOTHER proc's privilege create a bad config.
       - Re-entry to Z1 is possible when far procs fire and eventually a near
         proc fires back to an M-context.

    5. FAR-PROC CYCLING:
       - The n-3 far procs have P_rest state combinations.
       - In each bad config with proc 1 privileged, at least 1 far proc is also privileged.
       - Far procs can fire in sequence, cycling through their states.
       - KEY: the far procs' firing graph (restricted to Z1) may have cycles.
       - If it does, these cycles are BAD SCCs (proc 1 stays privileged, far procs cycle).

    6. THE IMPOSSIBILITY:
       - For convergence, EVERY bad config in Z1 must have a path to a good config.
       - The only paths out of Z1 go through near-proc fires.
       - But after a near-proc fire (leaving Z1), the config may re-enter Z1
         when far procs fire and near procs fire back.
       - The re-entry rate exceeds the drain rate when P_rest >> 3n.
       - For n >= 8: P_rest = 3^(n-3) >= 3^5 = 243, while good cycle ≈ 3n ≈ 24.
         Ratio > 10. The drain bottleneck is overwhelming.

    This isn't quite rigorous enough. Let me investigate computationally.
    """
    pass


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    print("=" * 70)
    print("PA: 3CB Convergence Failure Investigation")
    print("=" * 70)

    # Section 1: Privilege set enumeration
    print("\n\n### SECTION 1: Privilege Set Enumeration ###")
    priv_sets = enumerate_proc1_privilege_sets()
    by_size = defaultdict(int)
    for M, _, _ in priv_sets:
        by_size[len(M)] += 1
    print(f"Total functions: {len(priv_sets)}")
    print(f"|M| distribution: {dict(sorted(by_size.items()))}")

    # Section 2: Counting analysis for various n
    print("\n\n### SECTION 2: Counting Analysis ###")
    for n in [5, 6, 7, 8, 9, 10]:
        analyze_3cb_counting(n)

    # Section 3: Privilege persistence
    print("\n\n### SECTION 3: Privilege Persistence ###")
    for n in [5, 7, 8, 9]:
        privilege_persistence_analysis(n)

    # Section 4: n=7 vs n=8 comparison
    print("\n\n### SECTION 4: n=7 vs n=8 ###")
    n7_vs_n8()

    # Section 5: Ratio analysis
    print("\n\n### SECTION 5: Ratio Analysis ###")
    ratio_analysis()

    # Section 6: Direct SCC check at n=5
    print("\n\n### SECTION 6: Direct SCC Check at n=5 ###")
    simulate_3cb_n5()

    # Section 7: Direct SCC check (comprehensive)
    print("\n\n### SECTION 7: Comprehensive SCC Check ###")
    direct_scc_check_n5()

    # Section 8: Full comprehensive check
    print("\n\n### SECTION 8: Full Comprehensive Check ###")
    direct_scc_check_n5_full()
