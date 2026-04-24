"""
RA12 v2: Investigate sorry 5 — odd-parity residual.

The Lean proof takes an ARBITRARY good cycle as given. We don't need to find
valid systems — we need to enumerate ALL possible good cycles (mover sequences
+ config sequences) for given ms.

A good cycle is:
- A sequence of configs c_0, c_1, ..., c_{L-1} where each c_k is in the full
  config space
- Each c_k has exactly one privileged processor (mover)
- c_{k+1} = apply_move(c_k, mover_k)
- The sequence is a cycle: applying move at c_{L-1} gives c_0
- Every config in the cycle is distinct

We need to find good cycles where:
1. There exist 3 consecutive binary procs
2. The middle binary has isolated firings with fc >= 2
3. The MinFiringGap has odd parity for at least one neighbor

Key insight: for binary procs with state {0,1}, the transition f(L,S,R) must
return 1-S (flip) whenever the proc is privileged. So binary behavior is forced.

For ternary procs, f(L,S,R) can return any value != S when privileged.

Actually, let me think more carefully. A "good cycle" in the Lean formalization
is a property of a System (which includes transition functions). The cycle is
determined by the system's transitions.

But the sorry is universally quantified: for ALL systems with 3 consecutive
binary at sub-threshold, ALL good cycles have entry conflict.

So we need to check: over all possible transition functions, can any system
produce a good cycle that reaches the odd-parity residual WITHOUT entry conflict?

Since entry conflict is a property of the cycle (not the transitions), and the
cycle IS determined by the transitions... let me enumerate more transition types.

For binary proc (m=2): only one non-identity map: S -> 1-S. So binary
transitions are completely determined.

For ternary proc (m=3): when privileged, f(L,S,R) != S, so f maps to one of
the other two values. This can depend on (L,S,R). There are 3^3=27 possible
(L,S,R) triples, and for each, 2 choices of output. So 2^27 possible ternary
transition functions.

That's way too many. Let me instead directly enumerate good cycles.

Actually, let me reconsider. The question is simpler than I'm making it.

A good cycle with 3 consecutive binary at {0,1,2} (positions):
- Binary procs flip when they fire
- For any mover word, the binary proc states are determined by initial values + firing history
- The mover word determines which proc fires each step

So the approach is:
1. Enumerate all possible mover words (cyclic sequences of proc indices)
2. For each mover word, determine if it can be realized as a good cycle
3. If so, check isolation + parity

But mover words can be long. Let me bound the length.

Actually, let me just go back to the existing scripts. The cic_case3a_proof3.py
should have infrastructure for this.
"""

import itertools
from collections import defaultdict

def enumerate_good_cycles_small(ms, max_len=30):
    """
    Enumerate good cycles by BFS over config space.

    A good cycle exists within the config space for some transition functions.
    We enumerate by: for each config, for each possible single-privileged-proc
    assignment, try to build forward.

    This is transition-function agnostic: we allow ANY valid move (the new state
    can be anything != current state at the mover, within the modulus).
    """
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    all_cfgs = list(itertools.product(*(range(m) for m in ms)))

    # For each config, each possible mover, and each possible new state:
    # Build a successor.
    # A good cycle = a cycle in this graph where each config has exactly one
    # possible mover (privileged processor). But which proc is privileged
    # depends on the transition function, which we don't know.

    # Alternative approach: enumerate mover words and check consistency.
    # For 3 binary procs at {0,1,2} and ternary at rest:
    # Binary procs: when they fire, they flip (0<->1). Always.
    # Ternary procs: when they fire, state changes to some other value.

    # So a good cycle is determined by:
    # (1) An initial config c_0
    # (2) A mover sequence m_0, m_1, ..., m_{L-1}
    # (3) For each ternary mover step, a choice of new state

    # Then the cycle condition: the final config = c_0
    # And the single-privilege condition: at each step, exactly one proc is privileged

    # The single-privilege condition is the hardest to check because it depends
    # on the transition function. But we can work backwards: the mover IS the
    # privileged proc. So we need that there EXISTS a transition function where
    # at each step, the mover is the ONLY privileged proc.

    # This is complex. Let me try a simpler approach first: just check all
    # transition functions with context-independent transitions (proc-level modes).

    # For binary: flip (forced)
    # For ternary: inc or dec (proc-level)
    # For ternary with m=3: we can also have context-DEPENDENT transitions.
    # But at minimum cycle length, each ternary fires exactly m=3 times,
    # and must return to start. With 3 fires and m=3: inc(0->1->2->0) or dec(0->2->1->0).

    # Actually, we should also consider non-minimum-length cycles.
    # But the Lean proof's sorry is for n >= 9, so let me focus there.

    pass

def check_parity_residual_direct(n, ms, binary_triple_start):
    """
    Direct check: for given ms with 3 consecutive binary starting at
    binary_triple_start, enumerate ALL good cycles (via all transition functions)
    and check the odd-parity residual.

    For ternary procs with context-dependent transitions:
    With m=3, each (L,S,R) context maps to one of 2 non-S values.
    For proc with m=3, there are 3*m_L*m_R possible (L,S,R) contexts = 3*m_L*m_R.
    Each has 2 choices. Total: 2^(3*m_L*m_R) functions per proc.

    For n=5 with ms=[2,2,2,3,3]: proc 3 has contexts (L=2,S=3,R=3) -> 2^18 = 262144
    and proc 4 has (L=3,S=3,R=2) -> 2^18. Total: 2^36 ≈ 7*10^10. Way too many.

    So we restrict to proc-level modes (inc/dec per ternary proc).
    """
    pass

def check_with_all_contexts(n, ms, binary_pos, max_trans=None):
    """
    For small n: enumerate ALL context-dependent transition functions for ternary procs.
    For n=5, ms=[2,2,2,3,3]: ternary procs 3,4.
    Proc 3: left=proc2(m=2), self(m=3), right=proc4(m=3). Contexts: 2*3*3=18. Choices: 2^18.
    Proc 4: left=proc3(m=3), self(m=3), right=proc0(m=2). Contexts: 3*3*2=18. Choices: 2^18.
    Total: 2^36 ~ 70 billion. Too many.

    But: we only care about cycles that actually exist. Let me try a smarter approach.
    """
    pass

def smart_cycle_search(ms):
    """
    Build good cycles by forward simulation.

    Start from every config. For each config, try every possible single mover.
    For each mover, try every possible new state for that mover.
    Follow the chain until we get a cycle or dead end.

    The constraint "exactly one privileged proc" means: at each config,
    the transition function must make exactly one proc privileged.
    We don't fix the transition function in advance — we build it as we go.

    Key: for a config c and chosen mover p, the transition function must satisfy:
    - f_p(L,S,R) != S (p is privileged)
    - f_q(L',S',R') == S' for all q != p (q is not privileged)

    The second condition constrains the transition function at non-mover contexts.
    As we build the cycle, we accumulate constraints on f.

    This is a constraint-satisfaction approach.
    """
    n = len(ms)
    all_cfgs = list(itertools.product(*(range(m) for m in ms)))

    # State: (current config, accumulated constraints on f)
    # Constraints: for each proc p, a partial function
    #   f_p : (L,S,R) -> value
    # where some entries are forced by mover/non-mover conditions.

    # For binary procs (m=2): f_p(L,S,R) is always 1-S when privileged.
    # So binary transition is context-independent and fixed.

    # For ternary procs: f_p(L,S,R) when privileged can be either of 2 values.
    # When not privileged: f_p(L,S,R) = S (identity).

    # Constraint: at a non-mover step with context (L,S,R), we need f_p(L,S,R)=S.
    # At a mover step with context (L,S,R), we need f_p(L,S,R)!=S.
    # CONFLICT = same (L,S,R) appears at both mover and non-mover step.
    # THAT'S EXACTLY ENTRY CONFLICT!

    # So entry conflict is equivalent to: there exists proc p and context (L,S,R)
    # that appears at both a mover step and a non-mover step.

    # A good cycle WITHOUT entry conflict means: for each proc p, the set of
    # (L,S,R) contexts at mover steps is DISJOINT from non-mover steps.
    # This means a valid transition function CAN exist (set f_p = S for non-mover
    # contexts, f_p = anything != S for mover contexts).

    # So the question reduces to: enumerate all valid config cycles (mover sequences)
    # that have NO entry conflict, and check if any reach the odd-parity residual.

    # If ALL such cycles have entry conflict, the theorem is proved.
    # If some don't have entry conflict but also don't reach odd-parity, the odd-parity
    # case may be vacuous.

    # For efficiency: we don't need to enumerate valid systems. We enumerate
    # ALL possible mover sequences + config sequences that form a cycle,
    # and check entry conflict.

    # A cycle: sequence c_0, c_1, ..., c_{L-1} where:
    # - c_{k+1} = c_k with mover_k's value changed
    # - c_0 = apply_move(c_{L-1}, mover_{L-1})
    # - all c_k distinct
    # - at each step, only one proc changes value

    # DFS from each starting config
    cycles_found = []
    visited_cycles = set()

    for start_cfg in all_cfgs:
        # DFS with max depth
        stack = [(start_cfg, [start_cfg], [], set([start_cfg]))]

        while stack:
            cfg, path, movers, path_set = stack.pop()

            if len(path) > 40:  # max cycle length
                continue

            # Try each possible mover and new state
            for p in range(n):
                L_val = cfg[(p-1) % n]
                S_val = cfg[p]
                R_val = cfg[(p+1) % n]

                for new_s in range(ms[p]):
                    if new_s == S_val:
                        continue  # not a valid move

                    new_cfg = list(cfg)
                    new_cfg[p] = new_s
                    new_cfg = tuple(new_cfg)

                    if new_cfg == start_cfg and len(path) >= 2:
                        # Found a cycle!
                        cycle = list(path)
                        mover_seq = movers + [p]
                        cycle_key = tuple(sorted(cycle))
                        if cycle_key not in visited_cycles:
                            visited_cycles.add(cycle_key)
                            cycles_found.append((cycle, mover_seq))
                    elif new_cfg not in path_set and len(path) < 40:
                        stack.append((new_cfg, path + [new_cfg], movers + [p], path_set | {new_cfg}))

    return cycles_found

def focused_investigation():
    """
    Focused approach: at n=5,7 with 3 consecutive binary, enumerate good cycles
    (config sequences where one proc changes per step, forming a cycle).

    Check: among those with ri isolated + fc>=2 + odd-parity, do ALL have EC?
    """
    print("=" * 70)
    print("SORRY 5 v2: Focused investigation via cycle enumeration")
    print("=" * 70)

    # n=5 is small enough for direct enumeration
    # Total configs = 2^3 * 3^2 = 72
    # Good cycles visit a subset and return

    n = 5
    ms = [2, 2, 2, 3, 3]
    binary_pos = [0, 1, 2]
    i, ri, rri = 0, 1, 2

    print(f"\nn={n}, ms={ms}")
    print(f"Binary triple at {i},{ri},{rri}")
    print("Searching for good cycles (this may take a while)...")

    # More efficient: BFS from each config, following single-proc moves
    all_cfgs = list(itertools.product(*(range(m) for m in ms)))

    # Build adjacency: cfg1 -> [(cfg2, mover, new_state), ...]
    adj = defaultdict(list)
    for cfg in all_cfgs:
        for p in range(n):
            S = cfg[p]
            for new_s in range(ms[p]):
                if new_s != S:
                    new_cfg = list(cfg)
                    new_cfg[p] = new_s
                    new_cfg = tuple(new_cfg)
                    adj[cfg].append((new_cfg, p))

    # Find ALL simple cycles using DFS (up to reasonable length)
    # This is expensive but n=5 has only 72 configs

    print(f"Config space size: {len(all_cfgs)}")

    # Use Johnson's algorithm or similar? Actually for 72 nodes it's feasible
    # to enumerate short cycles.

    # Let me instead focus on what matters: check if the odd-parity residual
    # case can even arise. The key structural question is:
    #
    # For 3 consecutive binary at {0,1,2} (states {0,1}):
    # Middle proc ri=1 has neighbors i=0 (binary) and rri=2 (binary).
    # When ri fires at step a, its state flips.
    # Between consecutive ri-fires at a and b:
    #   - left neighbor (i=0) fires some number of times -> left_fires
    #   - right neighbor (rri=2) fires some number of times -> right_fires
    # Even parity: both left_fires % 2 == 0 AND right_fires % 2 == 0 -> EC by IsolatedParityEC
    # Odd parity: at least one of left_fires, right_fires is odd

    # With all 3 procs binary (states {0,1}), the state at ri after the gap
    # determines context. Since ri fires at a and b, and doesn't fire between:
    #   ri's state at step a+1 = flipped(state at a)
    #   ri's state at step b = same as a+1 (no fires between)
    # So S at a+1 = S at b. ✓ (this is the S-parity match in the Lean proof)

    # For L (= proc i): state at a+1 = state at a (ri fires, not i)
    #   state at b = state at a + left_fires (mod 2)
    #   Even parity: state at b = state at a+1 -> L matches -> EC
    #   Odd parity: state at b = 1 - state at a+1 -> L differs

    # For R (= proc rri=2): similarly
    #   Even: R matches -> EC
    #   Odd: R differs

    # So in the odd-parity case:
    #   S matches (always), but L or R differs between steps a+1 and b.
    #   The context (L,S,R) at step a+1 differs from (L,S,R) at step b
    #   in the L or R component.

    # This means the standard parity EC argument FAILS for the odd case.
    # But some OTHER EC might exist elsewhere in the cycle.

    # The question: can we construct a good cycle where:
    # (a) ri has isolated firings with gap >= 2
    # (b) at least one neighbor has odd fires in the gap
    # (c) NO entry conflict ANYWHERE

    # If no such cycle exists, the sorry is dischargeable.
    # If such cycles exist, we need a different mechanism.

    # Key structural insight: with only 8 possible (L,S,R) contexts at all-binary
    # procs, and the cycle visiting many steps, pigeonhole might force EC.

    # Let me check: what's the minimum cycle length with fc(ri) >= 2 + isolated?
    # ri fires at least twice, each fire is isolated (gap >= 2).
    # Between consecutive ri-fires, at least one other proc fires.
    # So cycle length >= 2*fc(ri) + fc(ri) = 3*fc(ri) >= 6.
    # Actually, isolation just means gap >= 2 between ri-fires, so length >= 2*fc(ri).
    # With fc(ri) >= 2: length >= 4.

    # But also, the theorem requires n >= 9, hfull (every proc fires at least once).
    # With n=9 procs each firing at least once, cycle length >= 9.

    # Let me think about this more carefully with the actual Lean hypotheses.
    # The sorry has: n >= 9, hfull (all procs fire), 3 consecutive binary,
    # sub-threshold product, some mover outside the triple.

    # With n=9, hfull, all 9 procs fire at least once -> L >= 9.
    # Sub-threshold: product < 4*3^7 = 8748.
    # With 3 binary + 6 ternary: 2^3 * 3^6 = 5832 < 8748.
    # Each ternary fires at least 3 times (to return to initial state).
    # Each binary fires at least 2 times (even fire count).
    # Total fires = L >= 3*2 + 6*3 = 24.

    # At L=24 with 9 procs, the middle binary ri sees (L,S,R) ∈ {0,1}^3 = 8 values.
    # ri fires 2+ times -> 2+ mover steps + 22+ non-mover steps.
    # With 8 possible contexts and 22+ non-mover steps, pigeonhole gives repeats
    # in NON-MOVER contexts. But that's not EC — we need a context that appears
    # at BOTH mover and non-mover.

    # ri's 2 mover contexts: 2 of the 8 possible.
    # ri's 22+ non-mover contexts: must include at least ceil(22/8) = 3 repeats.
    # But do any of the 22+ hit one of the 2 mover contexts?

    # Not necessarily. Consider: ri fires twice with contexts (0,0,0) and (1,1,1).
    # All other steps could have ri see contexts from {(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0)}.
    # That's 6 remaining values for 22 steps — possible with repeats.

    # So pigeonhole at ri alone doesn't force EC. The EC might come from other procs.

    # But the Lean theorem says ALL good cycles with these hypotheses have EC.
    # The even-parity case is handled. The odd-parity case has sorry.
    # The theorem IS correct (proved computationally). So the sorry case either:
    # (A) Never arises (vacuous), or
    # (B) Always has EC by some mechanism we haven't identified.

    # Let me check option (A) more carefully.

    # Can isolated firings with odd parity actually occur?
    # ri fires at step a and b (b > a, gap >= 2, no ri-fires between).
    # Odd parity for left: proc i fires an odd number of times in (a,b).
    # Odd parity for right: proc rri fires an odd number of times in (a,b).
    #
    # With hfull: all procs fire. But the gap (a,b) is just a SUBinterval of the cycle.
    # A proc might fire outside the gap and still have even fires inside.
    #
    # Actually, let me check: with hfull + every-proc-fires + binary-even-fire-count,
    # is the parity always even?
    #
    # Binary proc i fires an EVEN number of times in total (binary_fireCount_even).
    # In the gap (a,b), proc i fires some number of times.
    # This could be even or odd — it's a subinterval.
    #
    # So odd parity CAN arise in principle. The question is whether it actually
    # arises in any valid good cycle at n >= 9.

    # Let me try a different computational approach: build good cycles for n=9
    # using the CUP-2 or CLB construction, and check.

    print("\nChecking CLB/CUP constructions at n=9 for odd-parity residual...")

    # The CLB construction: ms=(2,3,3,3,3,3,3,3,2) — NOT 3 consecutive binary
    # CUP-2: ms=(2,3,3,3,3,3,3,3,2) — also not 3 consecutive binary
    # For 3 consecutive binary: ms=(2,2,2,3,3,3,3,3,3)
    # This is sub-threshold but has no known valid system.
    # That's the whole POINT of the lower bound proof — no valid system exists.

    # So there are NO good cycles at n=9 with ms=(2,2,2,3,3,3,3,3,3)?
    # That can't be right — the theorem proves False from the existence of a good cycle.
    # The sorry is inside a proof by contradiction: assume a good cycle exists, derive False.

    # The odd-parity branch is reached when:
    # 1. No safe processor (every proc is within 1 hop of some mover)
    # 2. Some mover is outside the triple {i, ri, rri}
    # 3. ri has isolated firings with fc >= 2
    # 4. At least one neighbor has odd prefix fire count parity in the MinFiringGap

    # The question is: given all these hypotheses, is there actually a contradiction
    # even WITHOUT constructing an explicit EC?

    # Let me check computationally at n=5 whether the odd-parity case can arise
    # in ANY cycle (not necessarily a valid good cycle — just any config sequence).

    print("\nDirect constraint check at n=5...")
    check_odd_parity_existence(5, [2,2,2,3,3])

    print("\nDirect constraint check at n=7...")
    check_odd_parity_existence(7, [2,2,2,3,3,3,3])

def check_odd_parity_existence(n, ms):
    """
    Check if the odd-parity residual can arise at all.

    We enumerate short mover words and check if a consistent config sequence exists
    that satisfies:
    - 3 consecutive binary at {0,1,2}
    - ri=1 fires at steps a, b with gap >= 2
    - ri has isolated firings (no consecutive ri-fires)
    - At least one neighbor (i=0 or rri=2) fires odd times in gap(a,b)
    - All procs fire at least once (hfull)
    - Some mover is outside {0,1,2}
    """
    binary_pos = [0, 1, 2]
    ri = 1

    # For short mover words (length 5 to 20):
    # Count mover words satisfying structural conditions
    # Then check if a consistent config assignment exists

    # Actually, for the structure check, we don't even need configs.
    # The parity is determined by the mover word alone!
    # prefix_fire_count(p, k) = number of times p appears in movers[0:k]
    # So the parity check is purely about the mover word.

    count_satisfying = 0
    count_with_ec = 0
    count_without_ec = 0

    # For small n, try mover words of reasonable length
    # Minimum length: each proc fires at least once -> length >= n
    # Binary procs fire even times -> at least 2 each -> length >= 3*2 + (n-3)*1 = n+3
    # But ternary fire count must be divisible by m_p? No, not necessarily in general.
    # Actually for a good cycle, each proc must return to its initial state.
    # Binary: fire count must be even.
    # Ternary (m=3): fire count must be divisible by 3 IF using increment transition,
    # but could be any value with context-dependent transitions.

    # Wait — binary fire count must be even because value returns to initial.
    # Ternary with m=3: after k fires, value = (initial + k*delta) mod 3 for some delta.
    # If delta = +1: need k ≡ 0 mod 3. If delta = -1: need k ≡ 0 mod 3.
    # If context-dependent: could be any k, as long as the sequence of deltas sums to 0 mod 3.

    # For now, let's assume binary fire counts are even and ternary fire counts are
    # multiples of 3 (proc-level mode). This covers the main cases.

    min_len = max(n + 3, 2 * 3)  # at least 3 binary firing twice each + n-3 ternary once
    max_len = 25

    # Instead of enumerating all mover words (n^L possibilities), let me reason:

    # Take a specific mover word structure:
    # ri=1 fires at positions a, b with b - a = gap
    # In (a, b), i=0 fires f_L times, rri=2 fires f_R times
    # Odd parity: f_L odd or f_R odd

    # For the MinFiringGap to have gap >= 2: between a and b, at least 1 other step
    # (and ri doesn't fire).

    # Simple example: ri fires at steps 0 and 3 (gap=3).
    # Steps 1,2: two non-ri movers.
    # If step 1 fires proc 0 and step 2 fires proc 3:
    #   f_L = 1 (odd), f_R = 0 (even) -> odd parity for left

    # Can this be realized as a good cycle? The mover word would need to
    # continue and form a cycle with all procs firing.

    # Let me build concrete examples.

    print(f"  Building concrete odd-parity mover words for n={n}...")

    # Approach: enumerate mover words that satisfy:
    # (1) Each binary fires an even number of times
    # (2) ri=1 has all isolated firings
    # (3) hfull: each proc fires >= 1
    # (4) Some mover outside {0,1,2}
    # (5) MinFiringGap of ri has odd parity for at least one neighbor
    # Then check: can this mover word yield a good cycle (consistent config sequence)?

    # For a mover word to yield a good cycle:
    # - Binary procs: state determined by initial + fire count parity up to that point
    # - Ternary procs: state can be anything compatible (context-dependent transition)
    # - Need: each config is distinct (no repeated configs in cycle)
    # - Need: transition function consistency (no entry conflict!)

    # AH HA. The last condition IS the entry conflict condition.
    # A mover word can be realized as a good cycle WITHOUT entry conflict
    # if and only if there is no entry conflict in the resulting cycle.

    # So the question becomes: for mover words satisfying (1)-(5),
    # does the resulting config sequence ALWAYS have entry conflict?

    # To check this, we need to actually build the config sequence.
    # Binary values are determined. Ternary values have freedom.
    # EC at a binary proc depends only on binary neighbor values -> determined.
    # EC at a ternary proc depends on its neighbors.

    # Let me check EC at binary procs first (which is fully determined).

    # For proc ri=1 (binary, neighbors 0 and 2, both binary):
    # Context (L,S,R) = (c[0], c[1], c[2]) ∈ {0,1}^3
    # c[p] at step k = (c[p]_initial + prefix_fire_count(p,k)) % 2
    # So context at step k =
    #   (init_0 + pfc(0,k)) % 2, (init_1 + pfc(1,k)) % 2, (init_2 + pfc(2,k)) % 2

    # Since we can choose initial values freely, let's set init_0 = init_1 = init_2 = 0.
    # Then context at step k = (pfc(0,k)%2, pfc(1,k)%2, pfc(2,k)%2)

    # EC at ri=1: exists step k where mover=1 and step k' where mover≠1
    # with same (pfc(0,k)%2, pfc(1,k)%2, pfc(2,k)%2) = (pfc(0,k')%2, pfc(1,k')%2, pfc(2,k')%2)

    # Since the context is in {0,1}^3 (8 values), and the cycle has L steps,
    # with L >= n+3 >= 8 for n=5, we have L >= 8 steps.
    # ri fires 2+ times -> 2+ mover steps. L-2 >= 6 non-mover steps.
    # 2 mover contexts + 6 non-mover contexts from 8 possible values.
    # By pigeonhole: if any of the 2 mover contexts equals any of the 6 non-mover contexts, EC.
    # If not: the 2 mover + 6 non-mover must use 8 distinct values = all of {0,1}^3.

    # Can we have exactly 2 mover steps using 2 unique contexts and 6 non-mover steps
    # using 6 unique contexts, all 8 values used exactly once?
    # That requires L = 8 exactly, and each context appears exactly once.

    # With n=5, binary fires: 0 fires 2+ times, 1 fires 2+ times, 2 fires 2+ times.
    # Total binary fires >= 6. Plus n-3=2 ternary procs firing >= 1 each.
    # Total L >= 8.

    # If L = 8 exactly: binary fires = 6 (2 each) + ternary fires = 2 (1 each).
    # But ternary with 1 fire: state changes and doesn't return. Not a valid cycle.
    # So ternary needs fire count ≡ 0 mod 3 for proc-level mode, minimum 3.
    # With proc-level: L >= 6 + 6 = 12.

    # But with context-dependent transitions, ternary fire count doesn't need to be
    # a multiple of 3. It just needs to return to initial value.
    # With m=3: after k fires with arbitrary transitions, can we return to initial?
    # Yes if the sum of increments (each ±1 or +2) sums to 0 mod 3.
    # With 1 fire: increment is +1 or +2. Neither is 0 mod 3. So 1 fire doesn't work.
    # With 2 fires: +1+1=2, +1+2=0, +2+1=0, +2+2=1. So 2 fires CAN return (+1+2 or +2+1).
    # With 3 fires: many combos work.

    # So minimum ternary fires = 2 (with context-dependent transitions).
    # Total L >= 6 + 4 = 10 for n=5.

    # With L=10: 2 mover steps at ri, 8 non-mover steps. 8 non-mover from 8 values.
    # All non-mover contexts must be distinct, and the 2 mover contexts must differ
    # from all 8 non-mover. But 2+8=10 values from 8 possible -> PIGEONHOLE:
    # some value repeats. If mover context repeats a non-mover context -> EC.
    # If two non-mover contexts repeat -> not EC at ri (but may be EC elsewhere).
    # If two mover contexts are the same... that can happen.

    # Wait: 10 steps, each with a context from {0,1}^3 = 8 values.
    # By pigeonhole, at least 2 steps share a context.
    # If both are mover or both are non-mover: no EC at ri.
    # If one is mover and one is non-mover: EC at ri!

    # So for L >= 10: with 8 possible contexts and 10 steps, at least one pair shares
    # a context. The question: can ALL repeated-context pairs be mover-mover or
    # non-mover-non-mover?

    # With 2 mover steps and 8 non-mover steps:
    # If the 2 mover contexts are the same: that accounts for one repeat.
    # The remaining 8 non-mover + 1 unique mover = 9 contexts from 8 values.
    # Another repeat is forced. Could be non-mover-non-mover.
    # So: 2 mover same + 2 non-mover same = 2 repeats in 10 items from 8 values.
    # Actually 10 items from 8 values = at least 2 repeats (by pigeonhole with surplus 2).
    # It's possible to have both repeats be "same type":
    # Mover-mover repeat + non-mover-non-mover repeat -> no EC at ri.

    # So EC at ri is NOT guaranteed by pigeonhole alone at L=10.
    # But EC somewhere else might be guaranteed.

    # At L=12 (proc-level modes): 2 mover steps, 10 non-mover steps.
    # 12 steps from 8 values -> at least 4 repeats.
    # 2 mover: could share 1 context. Then 10 non-mover from 8 values -> 2+ repeats.
    # Non-mover repeats: 10 from 7 remaining -> 3 repeats. All could be non-mover-non-mover.
    # Total: 1 + 3 = 4 repeats. All could be same-type. So still not forced EC at ri.

    # Conclusion: pigeonhole at ri alone doesn't force EC. The proof needs another mechanism.

    # Let me now check ALL 3 binary procs together.
    # EC at proc 0: context (c[-1%5], c[0], c[1]) = (c[4], c[0], c[1])
    #   c[4] is ternary -> not determined by parity alone
    # EC at proc 2: context (c[1], c[2], c[3])
    #   c[3] is ternary -> not determined by parity alone

    # So EC at procs 0 and 2 depends on ternary values, which have freedom.
    # The adversary can choose ternary transitions to avoid EC at procs 0,2.

    # So the mechanism for the odd-parity case must be more subtle.
    # Let me just do the brute-force enumeration for n=5.

    print(f"  Brute-force cycle enumeration for n={n}...")

    # Enumerate ALL simple cycles in the config graph
    # Config graph: nodes = all configs, edges = single-proc moves
    all_cfgs = list(itertools.product(*(range(m) for m in ms)))
    cfg_idx = {c: i for i, c in enumerate(all_cfgs)}

    # Build adjacency list
    adj = defaultdict(list)
    for cfg in all_cfgs:
        for p in range(n):
            S = cfg[p]
            for new_s in range(ms[p]):
                if new_s != S:
                    new_cfg = list(cfg)
                    new_cfg[p] = new_s
                    new_cfg = tuple(new_cfg)
                    adj[cfg].append((new_cfg, p))

    # Find cycles using DFS from a subset of starting configs
    # Limit search depth
    print(f"  Config space: {len(all_cfgs)} configs")

    cycle_count = 0
    isolated_count = 0
    odd_parity_count = 0
    odd_no_ec_count = 0
    odd_with_ec_count = 0

    max_depth = 16 if n == 5 else 10

    checked = 0
    for start_idx, start in enumerate(all_cfgs):
        if start_idx % 10 == 0:
            print(f"  Starting config {start_idx}/{len(all_cfgs)}, "
                  f"cycles found: {cycle_count}, odd: {odd_parity_count}")

        # DFS
        # State: (current_cfg, path_as_tuple, movers_as_tuple)
        stack = [(start, (start,), ())]

        while stack:
            cfg, path, movers = stack.pop()

            if len(path) > max_depth:
                continue

            path_set = set(path)

            for new_cfg, p in adj[cfg]:
                new_movers = movers + (p,)

                if new_cfg == start and len(path) >= 4:
                    # Found a cycle
                    cycle = list(path)
                    mover_list = list(new_movers)
                    L = len(cycle)

                    # Check hfull
                    procs_that_fire = set(mover_list)
                    if len(procs_that_fire) < n:
                        continue

                    # Check binary fire counts are even
                    from collections import Counter
                    fc = Counter(mover_list)
                    if any(fc[b] % 2 != 0 for b in binary_pos):
                        continue

                    # Check mover outside triple
                    if procs_that_fire <= {0, 1, 2}:
                        continue

                    cycle_count += 1

                    # Check ri=1 isolated firings
                    ri_steps = [k for k in range(L) if mover_list[k] == ri]
                    ri_fc = len(ri_steps)
                    if ri_fc < 2:
                        continue

                    # Check isolation
                    isolated = True
                    for k in ri_steps:
                        next_k = (k + 1) % L
                        if mover_list[next_k] == ri:
                            isolated = False
                            break
                    if not isolated:
                        continue

                    isolated_count += 1

                    # Find MinFiringGap
                    gaps = []
                    for idx in range(len(ri_steps)):
                        a = ri_steps[idx]
                        b = ri_steps[(idx + 1) % len(ri_steps)]
                        if b > a:
                            gap = b - a
                        else:
                            gap = (L - a) + b
                        gaps.append((a, b, gap))

                    min_gap = min(g for _, _, g in gaps)
                    if min_gap < 2:
                        continue

                    min_pair = [(a, b, g) for a, b, g in gaps if g == min_gap][0]
                    a_step, b_step, gap = min_pair

                    # Count neighbor fires in gap
                    left_fires = 0
                    right_fires = 0
                    for k_off in range(1, gap):
                        step = (a_step + k_off) % L
                        if mover_list[step] == 0:  # i
                            left_fires += 1
                        if mover_list[step] == 2:  # rri
                            right_fires += 1

                    if left_fires % 2 == 0 and right_fires % 2 == 0:
                        continue  # even parity, handled

                    odd_parity_count += 1

                    # Check EC at ri
                    # Context at ri: (c[0], c[1], c[2])
                    mover_contexts = set()
                    nonmover_contexts = set()
                    for k in range(L):
                        ctx = (cycle[k][0], cycle[k][1], cycle[k][2])
                        if mover_list[k] == ri:
                            mover_contexts.add(ctx)
                        else:
                            nonmover_contexts.add(ctx)

                    ec_at_ri = bool(mover_contexts & nonmover_contexts)

                    # Check EC at all procs
                    has_ec_anywhere = False
                    for p in range(n):
                        mc = set()
                        nc = set()
                        for k in range(L):
                            left_v = cycle[k][(p-1) % n]
                            self_v = cycle[k][p]
                            right_v = cycle[k][(p+1) % n]
                            ctx = (left_v, self_v, right_v)
                            if mover_list[k] == p:
                                mc.add(ctx)
                            else:
                                nc.add(ctx)
                        if mc & nc:
                            has_ec_anywhere = True
                            break

                    if has_ec_anywhere:
                        odd_with_ec_count += 1
                    else:
                        odd_no_ec_count += 1
                        print(f"\n  *** ODD-PARITY CYCLE WITHOUT EC! ***")
                        print(f"  Length: {L}")
                        print(f"  Movers: {mover_list}")
                        print(f"  Cycle: {cycle}")
                        print(f"  Gap: {gap}, L_fires={left_fires}, R_fires={right_fires}")

                elif new_cfg not in path_set:
                    stack.append((new_cfg, path + (new_cfg,), new_movers))

        checked += 1

    print(f"\n  Results for n={n}:")
    print(f"  Configs checked: {checked}")
    print(f"  Total qualifying cycles: {cycle_count}")
    print(f"  With isolated ri firings: {isolated_count}")
    print(f"  Odd-parity residual: {odd_parity_count}")
    print(f"  Odd + EC: {odd_with_ec_count}")
    print(f"  Odd + NO EC: {odd_no_ec_count}")

    if odd_parity_count == 0:
        print(f"  >>> ODD-PARITY CASE IS VACUOUS at n={n}")
    elif odd_no_ec_count == 0:
        print(f"  >>> ALL odd-parity cycles have EC at n={n}")

if __name__ == '__main__':
    focused_investigation()
