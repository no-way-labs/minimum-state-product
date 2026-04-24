"""
Investigate isolated sandwiched ternary pivots at n=9 with P=2.
ms = (3,3,2,2,3,2,2,3,3), pivot at position 4.

Positions:
  0(3) 1(3) 2(2) 3(2) 4(3) 5(2) 6(2) 7(3) 8(3)
  left4t left3t left2t leftt pivot rightt right2t right3t right4t

Pivot fires P=2 times. "Phase" = interval between consecutive pivot firings.
"All contaminated" (Case 3): every phase has interior left2t(pos2) or right2t(pos6) firing.
"Tight left" (Case 1): left2t fires at boundary (just before/after pivot), left2t silent in interior.
"Tight right" (Case 2): symmetric for right2t.

We enumerate good cycles, check fire counts, phase structure, and entry conflicts.
"""

import itertools
from collections import defaultdict

def run():
    ms = [3, 3, 2, 2, 3, 2, 2, 3, 3]
    n = 9
    pivot = 4
    product = 1
    for m in ms:
        product *= m
    print(f"ms = {ms}, n = {n}, product = {product}")
    print(f"Pivot at pos {pivot}, m_pivot = {ms[pivot]}")
    print(f"Positions: " + ", ".join(f"{i}({ms[i]})" for i in range(n)))
    print()

    # Generate all configs
    all_configs = list(itertools.product(*(range(m) for m in ms)))
    print(f"Total configs: {len(all_configs)}")

    # Good config: exactly one privileged processor
    # Privileged: f(L,S,R) != S. For token ring, use incrementing: f(L,S,R) = (S+1)%m if L==S else S
    # Actually we need to enumerate good cycles abstractly - via mover words.
    # A good cycle is a sequence of configs where each has exactly 1 privileged proc,
    # and firing that proc gives the next config.

    # For enumeration: build the good-config graph.
    # Config c is good if exactly 1 proc is privileged under ALL possible transition functions.
    # But we don't have a fixed system - we want to enumerate ALL possible good cycles
    # for ANY system with these ms.

    # Actually, the question is about good cycles in the abstract sense:
    # A good cycle is a cyclic sequence of (config, mover) pairs where:
    # - Each config has the mover privileged
    # - Firing the mover changes config[mover] to some new value != old value
    # - The resulting config is the next in the sequence
    # - Each proc fires exactly m_i times (for minimum-length cycles)

    # For tractability, let's directly enumerate good cycles by DFS.
    # A good cycle visits each config exactly once? No - it visits product/n configs
    # if it's a Hamiltonian good cycle... actually good cycles can vary in length.

    # Let me think about this differently. We want cycles where:
    # - fc(pivot) = 2 (pivot fires exactly twice)
    # - The cycle visits configs, at each step one proc fires
    # - Each proc fires at least m_i times (to return to original state)

    # For large state spaces, full enumeration is infeasible.
    # Let's focus on the LOCAL structure around the pivot.

    # Better approach: enumerate mover words (sequence of which proc fires)
    # with the constraint that each proc fires exactly m_i times,
    # then check which mover words can be realized as good cycles.

    # But product = 3*3*2*2*3*2*2*3*3 = 5832, cycle length = sum(m_i) = 23.
    # Mover words of length 23 with fc constraints... still huge.

    # Let's use a more targeted approach:
    # Build the successor graph on configs where exactly one proc is privileged,
    # using a specific transition function family.

    # For concreteness, use incrementing transitions: f_i(L,S,R) = (S+1)%m_i
    # Privileged iff L == S (Dijkstra-style).

    # Actually for general investigation, let's try multiple transition styles.
    # Start with the standard Dijkstra criterion.

    print("=== Using Dijkstra-style privilege: proc i privileged iff c[i-1] == c[i] ===")
    print("=== Transition: c[i] -> (c[i]+1) % m_i ===")
    print()

    def is_privileged_dijkstra(config, i):
        """Proc i is privileged iff left neighbor equals self."""
        L = config[(i - 1) % n]
        S = config[i]
        return L == S

    def get_privileged(config):
        return [i for i in range(n) if is_privileged_dijkstra(config, i)]

    def fire(config, i):
        lst = list(config)
        lst[i] = (lst[i] + 1) % ms[i]
        return tuple(lst)

    # Find good configs (exactly 1 privileged)
    good_configs = []
    for c in all_configs:
        priv = get_privileged(c)
        if len(priv) == 1:
            good_configs.append((c, priv[0]))

    print(f"Good configs (exactly 1 privileged): {len(good_configs)}")

    # Build successor graph on good configs
    good_set = {c for c, _ in good_configs}
    good_mover = {c: m for c, m in good_configs}

    # Find all good cycles by following the successor chain
    succ = {}
    for c, m in good_configs:
        c2 = fire(c, m)
        if c2 in good_set:
            succ[c] = (c2, m)

    # Find cycles in successor graph
    visited = set()
    cycles = []
    for start in good_set:
        if start in visited or start not in succ:
            continue
        path = []
        cur = start
        path_set = set()
        while cur not in path_set and cur in succ:
            if cur in visited:
                break
            path_set.add(cur)
            path.append(cur)
            cur = succ[cur][0]
        else:
            if cur in path_set:
                # Found a cycle
                cycle_start = path.index(cur)
                cycle = path[cycle_start:]
                movers = [good_mover[c] for c in cycle]
                cycles.append((cycle, movers))
                for c in cycle:
                    visited.add(c)
            continue
        for c in path:
            visited.add(c)

    print(f"Found {len(cycles)} good cycle(s)")

    for ci, (cycle, movers) in enumerate(cycles):
        print(f"\nCycle {ci}: length {len(cycle)}")
        # Fire counts
        fc = defaultdict(int)
        for m in movers:
            fc[m] += 1
        fc_str = ", ".join(f"p{i}:{fc[i]}" for i in range(n) if fc[i] > 0)
        print(f"  Fire counts: {fc_str}")
        print(f"  fc(pivot={pivot}) = {fc[pivot]}")

    # Now let's also try a more general approach: enumerate ALL possible good cycles
    # by DFS on config space with any privilege rule that gives exactly 1 privileged.
    # This is the "abstract" approach - any transition function.

    # For the abstract approach, a good cycle is determined by:
    # 1. A mover sequence (which proc fires at each step)
    # 2. A starting config
    # 3. At each step, config[mover] changes to a NEW value (not equal to current)
    # 4. After the full cycle, we return to start

    # Since ms are small, let's enumerate by building the abstract good-cycle graph.
    # At each step, the mover fires and their value changes.
    # The constraint is: after sum(ms) steps with each proc i firing m_i times,
    # we return to start.

    # Actually, let's be more careful. Minimum cycle length has each proc firing
    # exactly m_i times (visiting all m_i values). But cycles can be longer.
    # For the P=2 constraint, we want fc(pivot) = 2, not 3.
    # Since m_pivot = 3, fc(pivot) = 2 means pivot does NOT complete a full tour.
    # Wait - fc(pivot)=2 means pivot fires exactly 2 times. For it to return to
    # its original value with 2 firings out of m=3, the two transitions must
    # form a 2-step path that doesn't return (0->a->b, b != 0).
    # Actually for a CYCLE we need the pivot to return to its start value.
    # With incrementing: 0->1->2 (2 firings, end at 2, not back to 0).
    # So fc(pivot)=2 is NOT possible with incrementing if we need to return!
    # Unless the transition is not incrementing.

    # With m=3 and fc=2: need val after 2 firings = start val.
    # Possible transitions: 0->1->0 (dec then inc?), 0->2->0, etc.
    # This requires non-incrementing transitions at the pivot.

    # So the Dijkstra incrementing model won't give fc(pivot)=2 for m=3.
    # We need to use abstract mover words with arbitrary transitions.

    print("\n" + "="*70)
    print("=== Abstract good cycle enumeration (any transition function) ===")
    print("="*70)

    # For abstract cycles, we track:
    # - mover word (sequence of positions)
    # - config trajectory (sequence of full configs)
    # - Each firing changes exactly the mover's value to something different
    # - Cycle: return to start after L steps

    # Constraint: fc(pivot) = 2, and we want "reasonable" cycle lengths.
    # Minimum cycle length with fc constraints:
    # Each binary proc fires >= 2 times, each ternary proc fires >= 2 times (if fc=2)
    # or >= 3 times. For a full cycle, each proc must return to start value.
    # With m=2: must fire even number of times (min 2).
    # With m=3 and fc=2: value sequence v0->v1->v2=v0, so must have v2=v0.
    #   This means after 2 firings, return to start. Possible iff transition
    #   function allows a 2-cycle on {0,1,2}. E.g., 0->1->0 or 0->2->0.
    # With m=3 and fc=3: standard full tour 0->1->2->0.

    # For our setup: pivot has fc=2, all others have fc >= m_i.
    # But to minimize, let's set:
    # - Binary procs (pos 2,3,5,6): fc = 2
    # - Ternary procs (pos 0,1,7,8): fc = 3
    # - Pivot (pos 4, m=3): fc = 2
    # Total cycle length = 4*2 + 4*3 + 2 = 22

    # Wait, can ternary have fc=2? Yes if they do a 2-cycle on their values.
    # Min fc for m=3 to return: 2 (via 2-cycle) or 3 (full tour).
    # Let's allow fc=2 for ternary too.
    # Total with all fc=2: 9*2 = 18. With ternary fc=3: varies.

    # The question says P=2 meaning fc(pivot)=2.
    # For other procs, fc is determined by the cycle structure.
    # Let's enumerate mover words with various fc distributions.

    # Due to combinatorial explosion, let's focus on small targeted checks.
    # Key insight: we only need to check the LOCAL structure around pivot.

    # Let me enumerate abstractly by DFS.
    # State: (config, step_count, movers_so_far)
    # Too expensive for full space.

    # Alternative: enumerate mover words first, then check realizability.
    # A mover word is a sequence of processor indices.
    # For a cycle, the config must return to start.

    # Let's enumerate mover words of length L with fc(pivot)=2,
    # and for each check if any starting config gives a valid cycle.

    # For efficiency, let's work with a RESTRICTED region around pivot.
    # Focus on positions 1,2,3,4,5,6,7 (the pivot and its 3 neighbors on each side).

    # Actually, let's just brute-force enumerate all good cycles for a SMALL
    # subsystem to understand the structure. But n=9 is too large.

    # NEW APPROACH: Use the abstract framework.
    # For each proc i, the value sequence during its firings is a permutation cycle
    # on {0,...,m_i-1}. With fc(i)=k, it's a k-cycle (possibly with repeats if k>m_i).
    # For fc=m_i, it's a full tour of all values.
    # For fc=2, m=3: it's a 2-cycle, e.g., 0->1->0.

    # The key question is about BOUNDARY TRIPLES at pos 2 when pos 1 fires
    # vs when pos 2 fires (in the same phase).

    # Let me reformulate: In any good cycle with fc(4)=2:
    # - The 2 pivot firings divide the cycle into 2 phases.
    # - In each phase, various procs fire.
    # - "All contaminated" means both phases have pos 2 or pos 6 firing in their interior.

    # For the EC check: when pos 1 fires, the boundary triple at pos 2 is
    # (c[1], c[2], c[3]). When pos 2 fires (in the same phase), the boundary
    # triple at pos 2 is also (c[1], c[2], c[3]) but at that moment.
    # EC occurs if these triples match but the required transition differs.

    # Let me enumerate concretely. I'll build the full config space and find
    # all good cycles by graph search. Good config = exactly 1 proc wants to move.

    # For abstract good cycles (transition-function-independent):
    # At each config, exactly one proc is "privileged" = the mover.
    # The mover's value changes to some other value.
    # We don't fix the transition function; we just track configs.

    # Approach: BFS/DFS on (config, start_config) tracking the mover sequence.
    # A "step" is: choose a mover i, choose a new value v != config[i] for that proc.
    # The new config must have exactly one proc wanting to move (but we don't have
    # a fixed rule for who wants to move - that's what the transition function determines).

    # In fact, for ABSTRACT good cycles, any mover word + config trajectory where:
    # 1. At each step, exactly one proc changes value
    # 2. The changed value is different from the previous
    # 3. We return to start
    # ... is a valid good cycle for SOME transition function.

    # So the question reduces to: for mover words with the right structure,
    # can we always find an entry conflict?

    # Let me enumerate mover words with fc(4)=2 and check the phase structure
    # and boundary triple sharing.

    # APPROACH: Enumerate all valid mover words of the minimum length,
    # then for each, symbolically track which boundary triples must match.

    # For min cycle length with fc(4)=2:
    # Binary procs (2,3,5,6): fc=2 (minimum, must return to start with m=2)
    # Ternary procs (0,1,7,8): fc>=2 to return. fc=2 means 2-cycle (OK for m=3).
    #   fc=3 means full tour. Both are valid.
    # Pivot (4, m=3): fc=2.
    # Min total: 9*2 = 18.

    # But the question specifically says fc(left2t)=2, fc(right2t)=2.
    # So binary procs have fc=2 (forced), and we can have fc=2 or fc=3 for ternary.

    # Let me focus on the minimum case: all fc=2. Cycle length = 18.
    # Mover words: sequences of length 18 where each proc appears exactly 2 times.

    # The 2 pivot firings at positions p1, p2 divide the word into 2 phases.
    # Phase 1: steps p1+1 to p2-1. Phase 2: steps p2+1 to p1-1 (cyclic).

    # "All contaminated": both phases contain pos 2 or pos 6 in their interior.

    # For the EC at pos 2: when pos 1 fires in a phase, and pos 2 fires in the same phase,
    # do they see the same boundary triple at pos 2?

    # The boundary triple at pos 2 = (c[1], c[2], c[3]).
    # Between pos 1's firing and pos 2's firing (in the same phase),
    # c[1] changes (pos 1 just fired), c[2] hasn't fired yet (or has),
    # c[3] may or may not have fired.

    # Actually, the triple at pos 2 when pos 1 fires:
    # - This is the config JUST BEFORE pos 1 fires (pos 1 is the mover)
    # - Triple at pos 2 = (c[1], c[2], c[3]) = context that pos 2 "sees"
    # - But pos 2 is NOT the mover here; pos 1 is.
    # - For EC: we need pos 2's context to be the same when it's a NON-MOVER
    #   as when it IS the mover, but requiring different outputs.

    # Let me re-read the question more carefully.
    # "does the left³t-firing step always share a boundary triple with the left²t-mover step"
    # At the left³t-firing step: pos 1 fires, and pos 2 is a non-mover.
    #   The boundary triple at pos 2 is (c[1], c[2], c[3]).
    #   Since pos 2 is not firing, the transition function must give f(c[1],c[2],c[3]) = c[2].
    # At the left²t-mover step: pos 2 fires.
    #   The boundary triple at pos 2 is (c'[1], c'[2], c'[3]).
    #   Since pos 2 IS firing, f(c'[1],c'[2],c'[3]) != c'[2].
    # EC occurs if (c[1],c[2],c[3]) == (c'[1],c'[2],c'[3]):
    #   then f must equal c[2] AND not equal c[2], contradiction.

    # So the question is: when pos 1 fires and when pos 2 fires (in same phase),
    # is the triple (c[1],c[2],c[3]) the same at both moments?

    # For this to happen:
    # - c[2] must be the same (pos 2 hasn't fired between the two events)
    # - c[1] and c[3] must be the same at both moments.

    # If pos 1 fires BEFORE pos 2 in the phase: c[1] changes at pos 1's firing,
    #   so c[1] is DIFFERENT at pos 2's step. Unless pos 1 fires again between.
    #   But fc(1)=2 total, and we're in one phase, so pos 1 fires at most once per phase.
    #   So c[1] at pos 2's firing = c[1] after pos 1 fired = new value of pos 1.
    #   While c[1] at pos 1's firing = old value of pos 1.
    #   These differ → no EC from this ordering.

    # If pos 2 fires BEFORE pos 1 in the phase: c[1] is unchanged between pos 2
    #   and pos 1 (unless something else changes pos 1, but only pos 1 can change pos 1).
    #   Wait - between pos 2 firing and pos 1 firing, has pos 1 already changed?
    #   In this ordering: pos 2 fires first, then pos 1 fires later.
    #   At pos 2's firing: triple = (c[1], c[2], c[3]) with current c[1].
    #   At pos 1's firing: triple at pos 2 = (c[1], c[2]_new, c[3]_maybe_new).
    #   c[2] HAS changed (pos 2 already fired), so triple differs → no EC.

    # Hmm, so in a single phase, if pos 1 and pos 2 each fire once,
    # the triple at pos 2 always differs between the two events because
    # either c[1] or c[2] has changed. Let me verify this more carefully.

    # CASE A: pos 1 fires at step s1, pos 2 fires at step s2, s1 < s2 (same phase).
    # At step s1: triple_2 = (c[1]_old, c[2]_current, c[3]_current). Pos 1 fires → c[1] changes.
    # At step s2: triple_2 = (c[1]_new, c[2]_current, c[3]_??).
    # c[1]_new != c[1]_old (pos 1 fired and changed). So triples differ in first component.
    # UNLESS c[3] also changed to compensate? No, the first component differs regardless.
    # So NO EC from this case.

    # CASE B: pos 2 fires at step s2, pos 1 fires at step s1, s2 < s1 (same phase).
    # At step s2: triple_2 = (c[1]_current, c[2]_old, c[3]_current). Pos 2 fires → c[2] changes.
    # At step s1: triple_2 = (c[1]_current_maybe, c[2]_new, c[3]_??).
    # c[2]_new != c[2]_old (pos 2 fired and changed). So triples differ in second component.
    # Again NO EC.

    # Wait, this seems to say EC is IMPOSSIBLE when pos 1 and pos 2 fire in the same phase!
    # Because one of {c[1], c[2]} necessarily changes between the two events.

    # But the question asks about DIFFERENT phases too? No, it says "same phase".
    # And cross-phase: if pos 1 fires in phase 1 and pos 2 fires in phase 2,
    # then many things can change between.

    # Hmm, but the original question says "the left³t-firing step always shares a
    # boundary triple with the left²t-mover step, giving entry conflict at left²t".
    # Maybe the intended mechanism is cross-phase?

    # Or maybe I'm wrong about the "always differs" argument. Let me think again.
    # The triple at pos 2 when pos 1 fires: (c[1]_before_firing, c[2], c[3]).
    # Actually wait - at the step where pos 1 fires, the CONFIG is the one BEFORE
    # pos 1 changes. So the triple at pos 2 = (c[1]_old, c[2], c[3]).
    # After pos 1 fires, c[1] becomes c[1]_new.

    # At the step where pos 2 fires (later in same phase, s2 > s1):
    # Config at that moment has c[1] = c[1]_new (changed by pos 1).
    # Triple at pos 2 = (c[1]_new, c[2], c[3]').
    # First component differs. So triples differ. Confirmed: no EC.

    # At the step where pos 2 fires (earlier in same phase, s2 < s1):
    # Config has c[2] = c[2]_old. Triple = (c[1]', c[2]_old, c[3]').
    # After pos 2 fires, c[2] = c[2]_new.
    # At pos 1's step: triple = (c[1]'', c[2]_new, c[3]'').
    # Second component differs. No EC.

    # So same-phase EC between adjacent procs is IMPOSSIBLE!
    # The firing of one always changes a component of the other's triple.

    # This is actually a FUNDAMENTAL observation. Let me verify computationally.

    print("\n" + "="*70)
    print("=== FUNDAMENTAL CHECK: Same-phase EC between adjacent procs ===")
    print("="*70)
    print()
    print("ANALYTICAL ARGUMENT:")
    print("When pos j fires and pos j+1 fires in the same phase:")
    print("  If j fires first: c[j] changes, so triple at j+1 = (c[j],...) differs")
    print("  If j+1 fires first: c[j+1] changes, so triple at j+1 = (...,c[j+1],...) differs")
    print("In both cases, the boundary triple at j+1 MUST differ between the two steps.")
    print("Therefore, same-phase EC between pos j and pos j+1 is IMPOSSIBLE.")
    print("(The triple at j+1 has c[j] and c[j+1] as its first two components.)")
    print()
    print("This means the question's proposed mechanism CANNOT work as stated.")
    print()

    # Let me now check what the actual EC mechanisms are for this geometry.
    # The EC must come from NON-ADJACENT procs, or from cross-phase comparisons.

    # Let's do a COMPUTATIONAL check: enumerate all abstract good cycles
    # for a small version of this geometry and look for EC.

    # For tractability, let's use n=5 with similar structure:
    # ms = (3, 2, 3, 2, 3), pivot at pos 2, isolated (pos 0 is non-binary)
    # Hmm, but we need the specific geometry. Let me just verify the analytical
    # argument computationally on actual good cycles.

    # Use Dijkstra-style with DECREMENTING (to allow fc=2 for ternary):
    # f_i(L,S,R) = (S-1)%m if L==S else S → fires to (S-1)%m
    # Actually this still has fc=m for full tour.

    # Let me use a different approach: build ALL valid systems for a small case
    # and check good cycles for EC properties.

    # For n=5, ms=(3,2,3,2,3), product = 108.
    # This is small enough to enumerate.

    print("="*70)
    print("=== Computational verification on n=5, ms=(3,2,3,2,3) ===")
    print("="*70)

    ms5 = [3, 2, 3, 2, 3]
    n5 = 5
    prod5 = 1
    for m in ms5:
        prod5 *= m
    print(f"ms = {ms5}, product = {prod5}")

    all_c5 = list(itertools.product(*(range(m) for m in ms5)))

    # For each possible good cycle (abstract), we track configs and movers.
    # A good cycle is a cycle in the config graph where each step changes
    # exactly one proc's value.

    # Build the graph: nodes = configs, edges = (config, new_config, mover)
    # where new_config differs from config in exactly position mover,
    # and new_config[mover] != config[mover].

    # Find all cycles in this graph where at each node, the mover is determined
    # (i.e., only one proc can fire = the cycle is a good cycle for some TF).

    # This is still too broad. Let me focus on cycles with specific fc constraints.
    # For fc(pivot=2)=2 at n=5:

    # Instead, let me just verify the analytical argument with a concrete example.
    print()
    print("=== Verifying analytical argument with concrete example ===")
    print()

    # Consider a cycle fragment in one phase:
    # ... [pivot fires] ... pos1 fires ... pos2 fires ... [pivot fires] ...
    # or
    # ... [pivot fires] ... pos2 fires ... pos1 fires ... [pivot fires] ...

    # Example config at pivot firing: c = (a, b, x, y, z, ..., w)
    # Phase starts after pivot fires.

    # Case: pos 1 fires before pos 2 in a phase.
    # At pos 1's step: config has c[1]=b_old. Triple at pos 2 = (b_old, c[2], c[3]).
    # Pos 1 fires: c[1] -> b_new != b_old.
    # At pos 2's step: triple at pos 2 = (b_new, c[2], c[3]).
    # Since b_new != b_old, triples differ in first component. QED.

    # But wait: could other procs fire between pos 1 and pos 2 and change c[3]?
    # Yes! But c[1] still differs, so the triples still differ. The FIRST component
    # is what matters.

    # Case: pos 2 fires before pos 1 in a phase.
    # At pos 2's step: triple at pos 2 = (c[1], c[2]_old, c[3]).
    # Pos 2 fires: c[2] -> c[2]_new != c[2]_old.
    # At pos 1's step: triple at pos 2 = (c[1]?, c[2]_new, c[3]?).
    # The SECOND component differs. QED.

    print("The analytical argument holds regardless of what other procs do between steps.")
    print("The key insight: if procs j and j+1 both fire in the same phase,")
    print("the boundary triple at j+1 = (c[j], c[j+1], c[j+2]) necessarily differs")
    print("between their firing steps, because one of c[j] or c[j+1] changes.")
    print()

    # Now let's check the broader question: do Cases 1 and 2 occur?
    # Case 1: "tight left" - left2t fires only at phase boundary (adjacent to pivot firing)
    # Case 2: "tight right" - symmetric
    # Case 3: all contaminated

    # For Case 1/2 to apply: left2t is "silent in interior" meaning it fires
    # right before or right after the pivot. This means in the mover word,
    # pos 2 appears adjacent to a pivot occurrence.

    # With fc(pos2)=2 and fc(pivot)=2, if both pos 2 firings are adjacent to
    # pivot firings (one before, one after), then pos 2 is "tight".

    # The question is whether this can happen for isolated pivots.
    # "Isolated" means left4t (pos 0) is non-binary.

    # This is about mover word structure, which depends on the transition function.
    # For ANY transition function giving a good cycle with these fc constraints,
    # can we always find EC?

    # Let me now do a more DIRECT computational approach.
    # Generate all good cycles for a small system and classify them.

    print("="*70)
    print("=== Direct computational search: n=5 analog ===")
    print("="*70)
    print()

    # Use ms = (3, 3, 2, 3, 2) with pivot at pos 3 (ternary, sandwiched).
    # Wait, we need isolated sandwiched. Let me pick:
    # ms = (3, 3, 2, 2, 3), pivot at pos 4... no that's at the edge.
    # For n=5 ring: positions 0,1,2,3,4.
    # Pivot at pos 2, ms = (3, 3, 2, 2, 3).
    # left2t=pos 0, left_t=pos 1, pivot=pos 2, right_t=pos 3, right2t=pos 4.
    # Isolated: left3t would be pos (0-1)%5=4, but that's right2t. Ring wraps.
    # n=5 is too small for isolated sandwiched - the "isolation" condition
    # requires left4t to exist and be non-binary.

    # Let me just work with n=9 directly but use SAMPLING.
    # Generate random transition functions for ms=(3,3,2,2,3,2,2,3,3),
    # build the system, find good cycles, and check properties.

    print("="*70)
    print("=== Direct search on n=9, ms=(3,3,2,2,3,2,2,3,3) ===")
    print("="*70)
    print()

    import random
    random.seed(42)

    ms9 = [3, 3, 2, 2, 3, 2, 2, 3, 3]
    n9 = 9
    prod9 = 1
    for m in ms9:
        prod9 *= m
    print(f"ms = {ms9}, product = {prod9}")

    all_c9 = list(itertools.product(*(range(m) for m in ms9)))
    print(f"Total configs: {len(all_c9)}")

    # For each random transition function, find good configs and cycles
    def random_transition(ms, n):
        """Generate random transition functions for each proc."""
        fs = []
        for i in range(n):
            m_L = ms[(i-1) % n]
            m_S = ms[i]
            m_R = ms[(i+1) % n]
            table = {}
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        table[(L, S, R)] = random.randint(0, m_S - 1)
            fs.append(lambda L, S, R, t=table: t[(L, S, R)])
        return fs

    def find_good_cycles_from_system(ms, fs, max_cycles=100):
        """Find good cycles in a system by following successor chains."""
        n = len(ms)
        all_configs_list = list(itertools.product(*(range(m) for m in ms)))

        # Find good configs
        good = {}  # config -> mover
        for c in all_configs_list:
            priv = []
            for i in range(n):
                L = c[(i-1) % n]
                S = c[i]
                R = c[(i+1) % n]
                if fs[i](L, S, R) != S:
                    priv.append(i)
            if len(priv) == 1:
                good[c] = priv[0]

        # Build successor graph
        succ = {}
        for c, m in good.items():
            lst = list(c)
            L = c[(m-1) % n]
            S = c[m]
            R = c[(m+1) % n]
            lst[m] = fs[m](L, S, R)
            c2 = tuple(lst)
            if c2 in good:
                succ[c] = (c2, m)

        # Find cycles
        visited = set()
        cycles = []
        for start in good:
            if start in visited or start not in succ:
                continue
            path = []
            path_set = set()
            cur = start
            while cur not in path_set and cur in succ and cur not in visited:
                path_set.add(cur)
                path.append(cur)
                cur = succ[cur][0]
            if cur in path_set:
                ci = path.index(cur)
                cycle_configs = path[ci:]
                cycle_movers = [good[c] for c in cycle_configs]
                cycles.append((cycle_configs, cycle_movers))
                for c in cycle_configs:
                    visited.add(c)
            else:
                for c in path:
                    visited.add(c)
            if len(cycles) >= max_cycles:
                break

        return cycles

    # Search for systems with good cycles having fc(4)=2
    n_trials = 200
    found_fc2 = 0
    all_contaminated_cycles = []
    case1_cycles = []
    case2_cycles = []
    ec_found = 0
    ec_checked = 0

    print(f"Running {n_trials} random trials...")

    for trial in range(n_trials):
        fs = random_transition(ms9, n9)
        cycles = find_good_cycles_from_system(ms9, fs)

        for cycle_configs, cycle_movers in cycles:
            L = len(cycle_configs)
            fc = defaultdict(int)
            for m in cycle_movers:
                fc[m] += 1

            if fc[4] != 2:
                continue

            found_fc2 += 1

            # Find pivot firing positions
            pivot_steps = [i for i, m in enumerate(cycle_movers) if m == 4]
            if len(pivot_steps) != 2:
                continue

            # Define phases
            p1, p2 = pivot_steps
            # Phase 1: steps after p1 until p2 (exclusive)
            # Phase 2: steps after p2 until p1 (cyclic)
            phase1_steps = [(p1 + 1 + k) % L for k in range(((p2 - p1 - 1) % L))]
            phase2_steps = [(p2 + 1 + k) % L for k in range(((p1 - p2 - 1) % L))]

            phase1_movers = [cycle_movers[s] for s in phase1_steps]
            phase2_movers = [cycle_movers[s] for s in phase2_steps]

            # Check contamination: each phase has pos 2 or pos 6 in interior
            phase1_has_2or6 = (2 in phase1_movers) or (6 in phase1_movers)
            phase2_has_2or6 = (2 in phase2_movers) or (6 in phase2_movers)

            # Case classification
            # "Interior" firing of pos 2 = pos 2 fires in the phase (not at boundary with pivot)
            pos2_in_phase1 = 2 in phase1_movers
            pos2_in_phase2 = 2 in phase2_movers
            pos6_in_phase1 = 6 in phase1_movers
            pos6_in_phase2 = 6 in phase2_movers

            # Tight left (Case 1): pos 2 NOT in any phase interior
            # (fires only at phase boundaries = adjacent to pivot)
            pos2_interior = pos2_in_phase1 or pos2_in_phase2
            pos6_interior = pos6_in_phase1 or pos6_in_phase2

            if not pos2_interior:
                case1_cycles.append((cycle_configs, cycle_movers, fc, trial))
            if not pos6_interior:
                case2_cycles.append((cycle_configs, cycle_movers, fc, trial))
            if phase1_has_2or6 and phase2_has_2or6:
                all_contaminated_cycles.append((cycle_configs, cycle_movers, fc, trial))

            # Now check for EC at pos 2 in all contaminated case
            if phase1_has_2or6 and phase2_has_2or6:
                ec_checked += 1
                has_ec = False

                # Check each phase for EC at pos 2
                for phase_steps in [phase1_steps, phase2_steps]:
                    phase_movers_list = [(s, cycle_movers[s]) for s in phase_steps]

                    # Find pos 1 firing steps and pos 2 firing steps in this phase
                    pos1_steps_in_phase = [s for s, m in phase_movers_list if m == 1]
                    pos2_steps_in_phase = [s for s, m in phase_movers_list if m == 2]

                    for s1 in pos1_steps_in_phase:
                        for s2 in pos2_steps_in_phase:
                            # Triple at pos 2 when pos 1 fires (step s1)
                            c_at_s1 = cycle_configs[s1]
                            triple_s1 = (c_at_s1[1], c_at_s1[2], c_at_s1[3])

                            # Triple at pos 2 when pos 2 fires (step s2)
                            c_at_s2 = cycle_configs[s2]
                            triple_s2 = (c_at_s2[1], c_at_s2[2], c_at_s2[3])

                            if triple_s1 == triple_s2:
                                has_ec = True

                # Also check for EC from OTHER sources (non-adjacent procs)
                # Check all pairs of (non-mover step, mover step) at any position
                any_ec = False
                for pos in range(n9):
                    mover_steps = [i for i, m in enumerate(cycle_movers) if m == pos]
                    nonmover_steps = [i for i, m in enumerate(cycle_movers) if m != pos]

                    for sm in mover_steps:
                        cm = cycle_configs[sm]
                        triple_m = (cm[(pos-1)%n9], cm[pos], cm[(pos+1)%n9])
                        for snm in nonmover_steps:
                            cnm = cycle_configs[snm]
                            triple_nm = (cnm[(pos-1)%n9], cnm[pos], cnm[(pos+1)%n9])
                            if triple_m == triple_nm:
                                any_ec = True
                                break
                        if any_ec:
                            break
                    if any_ec:
                        break

                if has_ec:
                    ec_found += 1

    print(f"\nResults from {n_trials} trials:")
    print(f"  Good cycles with fc(pivot)=2: {found_fc2}")
    print(f"  Case 1 (tight left, pos2 not in interior): {len(case1_cycles)}")
    print(f"  Case 2 (tight right, pos6 not in interior): {len(case2_cycles)}")
    print(f"  Case 3 (all contaminated): {len(all_contaminated_cycles)}")
    print(f"  EC checked (Case 3): {ec_checked}")
    print(f"  EC at pos 2 from pos1-fires-then-pos2 (same phase): {ec_found}")
    print()

    # Now verify the analytical argument: same-phase EC between adjacent procs
    print("="*70)
    print("=== Verifying: adjacent-proc same-phase EC is impossible ===")
    print("="*70)
    print()

    adj_ec_count = 0
    adj_checked = 0
    for cycle_configs, cycle_movers, fc, trial in all_contaminated_cycles:
        L = len(cycle_configs)
        pivot_steps = [i for i, m in enumerate(cycle_movers) if m == 4]
        p1, p2 = pivot_steps

        phase1_steps = [(p1 + 1 + k) % L for k in range(((p2 - p1 - 1) % L))]
        phase2_steps = [(p2 + 1 + k) % L for k in range(((p1 - p2 - 1) % L))]

        for phase_steps in [phase1_steps, phase2_steps]:
            phase_movers_list = [(s, cycle_movers[s]) for s in phase_steps]

            # Check all adjacent pairs
            for j in range(n9):
                j1 = (j + 1) % n9
                j_steps = [s for s, m in phase_movers_list if m == j]
                j1_steps = [s for s, m in phase_movers_list if m == j1]

                for sj in j_steps:
                    for sj1 in j1_steps:
                        adj_checked += 1
                        cj = cycle_configs[sj]
                        cj1 = cycle_configs[sj1]
                        # Triple at j+1 when j fires vs when j+1 fires
                        triple_at_j_fires = (cj[j], cj[j1], cj[(j1+1)%n9])
                        triple_at_j1_fires = (cj1[j], cj1[j1], cj1[(j1+1)%n9])
                        if triple_at_j_fires == triple_at_j1_fires:
                            adj_ec_count += 1
                            print(f"  FOUND adjacent EC! j={j}, j1={j1}, phase step pair")

    print(f"  Adjacent pairs checked: {adj_checked}")
    print(f"  Adjacent EC found: {adj_ec_count}")
    if adj_ec_count == 0:
        print("  CONFIRMED: same-phase EC between adjacent procs never occurs.")
    print()

    # Final: check what EC mechanisms DO work for these cycles
    print("="*70)
    print("=== What EC mechanisms DO kill these cycles? ===")
    print("="*70)
    print()

    # For each all-contaminated cycle, find ALL entry conflicts
    ec_sources = defaultdict(int)
    cycles_with_no_ec = 0
    total_cycles_checked = 0

    for cycle_configs, cycle_movers, fc, trial in all_contaminated_cycles[:50]:  # limit for speed
        total_cycles_checked += 1
        L = len(cycle_configs)
        found_any_ec = False

        for pos in range(n9):
            mover_steps = [i for i, m in enumerate(cycle_movers) if m == pos]
            for sm in mover_steps:
                cm = cycle_configs[sm]
                triple_m = (cm[(pos-1)%n9], cm[pos], cm[(pos+1)%n9])

                for snm in range(L):
                    if cycle_movers[snm] == pos:
                        continue  # skip mover steps for same proc
                    cnm = cycle_configs[snm]
                    triple_nm = (cnm[(pos-1)%n9], cnm[pos], cnm[(pos+1)%n9])
                    if triple_m == triple_nm:
                        # Entry conflict at pos
                        ec_sources[pos] += 1
                        found_any_ec = True
                        break
                if found_any_ec:
                    break
            if found_any_ec:
                break

        if not found_any_ec:
            cycles_with_no_ec += 1

    print(f"Checked {total_cycles_checked} all-contaminated cycles")
    print(f"Cycles with NO entry conflict anywhere: {cycles_with_no_ec}")
    print(f"EC sources by position:")
    for pos in sorted(ec_sources.keys()):
        print(f"  pos {pos}: {ec_sources[pos]} cycles killed")

    print()
    print("="*70)
    print("=== SUMMARY ===")
    print("="*70)
    print()
    print("1. ANALYTICAL RESULT: Same-phase EC between adjacent procs j and j+1")
    print("   is IMPOSSIBLE. When j fires, c[j] changes; when j+1 fires, c[j+1]")
    print("   changes. Either way, the boundary triple at j+1 differs between")
    print("   the two firing steps. This kills the proposed mechanism.")
    print()
    print("2. The left³t-firing step CANNOT share a boundary triple with the")
    print("   left²t-mover step IN THE SAME PHASE, because they are adjacent")
    print("   (left³t = pos 1, left²t = pos 2).")
    print()
    print("3. Cases 1/2/3 classification and EC mechanisms need to come from")
    print("   NON-ADJACENT pairs or CROSS-PHASE comparisons.")

if __name__ == "__main__":
    run()
