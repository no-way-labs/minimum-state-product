"""
General phase-counting argument: Why does any valid system for n >= 5
need a processor with >= 4 distinct response patterns?

The key insight from the witness analysis: the quaternary P4's 4 states
all have DISTINCT response patterns. A "response pattern" of state s is
the function (L, R) -> f(L, s, R).

Theorem: If processor P has neighbors with m_L and m_R states respectively,
then the number of POSSIBLE distinct response patterns is m_P^(m_L * m_R).
But the number of NEEDED distinct response patterns is constrained by
the good cycle and convergence requirements.

The question: under what conditions does a processor need >= 4 distinct
response patterns?

Answer: When the processor must disambiguate >= 4 distinct "behavioral modes"
imposed by the good cycle. A behavioral mode is a (privilege_on, privilege_off)
partition of the input space.

Let's formalize this.
"""

import itertools
from collections import defaultdict

# ============================================================
# Formal framework
# ============================================================

def response_pattern(rules, proc_idx, state, m_L, m_R):
    """The response pattern of processor proc_idx in state s:
    the function (L, R) -> f(L, s, R)."""
    pattern = {}
    for L in range(m_L):
        for R in range(m_R):
            pattern[(L, R)] = rules[proc_idx][(L, state, R)]
    return tuple(sorted(pattern.items()))

def privilege_pattern(rules, proc_idx, state, m_L, m_R):
    """The privilege pattern: which (L,R) pairs make this state privileged?"""
    priv = set()
    non_priv = set()
    for L in range(m_L):
        for R in range(m_R):
            if rules[proc_idx][(L, state, R)] != state:
                priv.add((L, R))
            else:
                non_priv.add((L, R))
    return frozenset(priv), frozenset(non_priv)

# ============================================================
# The distinguishability theorem
# ============================================================

print("="*70)
print("RESPONSE PATTERN DISTINGUISHABILITY THEOREM")
print("="*70)

# n=5 witness
rules_5 = {
    0: {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
        (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,(3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
    1: {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
    2: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
        (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0},
    3: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,0,3):0,(0,1,0):1,(0,1,1):2,(0,1,2):1,(0,1,3):0,
        (0,2,0):0,(0,2,1):2,(0,2,2):2,(0,2,3):2,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,1,3):1,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
    4: {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):1,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):1,
        (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):0,(1,3,0):3,(1,3,1):0,
        (2,0,0):0,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):0,(2,3,0):3,(2,3,1):0},
}

ms_5 = [2, 2, 2, 3, 4]

print("\nn=5 witness response patterns:")
for i in range(5):
    m_L = ms_5[(i-1)%5]
    m_R = ms_5[(i+1)%5]
    patterns = set()
    for s in range(ms_5[i]):
        rp = response_pattern(rules_5, i, s, m_L, m_R)
        patterns.add(rp)
    print(f"  P{i} (m={ms_5[i]}): {len(patterns)} distinct response patterns out of {ms_5[i]} states")

# n=8 witness
rules_8 = {
    0: {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
    1: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
    2: {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
    3: {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
    4: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,(3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
    5: {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
    6: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,(2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
    7: {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
}

ms_8 = [2, 2, 3, 4, 3, 3, 2, 3]

print("\nn=8 witness response patterns:")
for i in range(8):
    m_L = ms_8[(i-1)%8]
    m_R = ms_8[(i+1)%8]
    patterns = set()
    for s in range(ms_8[i]):
        rp = response_pattern(rules_8, i, s, m_L, m_R)
        patterns.add(rp)
    print(f"  P{i} (m={ms_8[i]}): {len(patterns)} distinct response patterns out of {ms_8[i]} states")

# ============================================================
# KEY THEOREM: A processor with m states and all m distinct
# response patterns CANNOT be reduced to m-1 states.
#
# Proof: If states a and b have different response patterns,
# then there exists (L,R) such that f(L,a,R) ≠ f(L,b,R).
# Merging a and b into a single state forces f(L,merged,R) to
# have two values simultaneously — impossible for a function.
#
# Therefore: if a processor has k distinct response patterns,
# it needs at least k states. QED.
# ============================================================

print("\n" + "="*70)
print("THEOREM: RESPONSE PATTERN LOWER BOUND")
print("="*70)
print("""
THEOREM: If a processor P_i in a valid system has k distinct response
patterns across its m_i states, then m_i >= k.

PROOF: Immediate. If states a and b have different response patterns,
there exists (L, R) with f_i(L, a, R) ≠ f_i(L, b, R). Merging a and b
into one state creates an inconsistent transition function. Since no
two states with distinct patterns can be merged, at least k states
are needed. QED.

COROLLARY: In the n=5 witness, P4 has 4 distinct response patterns,
so m_4 >= 4. The quaternary is optimal.

QUESTION: Does EVERY valid system for n >= 5 have some processor
with >= 4 distinct response patterns?

This is the QUATERNARY NECESSITY CONJECTURE.
""")

# ============================================================
# Can we prove quaternary necessity for general n?
#
# Approach: Show that the good-cycle structure for n >= 5 FORCES
# some processor to need >= 4 response patterns.
#
# Key lemma: In any valid system with 3 consecutive binary
# processors B_0, B_1, B_2, the non-binary section must contain
# a processor with >= 4 response patterns.
# ============================================================

print("="*70)
print("ATTEMPT: General proof via binary block analysis")
print("="*70)

print("""
LEMMA (Binary block constraint):
Let B = (B_0, B_1, ..., B_{k-1}) be a maximal arc of consecutive binary
processors (k <= 3 by RFC). In the good cycle, the binary block visits
at least 2k distinct states in {0,1}^k (a partial Gray code).

For k=3: at least 6 states: 000, 100, 110, 111, 011, 001.

PROOF: By fairness, each B_j must move at least once. Each move flips
one bit. The block must return to its initial state. The minimum number
of bit-flips for k=3 is 6 (a cycle visiting all 3 processors at least
once in each direction).

LEMMA (Phase imposition):
The non-binary neighbor P of B (at one end of the block) sees B's
endmost processor as its L or R neighbor. Since B's endmost processor
alternates between 0 and 1 during the cycle, P sees at least 2 values
from this neighbor. But the TIMING of these values (which phase of the
binary sweep) is what matters.

For k=3: B's endmost processor changes state 2 times per sweep direction.
P sees a 0->1 transition during the rightward sweep and a 1->0 transition
during the leftward sweep. These transitions occur in DIFFERENT PHASES
of the good cycle, with different states of the non-binary processors.

CRITICAL QUESTION: Does the non-binary section need >= 4 states
somewhere to handle these phase differences?

ANSWER (partial): The non-binary section between the two ends of the
binary block forms a path P_{k}, P_{k+1}, ..., P_{n-1}, P_0, ..., P_{-1}
(going around the ring). This section must:
1. Relay the token from one end to the other (after each binary sweep)
2. Track which sweep just occurred (to prepare for the next one)
3. Handle convergence (no bad cycles)

Tracking which sweep just occurred is the PHASE COUNTING requirement.
With the binary block performing at least 2 full sweeps (one right, one
left) per good cycle, and each sweep potentially having multiple sub-phases,
the non-binary section must distinguish >= 4 macro-phases.

THE GAP: Proving that these 4 phases cannot be distributed across
multiple processors (each with <= 3 states) without creating
convergence failures. The product 3*3 = 9 >= 4, so phase counting
alone is not the bottleneck. The bottleneck is the TRANSITION STRUCTURE
of the phase tracking — the states must be connected by valid transitions,
not just available as labels.
""")

# ============================================================
# THE TRANSITION STRUCTURE ARGUMENT
#
# Key idea: the non-binary processor ADJACENT to the binary block
# (call it Q) must have a transition function that:
# (a) accepts tokens from the binary block (privileged when B changes)
# (b) sends tokens to the binary block (makes B privileged)
# (c) handles both directions
#
# For Q with m_Q states, between B (binary) and some other processor P:
# - Q sees L=B ∈ {0,1} and R=P ∈ {0,...,m_P-1}
# - When B flips (token arrives from binary block), Q must be privileged
#   and transition appropriately
# - When Q finishes processing, it must make either B or P privileged
#
# The DIRECTION of the token at Q determines whether it goes toward B
# (back into the binary block) or toward P (away from the block).
# Q must track WHICH DIRECTION the token should go.
#
# With only 2 directions and Q needing to handle both, Q needs at least
# 2 "mode" states. But Q also needs to handle multiple PHASES of the
# binary block's sweep, requiring additional states.
# ============================================================

print("="*70)
print("TRANSITION STRUCTURE OF Q (processor adjacent to binary block)")
print("="*70)

# In n=5, Q = P3 (ternary, adjacent to binary P2)
# Q sees L = P2 ∈ {0,1}, R = P4 ∈ {0,1,2,3}

# Key: Q's privilege depends on BOTH L and R.
# When the token arrives from the binary block (L changes), Q becomes privileged.
# Q's response (which state it transitions to) determines where the token goes next.

# In the good cycle for n=5:
gc = [(0,0,0,0,0),(1,0,0,0,0),(1,1,0,0,0),(1,1,1,0,0),(1,1,1,1,0),(1,1,1,1,1),
      (0,1,1,1,1),(0,0,1,1,1),(0,0,0,1,1),(0,0,0,2,1),(0,0,1,2,1),(0,0,1,0,1),
      (0,0,1,0,2),(0,0,1,2,2),(0,0,1,2,3),(0,0,1,1,3),(0,0,0,1,3),(0,0,0,0,3)]

print("\nQ = P3 (ternary) in n=5 witness:")
print("When P3 is privileged, what determines the token's next direction?")
print()

movers = []
for idx in range(len(gc)):
    c = gc[idx]
    c_next = gc[(idx+1) % len(gc)]
    for j in range(5):
        if c[j] != c_next[j]:
            movers.append(j)
            break

for idx in range(len(gc)):
    if movers[idx] == 3:
        c = gc[idx]
        L, S, R = c[2], c[3], c[4]
        new_S = rules_5[3][(L, S, R)]
        next_mover = movers[(idx+1) % len(gc)]
        direction = "→BINARY" if next_mover == 2 else ("→P4(away)" if next_mover == 4 else f"→P{next_mover}")
        print(f"  step {idx:2d}: f3({L},{S},{R})={new_S}  next=P{next_mover} {direction}")
        print(f"           P3 state: {S}->{new_S}, L(P2)={L}, R(P4)={R}")

print("""
KEY OBSERVATION: P3's decision of whether to send the token back into
the binary block (→P2) or away (→P4) depends on BOTH its own state S
AND P4's state R.

When P4 is in state 0: P3 sends token to P4 (step 3)
When P4 is in state 1: P3 alternates (sends to P2 at step 8, P4 at step 10)
When P4 is in state 2: P3 sends to P4 (step 12)
When P4 is in state 3: P3 sends to P2 (steps 14, 16)

P3 READS P4's state to decide routing. If P4 had only 3 states,
P3 couldn't distinguish all the routing cases.

This is the precise mechanism: P4's states serve as a ROUTING MEMORY
that P3 consults to determine the token's direction. Four distinct
routing decisions require 4 distinct memory states.
""")

# Verify: count the number of distinct (P3_action, based_on_P4_state) pairs
print("Distinct routing decisions by P4 state:")
from collections import defaultdict
routing_by_p4 = defaultdict(list)
for idx in range(len(gc)):
    if movers[idx] == 3:
        c = gc[idx]
        p4_state = c[4]
        next_mover = movers[(idx+1) % len(gc)]
        L, S = c[2], c[3]
        new_S = rules_5[3][(L, S, c[4])]
        routing_by_p4[p4_state].append((idx, L, S, new_S, next_mover))

for p4s in sorted(routing_by_p4):
    print(f"  P4={p4s}:")
    for (idx, L, S, new_S, nm) in routing_by_p4[p4s]:
        print(f"    step {idx}: P3({L},{S},{p4s})->{new_S}, token→P{nm}")
