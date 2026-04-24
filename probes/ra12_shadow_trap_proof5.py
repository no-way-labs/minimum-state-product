"""
Shadow Trap Proof — Part 5: The fundamental mechanism.

Key realization: The shadow cycle construction doesn't replay the same mover
sequence. Instead, it uses a PERMUTED mover sequence. The shadow permutation σ
maps each shadow step to a good-cycle step, and the mover at shadow step k
is the proc that was the mover at good-cycle step σ(k).

But the CONTEXT at the shadow config matches the context at the good-cycle
step σ(k). This is what forces the transition.

Let me understand this for the general sweep case.

SETUP:
- Good cycle: g_0, ..., g_{CL-1} with movers m_0, ..., m_{CL-1}
- Mover context at step k: proc m_k sees (L_k, S_k, R_k) and fires to S'_k
- The mover context table T: entries (m_k, L_k, S_k, R_k) -> S'_k

SHADOW CYCLE HYPOTHESIS:
- There exist non-good configs s_0, ..., s_{CL-1} and a permutation σ
  such that at s_k, proc m_{σ(k)} sees context (L_{σ(k)}, S_{σ(k)}, R_{σ(k)})
  and fires to S'_{σ(k)}, producing s_{k+1}.

This means the shadow cycle "replays" the good cycle's transitions but in
a permuted order.

For this to work:
1. At s_k, proc m_{σ(k)}'s left neighbor has value L_{σ(k)}
2. At s_k, proc m_{σ(k)} has value S_{σ(k)}
3. At s_k, proc m_{σ(k)}'s right neighbor has value R_{σ(k)}
4. Firing produces s_{k+1} = s_k with proc m_{σ(k)} changed to S'_{σ(k)}
5. s_k ∉ good cycle for all k

This is a very specific construction. Let me verify it computationally
for the case where the existing shadow formula is known, then try to
generalize.

Actually, let me take a step back. The problem says the PREVIOUS RA found
that following forced transitions from a shifted good config creates a cycle.
"Verified 512/512 at n=9." But MY experiment above found ZERO cycles with
the naive approach. So either:
(a) The shift is different (not just changing one proc)
(b) The forced-transition following uses a DIFFERENT rule
(c) I need to use the actual forced graph (pick ANY forced proc, not follow the good cycle order)

Let me try (c): follow the actual forced graph, using a scheduler.
"""

import itertools
from collections import defaultdict

def build_sweep(n, ms):
    right_order = []
    left_order = []
    for p in range(n):
        rc = (ms[p] + 1) // 2
        lc = ms[p] - rc
        right_order.extend([p] * rc)
        left_order.extend([p] * lc)
    right_order.sort()
    left_order.sort(reverse=True)

    cfg = [0] * n
    configs = [tuple(cfg)]
    movers = right_order + left_order

    for p in movers:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    if configs[-1] != configs[0]:
        return None, None
    configs = configs[:-1]
    return configs, movers

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

# Work with the KNOWN shadow cycle case: 3 binary + ternary
# From the existing code: ms = [2,2,2] + [3]*(n-3), sweep word

n = 7
ms = [2, 2, 2] + [3] * (n - 3)
CL = sum(ms)
print(f"n={n}, ms={ms}, CL={CL}, product={eval('*'.join(str(m) for m in ms))}")

# Build sweep: right (increment by 1 each) then left (decrement)
# For this specific ms, the sweep is:
# Right: proc 0 (0->1), 1 (0->1), 2 (0->1), 3 (0->1), 4 (0->1), 5 (0->1), 6 (0->1)
# Left: proc 6 (1->2), 5 (1->2), 4 (1->2), 3 (1->2), 2 (1->0), 1 (1->0), 0 (1->0)
# But binary procs only have 2 values, so they fire twice total (once up, once down)
# Ternary fire 3 times total (0->1, 1->2, 2->0)

# Actually for the known shadow cycle: uniform sweep, NB value = 1
# Right sweep: 0->n-1, each proc goes from 0 to NB (binary: 0->1, ternary: 0->1)
# Left sweep: n-1->0, each proc goes from NB to 0 (binary: 1->0, ternary: 1->2->0)

# Let me use the build_good_cycle from the existing code
def build_good_cycle_known(n, v=1):
    ms = [2, 2, 2] + [3] * (n - 3)
    config = [0] * n
    cycle_configs = [tuple(config)]
    cycle_movers = []

    # Right sweep
    for proc in range(n):
        cycle_movers.append(proc)
        config = list(cycle_configs[-1])
        config[proc] = 1 if ms[proc] == 2 else v
        cycle_configs.append(tuple(config))

    # Left sweep
    for proc in range(n - 1, -1, -1):
        cycle_movers.append(proc)
        config = list(cycle_configs[-1])
        config[proc] = 0 if ms[proc] == 2 else (config[proc] + 1) % 3  # ternary: v->v+1
        cycle_configs.append(tuple(config))

    # Wait, this doesn't return to (0,...,0) for ternary procs
    # Ternary: 0 -> v -> v+1 -> ... we need 3 firings
    # Actually a sweep has CL = sum(m_i) = 2*3 + 3*4 = 6+12 = 18 steps for n=7
    # But a right-left sweep is only 2n = 14 steps for n=7
    # So we need MORE than just right-left!

    print(f"After right+left: config = {tuple(config)}")
    print(f"Start was: {cycle_configs[0]}")
    return cycle_configs, cycle_movers, ms

cycle_configs, cycle_movers, ms = build_good_cycle_known(n)

# The cycle doesn't close with just right+left for ternary procs.
# For ternary procs, we need 3 firings each.
# The KNOWN sweep has length 2n (for 3 binary + (n-3) ternary):
# CL = 3*2 + (n-3)*3 = 6 + 3n - 9 = 3n - 3 for n >= 3
# But 2n only gives 14 firings for n=7, and we need CL = 3*7-3 = 18.
# So the sweep must have some procs firing multiple times in a row or in a pattern.

# Let me look at how the existing code actually builds the cycle
# The sweep word from cic_wiggle_symbolic_proof.py is:
# [0, 1, 2, 1, 2, 3, ..., n-1, 0, 1, ..., n-1]
# Length: 5 + (n-3) + n = 2n + 2

# But CL should be sum(m_i) = 2*3 + 3*(n-3) = 3n - 3
# And 2n + 2 = 2n + 2. These only match when 3n - 3 = 2n + 2, i.e., n = 5.
# So for n=7: CL = 18 but wiggle word length = 16. That's different!

# Wait, let me recount. fc[0]=2, fc[1]=3, fc[2]=3, fc[j]=2 for j>=3.
# Sum = 2 + 3 + 3 + 2*(n-3) = 8 + 2n - 6 = 2n + 2. OK so CL = 2n + 2.
# But ms = [2,2,2,3,...,3], so sum(ms) = 2*3 + 3*(n-3) = 3n-3.
# CL = sum of fire counts = 2n+2, which is NOT sum(ms) = 3n-3.
# Unless... the fire count is NOT ms[p] for each proc?
# In a good cycle, each proc fires exactly ms[p] times?
# For a UNIFORM sweep: word [0,1,...,n-1,n-1,...,1,0], length 2n.
# But binary procs fire 2 times (= ms), ternary fire 2 times (< ms[p]=3).
# So this is NOT a good cycle that visits all good configs.

# I think the "good cycle" here is not what I assumed.
# Let me check: how many GOOD configs does the wiggle word cycle visit?

print("\n=== Checking the wiggle word ===")
n = 8
ms_wig = [2, 2, 2] + [3] * (n - 3)  # This doesn't match wiggle fc!
# Actually: wiggle word fire counts: fc[0]=2, fc[1]=3, fc[2]=3, fc[j>=3]=2
# So the effective ms for the cycle must be: [2, 3, 3, 2, 2, ..., 2]
# But we're told ms has binary at NON-CONSECUTIVE positions!

# Let me re-read the problem...
# "non-consecutive binary" means the binary procs (m_i=2) are not adjacent.
# The wiggle word [0,1,2,1,2,3,...,n-1,0,1,...,n-1] has fc[0]=2,fc[1]=3,fc[2]=3,fc[j>=3]=2.
# So the "binary procs" (those firing 2 times) are procs 0, 3, 4, ..., n-1.
# And "ternary procs" (firing 3 times) are procs 1, 2.
# This has binary procs CONSECUTIVE (3,4,...,n-1 are all binary).
# That contradicts the "non-consecutive" requirement!

# Something is off. Let me reconsider what "binary" means.
# m_i = 2 means proc i has 2 states. In the good cycle, it fires exactly 2 times.
# m_i = 3 means proc i has 3 states. In the good cycle, it fires exactly 3 times.
# CL = sum(m_i).

# For the wiggle word: word length is 2n+2, but sum(ms) for ms=[2,2,2,3,...,3] is 3n-3.
# These don't match unless n=5 (2*5+2=12, 3*5-3=12).

# So the wiggle word is for a DIFFERENT ms vector!
# Wiggle fires: fc = [2, 3, 3, 2, 2, ..., 2].
# This means ms = [2, 3, 3, 2, 2, ..., 2].
# Binary procs: 0, 3, 4, ..., n-1.
# These ARE non-consecutive IF n >= 5 (proc 0 and proc 3 are distance 3 apart).

# Actually: proc 0 is binary. The next binary is proc 3. On the ring,
# proc 0's other neighbor is proc n-1 which is also binary.
# So 0 and n-1 are adjacent and both binary. That's CONSECUTIVE!

# Unless the ring is oriented differently. Let me check.
# 0-1-2-...-{n-1}-0. So proc 0 neighbors are n-1 and 1.
# Binary procs: {0, 3, 4, ..., n-1}. Proc 0 and n-1 are adjacent. Both binary.
# That's consecutive binary!

# I think the non-consecutive condition is for the SPECIFIC binary procs mentioned
# in the theorem: ">=3 binary processors" at non-consecutive positions.

# OK, let me just focus on the key mechanism. Let me use a concrete ms vector
# with non-consecutive binary and build the shadow cycle from scratch.

# Use the known shadow cycle for 3 CONSECUTIVE binary first, then worry about non-consecutive.
print("\n=== USING KNOWN SHADOW CONSTRUCTION ===")
n = 7
ms = [2, 2, 2, 3, 3, 3, 3]

# Build uniform sweep: right then left
# Right: 0->1->2->3->4->5->6, each fires once (goes to value 1)
# Left: 6->5->4->3->2->1->0, each fires once more
# Total firings per proc: 2 (binary) or 2 (ternary needs 3!)
# So we need an extra pass for ternary procs!

# For ms = [2,2,2,3,3,3,3], a proper good cycle:
# Must have each proc p fire exactly ms[p] times.
# Binary: fire 2 times. Ternary: fire 3 times.
# CL = 2*3 + 3*4 = 18.

# A sweep pattern: right sweep (each fires once), left sweep (each fires once),
# then another right sweep (only ternary fire once more).
# Movers: [0,1,2,3,4,5,6, 6,5,4,3,2,1,0, 3,4,5,6]

# Let's try this
movers = list(range(7)) + list(range(6, -1, -1)) + [3, 4, 5, 6]

cfg = [0] * n
configs = [tuple(cfg)]
for p in movers:
    cfg = list(configs[-1])
    cfg[p] = (cfg[p] + 1) % ms[p]
    configs.append(tuple(cfg))

print(f"After {len(movers)} steps: start={configs[0]}, end={configs[-1]}")
if configs[-1] == configs[0]:
    print("CLOSES!")
    configs = configs[:-1]
else:
    print("DOESN'T CLOSE")

    # Try: right, left, right (ternary only)
    movers2 = list(range(7)) + list(range(6, -1, -1)) + list(range(3, 7))
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers2:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))
    print(f"Attempt 2: start={configs[0]}, end={configs[-1]}")

    # Actually, for a sweep the simplest pattern is:
    # Each proc fires its values in order: 0->1->2->0 (ternary) or 0->1->0 (binary)
    # The mover word encodes which proc fires at each step.
    # For a right-left sweep with ternary, we can do:
    # Phase 1 (right): 0,1,2,3,4,5,6  (everyone 0->1)
    # Phase 2 (left): 6,5,4,3 (ternary 1->2), then 2,1,0 (binary 1->0)
    # Phase 3 (right): 3,4,5,6 (ternary 2->0)
    # Wait, ternary 2->0 = third firing. That's CL = 7 + 7 + 4 = 18. Correct!

    movers3 = list(range(7)) + [6,5,4,3] + [2,1,0] + [3,4,5,6]
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers3:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))
    print(f"Attempt 3: movers={movers3}")
    print(f"  start={configs[0]}, end={configs[-1]}")

    # Let me just build correctly:
    movers4 = list(range(7)) + list(range(6,-1,-1)) + list(range(3,7))
    # Right: all 0->1. Left: all fire again (binary 1->0, ternary 1->2).
    # Extra right: ternary 2->0.
    # But left sweep goes 6,5,...,0 and binary 2,1,0 go 1->0, while ternary go 1->2.
    # Then extra right: ternary 3,4,5,6 go 2->0.
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers4:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))
    print(f"Attempt 4: movers={movers4}")
    print(f"  start={configs[0]}, end={configs[-1]}")
    print(f"  len={len(movers4)}, expected CL={CL}")
    for i, (c, m) in enumerate(zip(configs, movers4)):
        print(f"  Step {i:2d}: {c} -> fire proc {m}")
    print(f"  Final: {configs[-1]}")
