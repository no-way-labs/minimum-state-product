#!/usr/bin/env python3
"""
PART 6: Understand the EXACT mechanism at chain termination.

Observation: 100% terminate at 'no_fire_first_step' with EC at bL or bR (distance 1 from t).

This means the chain ALWAYS extends through ALL procs in between, wrapping around
the ring, and terminates when it reaches the OTHER binary neighbor.

Let me verify:
1. The chain start at bR (for sorry 1121) goes through RR, RRR, ..., wrapping around
   to LL, LL, bL. At bL: first fire is at interior[0]. Next outward = t.
   t doesn't fire in the interior (it's a TernaryPhase).
   -> "No fire" at proc bL with first_idx = 0.
   EC: step a (fires t, nonmover for bL) has same triple as interior[0] (fires bL, mover).

Actually wait: EC proc at distance +-1 means bL or bR. For sorry 1121 where chain goes
RIGHT from bR: the chain goes bR -> RR -> RRR -> ... -> LL -> bL.
At bL (the last chain proc): first fire of bL is at interior[0] (bL fires first in phase).
Next outward from bL in the chain direction (-1) = t.
t doesn't fire in [0, first(bL)=0) = empty set.
So "no fire" with first_idx=0.

EC: step a fires t. bL's boundary triple at step a:
  (left(bL), bL, right(bL)) = (LL, bL, t) values at config[a].
Step interior[0] fires bL. bL's boundary triple at step interior[0]:
  (LL, bL, t) values at config[interior[0]].
Between step a and interior[0]: just ONE step (a+1 = interior[0] if no gap, but actually
a IS the t-fire, and interior starts at a+1). So interior[0] = a+1.
Config at a+1: same as config at a EXCEPT at the proc that fires at step a, which is t.
So bL's boundary values: (LL, bL, t).
LL doesn't change (nobody fires LL between a and a+1: only t fires).
bL doesn't change.
t changes at step a (t fires).

So config[a+1][t] = config[a][t] + 1. But right(bL) = t.
The triple at bL: (config[a+1][LL], config[a+1][bL], config[a+1][t])
                 = (config[a][LL], config[a][bL], config[a][t] + 1 mod m_t)
                 ≠ (config[a][LL], config[a][bL], config[a][t])

Wait, that means the triple CHANGED because t fired at step a!
So step a does NOT have the same triple as interior[0] at bL.

Let me recheck. The claim was EC at bL between step a and interior[0].
But t fires at step a, changing bL's right-neighbor value. So they DON'T match.

So where does the EC actually come from?

Let me trace it more carefully.
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


n, ms = 5, [2, 3, 2, 3, 2]
word = (0, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4, 3, 4, 0, 1)
cycle = build_cycle(ms, n, word)
ell = len(word)

print(f"word = {word}")
print(f"cycle len = {ell}")
print()

# Focus on sorry 1121 at t=1, phase a=15, s=4
t = 1
a_step = 15  # fires t=1
s_step = 4   # fires t=1

print(f"t={t}, bL={(t-1)%n}={0}, bR={(t+1)%n}={2}")
print(f"Phase: a={a_step} (fires {word[a_step]}), s={s_step} (fires {word[s_step]})")

# Interior: steps 16%16=0, 1, 2, 3
interior = list(range(a_step + 1, ell)) + list(range(0, s_step))
print(f"Interior steps: {interior}")
print(f"Interior movers: {[word[st] for st in interior]}")
print()

# Configs at each step
print("Configs:")
for st in [a_step] + interior + [s_step]:
    c = cycle[st]
    m = word[st]
    print(f"  step {st:2d}: fires proc {m}, config = {c}")

# The chain goes RIGHT from bR=2: procs 2, 3, 4, 0
# Let's trace explicitly.
print()
print("Chain RIGHT from bR=2:")
bR = 2
chain_procs = []
for d in range(1, n):
    p = (bR + d) % n
    chain_procs.append(p)
print(f"  Chain procs after bR: {chain_procs}")

# For each chain proc, find its first fire in interior
for cp in chain_procs:
    first_fire = None
    for i, st in enumerate(interior):
        if word[st] == cp:
            first_fire = (i, st)
            break
    if first_fire:
        print(f"  proc {cp}: first fire at interior[{first_fire[0]}] = step {first_fire[1]}")
    else:
        print(f"  proc {cp}: does NOT fire in interior")

# What is the chain sequence?
# interior movers: [0, 4, 3, 2]
# proc 0 fires at interior[0] = step 0
# proc 4 fires at interior[1] = step 1
# proc 3 fires at interior[2] = step 2
# proc 2 fires at interior[3] = step 3

# Chain from bR=2: next is RR=3, then RRR=4, then right^3=0, then right^4=1=t.
# 3 fires at interior[2], 4 fires at interior[1], 0 fires at interior[0].
# Chain: 3 (first at idx 2), tight? 4 fires at idx 1 = 2-1. Yes tight.
# Next: 4 (first at idx 1), tight? 0 fires at idx 0 = 1-1. Yes tight.
# Next: 0 (first at idx 0). Next outward = (0+1)%5 = 1 = t. t doesn't fire in interior.
# "No fire" with first_idx = 0.

print()
print("Chain trace:")
print("  bR=2 fires at interior[3]")
print("  RR=3 fires at interior[2] (tight: 3-1=2)")
print("  RRR=4 fires at interior[1] (tight: 2-1=1)")
print("  right^3=0 fires at interior[0] (tight: 1-1=0)")
print("  right^4=1=t: doesn't fire in interior (it's a TernaryPhase)")
print("  -> No fire at proc 0 with first_idx=0")
print()

# Now: where is the EC?
# The claim in the previous script was EC at proc 0 (= bL).
# Step a=15 fires t=1. Config at step 15:
print("Checking EC mechanism:")
print(f"  Step a={a_step} fires t={t}. Config: {cycle[a_step]}")
print(f"  Step interior[0]={interior[0]} fires proc 0. Config: {cycle[interior[0]]}")
print()

# Boundary triple at proc 0:
p = 0
pL = (p-1) % n  # 4
pR = (p+1) % n  # 1 = t
print(f"  Proc 0 boundary: (left={pL}, self=0, right={pR}={t})")
triple_at_a = (cycle[a_step][pL], cycle[a_step][p], cycle[a_step][pR])
triple_at_int0 = (cycle[interior[0]][pL], cycle[interior[0]][p], cycle[interior[0]][pR])
print(f"  Triple at step {a_step} (nonmover for 0): {triple_at_a}")
print(f"  Triple at step {interior[0]} (mover for 0): {triple_at_int0}")
print(f"  Match: {triple_at_a == triple_at_int0}")
print()

# They DON'T match because right(0) = t = 1, and t fires at step a_step,
# changing config at proc 1.

# So where is the ACTUAL EC?
# Let me find ALL ECs in this cycle
print("All entry conflicts in this cycle:")
for p in range(n):
    pL = (p-1) % n
    pR = (p+1) % n
    mover = {}
    nonmover = {}
    for st in range(ell):
        triple = (cycle[st][pL], cycle[st][p], cycle[st][pR])
        if word[st] == p:
            mover[triple] = st
        else:
            if triple not in nonmover:
                nonmover[triple] = []
            nonmover[triple].append(st)
    for tr in mover:
        if tr in nonmover:
            print(f"  EC at proc {p}: mover step {mover[tr]}, nonmover steps {nonmover[tr]}, "
                  f"triple={tr}")

# The previous script found EC at proc 0. Let me check what triple it is.
# From earlier output:
# proc=0, mover_step=10, nonmover_step=15, triple=(0, 0, 2)
# proc=0, mover_step=14, nonmover_step=11, triple=(0, 1, 2)
# proc=4, mover_step=1, nonmover_step=14, triple=(0, 0, 1)
# proc=4, mover_step=13, nonmover_step=2, triple=(0, 1, 1)
#
# EC at proc 0 between steps 10 and 15.
# Step 10 fires proc 0 (mover). Step 15 fires proc 1 (nonmover for 0).
# These are NOT in the same phase.

print()
print("INSIGHT: The EC is NOT at the chain-end proc within the same phase.")
print("It's a GLOBAL EC elsewhere in the cycle.")
print()
print("The chain analysis code was reporting EC at the chain-end proc,")
print("but using a different EC finding method (global search).")
print()

# Let me re-examine the full_chain_analysis function.
# When 'no_fire_first_step': ec_proc is set but ec_info is None.
# The function returns (chain, 'no_fire_first_step', current_proc, None).
# current_proc = 0 (bL). EC proc = 0. But the EC is GLOBAL, not local.

# So the chain termination does NOT directly give EC at the chain-end proc.
# The chain just extends all the way through. The EC exists in the cycle,
# but the chain argument alone doesn't find it.

# This means the sorry cannot be discharged by extending the chain.
# We need a DIFFERENT argument.

# Let me think about what the chain tells us.
# The chain says: interior movers are [0, 4, 3, 2] (for this phase).
# That is: bL, LL, RR, bR in order.
# The entire interior is a SWEEP from bL through LL, wrapping around to RR, bR.
# All procs except t fire exactly once in this phase.
# The phase has length = n-1 = 4 steps. Each step fires a different non-t proc.

# This is a FULL SWEEP PHASE: every non-t proc fires exactly once,
# in the order bL, left(bL), left(left(bL)), ..., right(t) = bR.
# It's a sweep going LEFT from t (through bL, LL, ...).

# Full sweep phases at sandwiched ternary with J=1, K=1 are highly structured.
# The question: do full sweep phases lead to EC?

print("="*70)
print("KEY FINDING: FULL SWEEP PHASES")
print("="*70)
print()
print("When the chain extends all the way through, the interior is a FULL SWEEP:")
print("every non-t proc fires exactly once, in consecutive order around the ring.")
print()
print("The phase interior movers are: bL, left(bL), ..., right(bR), bR")
print("(going one direction around the ring, covering all n-1 non-t procs).")
print()
print("This means: every phase has J=1, K=1, and length n-1.")
print("With fc(t) phases, each of length n-1: total cycle length = fc(t) * (n-1) + fc(t) = fc(t)*n.")
print("But cycle length must equal product of all fire counts.")
print()
print("Let me check: in the sorry cases, are ALL phases full sweeps?")

# Check all phases for the sorry-case word
for t in [1, 3]:
    bL = (t-1) % n
    bR = (t+1) % n
    t_fires = sorted(i for i in range(ell) if word[i] == t)
    print(f"\nt={t}, t_fires={t_fires}")
    for idx in range(len(t_fires)):
        s_step = t_fires[idx]
        a_step = t_fires[(idx-1) % len(t_fires)]
        if s_step > a_step:
            interior = list(range(a_step+1, s_step))
        else:
            interior = list(range(a_step+1, ell)) + list(range(0, s_step))
        movers = [word[st] for st in interior]
        J = sum(1 for m in movers if m == bL)
        K = sum(1 for m in movers if m == bR)
        unique = len(set(movers))
        print(f"  phase [{a_step}, {s_step}): interior movers = {movers}, "
              f"J={J}, K={K}, #unique={unique}, len={len(movers)}")

print()
print("="*70)
print("REVISED PROOF APPROACH")
print("="*70)
print()
print("The chain extends through all interior procs, showing the phase is a sweep.")
print("A sweep phase has ALL n-1 non-t procs firing once each.")
print("This is a VERY strong structural constraint.")
print()
print("Key observation: in a full sweep phase, the t-fire step and the")
print("sweep steps have a specific triple pattern.")
print()
print("For the LEAN sorry: instead of finding EC at the chain end,")
print("recognize that the sorry conditions (tight chain all the way through)")
print("imply the phase is a sweep. Then use a DIFFERENT EC argument for sweeps.")
print()
print("But wait: the Lean code at sorry 1077/1121 is already in a case split")
print("where it has exhausted simple EC arguments. The sorry says the chain")
print("extends further. The fix: either")
print("  (A) Extend the chain recursively (but it doesn't directly give EC), or")
print("  (B) Show the sorry conditions are actually impossible (like sorry 1012), or")
print("  (C) Use a different argument entirely at this case.")
print()
print("Let me check: ARE the sorry 1077/1121 conditions actually possible?")
print("They ARE (we found examples). So (B) is out.")
print("The chain extends but doesn't directly give EC. So (A) is insufficient.")
print("We need (C): a different argument.")
print()
print("The different argument: the full-sweep structure of the phase gives EC")
print("via a DIFFERENT entry conflict mechanism. Specifically:")
print("In a full sweep, configs cycle through all n-1 non-t values.")
print("The t-fire step has a specific boundary triple.")
print("One of the sweep steps has a matching triple.")
print()

# Let me check: in full-sweep phases, is there always an EC?
# Actually, the EC might not be AT t. Let me find it at any proc.
print("Looking for EC mechanism in full-sweep phases...\n")

# Check the specific example in detail
word_ex = (0, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4, 3, 4, 0, 1)
cycle_ex = build_cycle(ms, n, word_ex)
t = 1
a_step = 15
s_step = 4
interior = [0, 1, 2, 3]
movers = [word_ex[st] for st in interior]
print(f"Phase [{a_step}, {s_step}): movers = {movers}")

# Configs in this phase
print("Configs in phase:")
for st in [a_step] + interior + [s_step]:
    c = cycle_ex[st]
    m = word_ex[st]
    print(f"  step {st:2d}: fires {m}, config = {c}")

# The key: step a_step=15 fires t=1.
# After step 15: config = ... (with t advanced by 1).
# Step 0 fires 0 (bL). Step 1 fires 4 (LL). Step 2 fires 3 (RR). Step 3 fires 2 (bR).
# Step 4 fires 1 (t again).

# Between steps 15 and 4: t doesn't fire. This is the TernaryPhase.
# Step 15 fires t. Step 0 fires bL. Between them: no steps.
# So config[0] = config[15] except at t (which fired).

# Now: for EC at proc 0 (bL):
# boundary = (left(0)=4, 0, right(0)=1)
# At step 15: mover is 1 (t). Not 0. So nonmover for 0.
# At step 0: mover is 0. So mover for 0.
# Between steps 15 and 0: NO steps (interior[0] = 0 is adjacent to step 15).
# But step 15 fires t=1 = right(0). So right(0) value changes.
# Triple at step 15: (cycle_ex[15][4], cycle_ex[15][0], cycle_ex[15][1])
# Triple at step 0: (cycle_ex[0][4], cycle_ex[0][0], cycle_ex[0][1])
# Since step 15 fires t=1: cycle_ex[0] = cycle_ex[15] except at proc 1.
# cycle_ex[0][1] = (cycle_ex[15][1] + 1) % 3.
# So triple differs in the right component. NO EC here.

# Hmm. So the sweep phases have EC elsewhere, not between the t-fire and the first sweep step.

# Let me check: across ALL phases (not just one), the sweep structure creates EC
# because the same boundary triple must repeat.

# Actually: the sorry 1077/1121 is inside the h_phase_le1 proof.
# h_phase_le1 says: for EACH phase, J + K <= 1.
# If ANY phase has J + K >= 2, we derive EC.
# The sorry is reached when a SPECIFIC phase has J >= 1 and K >= 1.
# We need EC from THAT phase (not globally).

# But the Lean proof just needs hasEntryConflict gc (global).
# Let me re-read the Lean: at the sorry, the goal is hasEntryConflict gc.
# Not per-phase. So a GLOBAL EC works.

# The issue: we have a specific phase with J >= 1, K >= 1, and the chain
# extends all the way. We know the cycle HAS global EC. But can we
# CONSTRUCT it from the chain information?

# The observation from the data: EC proc is always at distance +-1 from t.
# That means EC at bL or bR. But NOT from the chain argument.
# From a DIFFERENT mechanism entirely.

# Let me find the actual EC for each sorry-case phase and understand its source.

words = enumerate_mover_words(ms, n, 18)
ec_mechanism = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in [1, 3]:
        bL = (t-1) % n
        bR = (t+1) % n

        t_fires = sorted(i for i in range(ell) if word[i] == t)
        if len(t_fires) < 2:
            continue

        for idx in range(len(t_fires)):
            s_step = t_fires[idx]
            a_step = t_fires[(idx-1) % len(t_fires)]
            if s_step > a_step:
                interior = list(range(a_step+1, s_step))
            else:
                interior = list(range(a_step+1, ell)) + list(range(0, s_step))
            if not interior:
                continue

            J = sum(1 for st in interior if word[st] == bL)
            K = sum(1 for st in interior if word[st] == bR)
            if J < 1 or K < 1:
                continue

            # Check if full sweep (sorry case)
            movers = [word[st] for st in interior]
            if len(interior) != n - 1:
                continue  # not full sweep
            if len(set(movers)) != n - 1:
                continue  # not all different

            # Find global EC
            for p in range(n):
                pL = (p-1) % n
                pR = (p+1) % n
                triples_mover = {}
                triples_nonmover = {}
                for st in range(ell):
                    tr = (cycle[st][pL], cycle[st][p], cycle[st][pR])
                    if word[st] == p:
                        triples_mover[tr] = st
                    else:
                        if tr not in triples_nonmover:
                            triples_nonmover[tr] = []
                        triples_nonmover[tr].append(st)
                for tr in triples_mover:
                    if tr in triples_nonmover:
                        m_step = triples_mover[tr]
                        nm_step = triples_nonmover[tr][0]
                        # Classify: are these steps in the same phase?
                        in_phase = m_step in interior or m_step == s_step
                        nm_in_phase = nm_step in interior or nm_step == a_step
                        rel = ((p - t) % n)
                        if rel > n//2: rel -= n
                        ec_mechanism[f'p={p}_rel={rel}_same_phase={in_phase and nm_in_phase}'] += 1
                        break
                else:
                    continue
                break

print(f"\nEC mechanism distribution for full-sweep sorry phases:")
for key in sorted(ec_mechanism.keys()):
    print(f"  {key}: {ec_mechanism[key]}")
