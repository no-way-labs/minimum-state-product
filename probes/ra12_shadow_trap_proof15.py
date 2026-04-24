"""
Shadow Trap Proof — Part 15: Understanding the role of isolated firings.

The closure violation in Part 14 occurred because:
- (0,1,0,1,0) fires proc 0 (matching a mover entry) and reaches g_5=(1,1,0,1,0)
- g_5 has extra H-1 good neighbors beyond g_4 and g_6

The word was (1,0,4,3,4,3,2,1,0,1,2,3).
Binary procs: 0, 2, 4.
Proc 0 fires at steps 1 and 8.
Step 1: mover=0, (0,0,0)->1 (from g_1=(0,1,0,0,0) to g_2=(1,1,0,0,0))
Step 8: mover=0, (0,2,1)->0 (from g_8=(1,2,1,2,0) to g_9=(0,2,1,2,0))

The closure violation: config (0,1,0,1,0) has proc 0 context (0,0,0)
(since left=proc4=0, self=0, right=proc1=1... wait, let me check).

Actually, proc 0's context in (0,1,0,1,0):
  L = config[4] = 0
  S = config[0] = 0
  R = config[1] = 1

Step 1 mover entry: proc 0, ctx=(0,0,0)->1. Context is (0,0,0).
But in (0,1,0,1,0), proc 0's context is (0,0,1). That's DIFFERENT.

Wait, maybe it matches step 8: proc 0, ctx=(0,2,1)->0.
In (0,1,0,1,0), proc 0's context is (0,0,1). That's (L=0,S=0,R=1).
Step 8 context: (L=0,S=2,R=1). S doesn't match.

So HOW does (0,1,0,1,0) fire proc 0? Let me recheck.

Actually, the forced entry table includes NON-MOVER entries too.
At step 5 (mover=3), proc 0 has context (0,1,1) -> identity.
At step 2 (mover=4), g_2=(1,1,0,0,0), proc 0 has L=0,S=1,R=1, non-mover.
Hmm, but the issue is MOVER entries for other procs that happen to fire
proc 0 to a different value.

Let me re-examine: the extract_forced_entries function collects:
- Mover entries: (mover, L, S, R) -> S' != S
- Non-mover entries: (q, L, S, R) -> S (identity)

A proc p is "forced-privileged" if entries[(p,L,S,R)] != S.
This happens ONLY for mover entries. Non-mover entries map to S.

So the transition (0,1,0,1,0) -> (1,1,0,1,0) means there's a mover
entry (0, L, 0, R) -> 1 where L = left of 0 in (0,1,0,1,0) = proc4 = 0,
R = right of 0 = proc1 = 1. So key = (0, 0, 0, 1).

Is (0, 0, 0, 1) a mover entry? Step 1: (0, 0, 0, 0) -> 1. No, R=0 not 1.
Step 8: (0, 0, 2, 1) -> 0. No, that's S=2.

Something is wrong with my forced_step function. Let me debug.
"""

import itertools

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

n = 5
ms = [2, 3, 2, 3, 2]
word = (1, 0, 4, 3, 4, 3, 2, 1, 0, 1, 2, 3)
combo = ((0, 1, 0), (0, 1, 2, 0), (0, 1, 0), (0, 1, 2, 0), (0, 1, 0))
CL = len(word)

# Build cycle
fc = [0] * n
state = [combo[p][0] for p in range(n)]
configs = [tuple(state)]
for s in range(CL):
    p = word[s]
    fc[p] += 1
    state[p] = combo[p][fc[p]]
    configs.append(tuple(state))
configs = configs[:-1]
good_set = set(configs)

print("Good cycle:")
for k in range(CL):
    g = configs[k]
    p = word[k]
    ctx = get_context(g, p, n)
    sp = configs[(k+1) % CL][p]
    print(f"  g_{k:2d}={g}, mover={p}, ctx={ctx}->{sp}")

# Build forced entries CAREFULLY
entries = {}
for s in range(CL):
    p = word[s]
    c = configs[s]

    # Mover entry
    L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
    Sp = configs[(s+1) % CL][p]
    key = (p, L, S, R)
    print(f"  Adding mover entry: {key} -> {Sp}")
    entries[key] = Sp

    # Non-mover entries
    for q in range(n):
        if q == p:
            continue
        Lq = c[(q-1) % n]; Sq = c[q]; Rq = c[(q+1) % n]
        key = (q, Lq, Sq, Rq)
        if key not in entries:
            entries[key] = Sq  # Identity

# Check: what entry matches proc 0 in (0,1,0,1,0)?
c = (0, 1, 0, 1, 0)
print(f"\nChecking config {c}:")
for p in range(n):
    L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
    key = (p, L, S, R)
    if key in entries:
        v = entries[key]
        if v != S:
            print(f"  Proc {p}: ctx=({L},{S},{R}), entry maps to {v} (FIRES)")
        else:
            print(f"  Proc {p}: ctx=({L},{S},{R}), entry maps to {v} (identity)")
    else:
        print(f"  Proc {p}: ctx=({L},{S},{R}), NO entry")

# The issue might be that a NON-MOVER entry at one step conflicts
# with a MOVER entry at another step. Let me check for conflicts.
print("\n\nChecking for entry conflicts:")
entry_sources = {}  # key -> [(step, is_mover, value)]
for s in range(CL):
    p = word[s]
    c = configs[s]

    # Mover
    L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
    Sp = configs[(s+1) % CL][p]
    key = (p, L, S, R)
    if key not in entry_sources:
        entry_sources[key] = []
    entry_sources[key].append((s, True, Sp))

    # Non-movers
    for q in range(n):
        if q == p:
            continue
        Lq = c[(q-1) % n]; Sq = c[q]; Rq = c[(q+1) % n]
        key = (q, Lq, Sq, Rq)
        if key not in entry_sources:
            entry_sources[key] = []
        entry_sources[key].append((s, False, Sq))

conflicts = 0
for key, sources in entry_sources.items():
    values = set(v for _, _, v in sources)
    if len(values) > 1:
        conflicts += 1
        print(f"  CONFLICT at {key}: {sources}")

print(f"\nTotal conflicts: {conflicts}")

# If there are conflicts, the forced entry table is INCONSISTENT.
# This means no valid transition table can satisfy all entries.
# Which is EXACTLY what we want to prove: the system CANNOT converge.
# But the proof mechanism is different from what I was trying.

# Actually, the conflict means: the context (p, L, S, R) appears as
# a mover entry with S->S' and also as a non-mover entry with S->S.
# Since S' != S, these are contradictory. This IS the entry conflict
# mechanism from the existing proofs!

# So the correct proof approach is:
# 1. Show that the forced entry table has conflicts (entry conflicts)
# 2. Entry conflicts mean no consistent transition table exists
# 3. Therefore, no valid system exists with this good cycle.

# But wait: the problem asks for a ShadowTrap, not an entry conflict.
# These are different mechanisms.
# Entry conflict: direct impossibility (no consistent transition table).
# ShadowTrap: existence of a trap cycle (given a consistent table, the
#   system gets trapped in non-good configs).

# Are they related? Let me think...
# If the forced entry table has conflicts, then REGARDLESS of how the
# transition table resolves the conflict, there's a bad outcome.
# Either:
# (a) The transition matches the mover entry: the non-mover step now
#     produces a firing instead of identity, creating unexpected behavior.
# (b) The transition matches the identity: the mover step doesn't fire,
#     meaning the good cycle can't proceed.
#
# Either way, the system can't have this good cycle. But we ASSUMED this
# IS the good cycle. So the assumption fails: this good cycle can't exist
# with a valid transition table.

# This is the ENTRY CONFLICT approach, not the ShadowTrap approach.
# The two are complementary mechanisms for proving impossibility.

print("\n\nKEY INSIGHT:")
print("Entry conflicts and ShadowTraps are COMPLEMENTARY mechanisms.")
print("When entry conflicts exist: no consistent transition table is possible.")
print("When no entry conflicts: the transition table is consistent, and we need")
print("to show that the forced graph has a trap cycle (ShadowTrap).")
print()
print("The original theorem says: for sweeps with isolated binary firings,")
print("a ShadowTrap exists. This should apply when the forced entry table")
print("is CONSISTENT (no conflicts). In that case, H-1 Uniqueness should hold.")
print()
print("Let me check: do the H-1 failures always coincide with entry conflicts?")

# Check: for all instances, does H-1 failure correlate with entry conflicts?
