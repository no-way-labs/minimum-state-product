#!/usr/bin/env python3
"""Test 12: Verify the mixed round-trip parity argument.

Claim: Even if an intermediate round-trip exits through Bridge 0 and
returns through Bridge 2 (traversing the binary block), the parity
of k_0 and k_2 is both odd.

This is because:
- Base: k_0 = 1, k_2 = 1 (first exit through B0, last entry through B2)
- Bridge 0 round-trip: adds (2, 0) -> (odd+2, odd) = (odd, odd)
- Bridge 2 round-trip: adds (0, 2) -> (odd, odd+2) = (odd, odd)
- Mixed round-trip (exit B0, return B2): adds (1, 1) -> (odd+1, odd+1) = (even, even)
  WAIT: This breaks the parity!

Let me re-examine...

Actually, a "mixed round-trip" means:
  - Walk exits binary through B0 (k_0 += 1), traverses non-binary,
    enters binary through B2 (k_2 += 1), traverses binary block,
    and then either exits again through B0 or B2.

But this isn't a "round-trip" in my sense. A round-trip is: leave binary,
come back. If you leave through B0 and come back through B2, that's
one trip adding (1, 1). The next trip adds another (1, 1) or (2, 0) etc.

Let me reconsider the counting.

The walk starts at P_0 (binary). Let's track each crossing:
- C1: P_0 -> P_{n-1} (binary to non-binary via B0). k_0 += 1.
Now in non-binary territory.
- C2: P_3 -> P_2 or P_{n-1} -> P_0 (non-binary to binary).
  If through B0: k_0 += 1. Back in binary.
  If through B2: k_2 += 1. Back in binary.
Now in binary territory. Walk might traverse to the other side and exit again.
- C3: binary -> non-binary. Through whichever bridge.
...
- C_{2m}: non-binary -> binary (must end at P_2 for the walk to reach P_1).
  This last crossing must be through B2. k_2 += 1.

Total: 2m crossings. Each crossing adds 1 to either k_0 or k_2.
k_0 + k_2 = 2m (even).

The first crossing is through B0 (k_0 starts at 1).
The last crossing is through B2 (k_2 ends with += 1).
The intermediate 2m-2 crossings can be through either bridge.

k_0 = 1 + (number of intermediate B0 crossings)
k_2 = 1 + (number of intermediate B2 crossings)
k_0 + k_2 = 2m

For the intermediate 2m-2 crossings:
They come in pairs (exit + return). Each pair has two crossings.
A pair can be:
  (B0, B0): k_0 += 2
  (B2, B2): k_2 += 2
  (B0, B2): k_0 += 1, k_2 += 1
  (B2, B0): k_0 += 1, k_2 += 1

Wait, is (B0, B2) possible? That means exit binary through B0, return through B2.
Between those: traverse non-binary from B0 side to B2 side.
Then between return through B2 and next exit: traverse binary block from P_2 to P_0.
This means passing through P_1 (middle of binary block) WITHOUT P_1 firing.

If (B0, B2) happens, k_0 and k_2 each increase by 1.
Starting from k_0 = 1, k_2 = 0 (just the first crossing):
After one (B0, B2) pair: k_0 = 2, k_2 = 1.
Then the last crossing through B2: k_2 = 2.
Result: k_0 = 2, k_2 = 2. Both EVEN. BAD!

So mixed round-trips DO break the parity. But computation shows parity is
always odd. So mixed round-trips DON'T HAPPEN for n >= 5.

Let me verify: can the walk traverse the binary block (from P_2 to P_0 or
P_0 to P_2) without P_1 firing?
"""
from itertools import product as iproduct
from collections import Counter

def enum_cycles(ms, max_cycles=500, max_time=30):
    import time
    n = len(ms)
    t0 = time.time()
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    for start in all_configs:
        if time.time() - t0 > max_time: break
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 100000:
            if time.time() - t0 > max_time: break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for nv in range(ms[p]):
                    if nv == config[p]: continue
                    if movers:
                        d = min(abs(p-movers[-1]), n-abs(p-movers[-1]))
                        if d > 1: continue
                    L,S,R = config[(p-1)%n], config[p], config[(p+1)%n]
                    nd = dict(det); ok = True
                    km = (p,L,S,R)
                    if km in nd:
                        if nd[km] != nv: ok = False
                    else: nd[km] = nv
                    if not ok: continue
                    for i in range(n):
                        if i == p: continue
                        Li,Si,Ri = config[(i-1)%n], config[i], config[(i+1)%n]
                        ki = (i,Li,Si,Ri)
                        if ki in nd:
                            if nd[ki] != Si: ok = False; break
                        else: nd[ki] = Si
                    if not ok: continue
                    nc = list(config); nc[p] = nv; nc = tuple(nc)
                    if nc == start and len(path) >= n:
                        fired = set(movers + [p])
                        if fired == set(range(n)):
                            fm = movers + [p]
                            me_ok = True
                            for idx in range(len(path)):
                                c = path[idx]; priv = []
                                for i in range(n):
                                    ki = (i,c[(i-1)%n],c[i],c[(i+1)%n])
                                    if ki in nd and nd[ki] != c[i]: priv.append(i)
                                if len(priv) != 1: me_ok = False; break
                            if me_ok:
                                cycles.append((path, fm, nd))
                                if len(cycles) >= max_cycles: return cycles
                        continue
                    if nc not in set(path) and len(path) < 6*n:
                        stack.append((nc, path+[nc], nd, movers+[p]))
    return cycles

# Check: does the walk ever traverse the binary block without P1 firing?
# i.e., sequence ..., P0, P1, P2, ... or ..., P2, P1, P0, ... where
# P1 fires but... wait, P1 DOES fire if the mover is P1.
# The question: can P1 be a mover (in the mover word) during the between-segment?
# No! P1 only fires at steps s1 and s2. Any P1 in the mover word between s1 and s2
# would be a third P1 firing, contradicting fire count = 2.

# AH! This is the key. P1 fires exactly 2 times (steps s1 and s2).
# In the between-segment, P1 does NOT fire at all.
# But the mover word requires consecutive movers to be adjacent.
# If the walk is at P0, it can go to P1 (but P1 doesn't fire, so this can't happen).
# Wait: the mover word says who FIRES, not who the walk visits.
# If movers[t] = 1, then P1 fires at step t.
# Consecutive movers must be ring-adjacent.
# So if movers[t] = 0, then movers[t+1] must be in {n-1, 1}.
# But in the between-segment, P1 doesn't fire. So movers[t+1] = 1 is impossible.
# If movers[t] = 0 and P1 can't fire, then movers[t+1] = n-1 (the non-binary neighbor).

# Similarly, if movers[t] = 2, then movers[t+1] must be in {1, 3}.
# But P1 can't fire, so movers[t+1] = 3.

# THIS IS THE KEY STRUCTURAL FACT!
# In the between-segment:
# - When the walk reaches P0, it MUST go to P_{n-1} (can't go to P1).
# - When the walk reaches P2, it MUST go to P3 (can't go to P1).
# P1 acts as a WALL in the between-segment!

# Therefore, the walk cannot traverse from P0 to P2 or P2 to P0 through the
# binary block in the between-segment. P1 blocks any traversal.

# This means:
# - The walk enters non-binary through B0 (P0 -> P_{n-1}).
# - To return to binary, it must come through B0 (P_{n-1} -> P0) or B2 (P3 -> P2).
# - If it returns through B0: it's at P0, and must go back to P_{n-1} (P1 is blocked).
#   So the next exit is also through B0. This is a B0-B0 round-trip.
# - If it returns through B2: it's at P2, and must go to P3 (P1 is blocked).
#   So the next exit is through B2. But then the walk is on the P3 side.
#   To reach P2 again (for P1's second firing), it re-enters through B2.
#   This would be a B2-B2 round-trip... but wait, we need to eventually
#   reach P2 to fire P1. P2 is the last step before P1's second firing.

# With P1 blocking, the binary block is split into {P0} and {P2} as isolated
# nodes (from the perspective of the between-segment walk). The walk can bounce
# at P0 (P0 <-> P_{n-1}) or bounce at P2 (P2 <-> P3), but CANNOT cross from
# one to the other through P1.

# So every crossing is either B0 or B2, and consecutive crossings alternate:
# exit through B0, return through B0 (B0-B0 pair), or exit B2, return B2 (B2-B2 pair).
# MIXED ROUND-TRIPS ARE IMPOSSIBLE because P1 blocks the traversal!

# The crossing sequence is:
# Start at P0 -> exit B0 (k_0 += 1) -> [non-binary path] -> return through B0 or B2.
# If return through B0: at P0, exit B0 again (k_0 += 2 for the pair).
# If return through B2: at P2, must exit B2 (k_2 += 1 for return, k_2 += 1 for exit).
#   Wait, return through B2 means entering binary at P2. Then P2 can exit through B2
#   (P2 -> P3). That's k_2 += 1 (return) then k_2 += 1 (exit) = k_2 += 2 for the pair.
#   But is the return + exit counted as one round-trip? Let me recount.

# Actually the first time the walk returns to binary through B2, it arrives at P2.
# At P2, the walk can only go to P3 (P1 is blocked). So P2 fires and goes to P3.
# P3 -> ... non-binary ... -> and the walk must eventually come back to P2.
# The walk can return through B0 (to P0) or B2 (to P2).
# If return through B0: at P0, exit B0. Now we're counting.

# Let me just track the exact sequences.

ms = (2,2,2,3,4); n = 5
cycles = enum_cycles(ms, 200, 30)

print('=== Verify: P1 blocks traversal in between-segment ===')
# Check that movers[t] = 0 implies movers[t+1] = n-1 in between-segment
# and movers[t] = 2 implies movers[t+1] = 3 in between-segment
blocked = True
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    for s in range(s1+1, s2-1):  # between, not including last step
        m = movers[s]
        m_next = movers[s+1]
        if m == 0 and m_next == 1:
            print(f'  FAIL: P0 -> P1 in between at step {s}')
            blocked = False
        if m == 2 and m_next == 1:
            print(f'  FAIL: P2 -> P1 in between at step {s}')
            blocked = False

if blocked:
    print('  CONFIRMED: P1 never fires in between-segment, blocking binary traversal.')
else:
    print('  CONTRADICTION: P1 fires in between-segment!')

# Now verify that crossings are always same-bridge round-trips
print('\n=== Crossing type analysis ===')
crossing_types = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]

    # Track crossings: what bridge, and direction (exit/enter binary)
    crossings = []
    in_binary = True  # start at P0 (binary)
    for m in between:
        if m == 0:
            if in_binary:
                # P0 fires, next goes to P_{n-1} (exit through B0)
                # Actually, P0 firing doesn't tell us direction.
                # P0 firing means P0 is the mover. The walk was already at P0.
                # After P0 fires, next mover is P_{n-1} or P1.
                # Since P1 is blocked, next = P_{n-1}. So exit through B0.
                crossings.append(('B0', 'exit'))
                in_binary = False
            else:
                # Walk was at P_{n-1}, P0 fires (re-enters binary through B0)
                crossings.append(('B0', 'enter'))
                in_binary = True
        elif m == 2:
            if in_binary:
                crossings.append(('B2', 'exit'))
                in_binary = False
            else:
                crossings.append(('B2', 'enter'))
                in_binary = True

    # Classify the round-trip pairs
    # First crossing: exit through B0
    # Last crossing: enter through B2
    # Intermediate: pairs (exit, enter) that should be same-bridge
    if len(crossings) >= 2:
        pairs = []
        i = 0
        while i < len(crossings) - 1:
            if crossings[i][1] == 'exit' and crossings[i+1][1] == 'enter':
                pair_type = (crossings[i][0], crossings[i+1][0])
                pairs.append(pair_type)
                i += 2
            else:
                i += 1  # shouldn't happen

        pair_key = tuple(pairs)
        crossing_types[pair_key] += 1

print(f'  Crossing pair types:')
for ct, cnt in sorted(crossing_types.items(), key=lambda x: -x[1])[:20]:
    mixed = any(a != b for a, b in ct)
    tag = ' <-- MIXED!' if mixed else ''
    print(f'    {ct}: {cnt}{tag}')
