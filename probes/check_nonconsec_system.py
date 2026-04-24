#!/usr/bin/env python3
"""
Key question: can the 6192 EC-free zero-winding cycles at n=5, ms=[2,3,2,3,2]
be embedded in a valid SYSTEM? Or does system-level consistency kill them?

A valid system means: for each processor p, there's a transition function
f_p: contexts -> states, such that:
- f_p(L,S,R) != S for privileged (mover) contexts
- f_p(L,S,R) = S for non-privileged (non-mover) contexts
- These are GLOBALLY consistent (same f_p used everywhere)

The EC-free cycles have consistent M/N partitions within the cycle.
But can the resulting f_p be extended to a TOTAL function on all contexts?

For a cycle to be part of a valid system:
- Each proc p has mover contexts M_p and nonmover contexts N_p (disjoint by EC-free)
- f_p must map M_p contexts to something != S, and N_p contexts to S
- For unseen contexts: f_p can be anything
- This is ALWAYS possible! Just set f_p(L,S,R) = 1-S for (L,S,R) in M_p,
  f_p(L,S,R) = S for everything else.

Wait... so if cycles are EC-free, they CAN always be embedded in a system?
Then how does the non-consecutive lower bound work?

The answer must be: the CONVERGENCE requirement kills it.
A valid system must CONVERGE (every execution reaches a legitimate config).
Having a good cycle means the system has a cycle of bad configs.
But convergence means: from every config, you eventually reach a good config.
A cycle of bad configs is OK as long as it's not a TRAP (no escape to good configs).

So the argument is: EC-free cycles at sub-threshold → the system has a cycle
of bad configs that IS a trap (no escape), contradicting convergence.

OR: the argument uses the SHADOW TRAP idea — the good cycle forces a shadow
cycle that traps bad configs.

Let me check: do these EC-free cycles have shadow cycles?
"""
from itertools import product as iproduct
from collections import Counter
import time

n = 5
ms = [2, 3, 2, 3, 2]
binary_procs = [0, 2, 4]

all_configs = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs)}
total = len(all_configs)

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

print(f"n={n}, ms={ms}, configs={total}")
print("Finding EC-free zero-winding cycles (max_path=12)...")

t0 = time.time()
ec_free_cycles = []

for start in range(total):
    stack = [(start, [start], [0]*n, 0, {}, [])]
    while stack:
        ci, path, fc, wind, cons, movs = stack.pop()
        if len(path) > 12: continue
        c = all_configs[ci]
        for mover in range(n):
            L = c[(mover-1) % n]; S = c[mover]; R = c[(mover+1) % n]
            key = (mover, L, S, R)
            if key in cons and cons[key] == 'nonmover': continue
            valid = True
            new_cons = dict(cons)
            new_cons[key] = 'mover'
            for p in range(n):
                if p == mover: continue
                kp = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if kp in new_cons and new_cons[kp] == 'mover':
                    valid = False; break
                new_cons[kp] = 'nonmover'
            if not valid: continue
            possible_vals = [v for v in range(ms[mover]) if v != S]
            for new_val in possible_vals:
                new_c = list(c); new_c[mover] = new_val
                new_ci = cidx[tuple(new_c)]
                new_fc = list(fc); new_fc[mover] += 1
                new_wind = wind
                if movs: new_wind += signed_step(movs[-1], mover)
                if new_ci == start and len(path) >= 3:
                    fw = new_wind + signed_step(mover, movs[0])
                    if fw == 0:
                        # Check EC-free
                        has_ec = False
                        for p in range(n):
                            m_set = set()
                            n_set = set()
                            for k, role in new_cons.items():
                                if k[0] != p: continue
                                ctx = k[1:]
                                if role == 'mover':
                                    if ctx in n_set: has_ec = True; break
                                    m_set.add(ctx)
                                else:
                                    if ctx in m_set: has_ec = True; break
                                    n_set.add(ctx)
                            if has_ec: break
                        if not has_ec:
                            ec_free_cycles.append({
                                'path': list(path), 'movers': movs + [mover],
                                'fc': list(new_fc), 'cons': dict(new_cons)
                            })
                    continue
                if new_ci in path: continue
                remaining = 12 - len(path)
                if remaining < 2: continue
                stack.append((new_ci, path+[new_ci], new_fc, new_wind,
                              new_cons, movs+[mover]))

elapsed = time.time() - t0
print(f"Found {len(ec_free_cycles)} EC-free zero-winding cycles in {elapsed:.1f}s")

# Analyze the cycles
print(f"\nCycle length distribution:")
len_dist = Counter(len(c['path']) for c in ec_free_cycles)
for k in sorted(len_dist): print(f"  len={k}: {len_dist[k]}")

print(f"\nFC distribution:")
fc_dist = Counter(tuple(c['fc']) for c in ec_free_cycles)
for k in sorted(fc_dist)[:10]: print(f"  fc={list(k)}: {fc_dist[k]}")

# KEY: how many GOOD configs does each cycle visit?
# A "good" config is one where some proc is privileged.
# Actually: configs IN the cycle are the ones the good cycle visits.
# The cycle visits len(path) distinct configs.
print(f"\nConfigs per cycle: {set(len(c['path']) for c in ec_free_cycles)}")

# KEY QUESTION: For these cycles, how many total configs are "covered"
# (appear in at least one EC-free cycle)?
covered = set()
for cyc in ec_free_cycles:
    for ci in cyc['path']:
        covered.add(ci)
print(f"\nTotal configs covered by EC-free cycles: {len(covered)}/{total}")
print(f"Uncovered configs: {total - len(covered)}")

# How many configs appear as GOOD (in the cycle) vs BAD (not in any cycle)?
# For a system to converge: every config must eventually reach a good config.
# Good configs = configs in the good cycle. Bad = everything else.
# If there's a cycle of bad configs with no escape: ¬converges.

# For each EC-free cycle: can we build a valid system around it?
# Check: does the system have a trap (unreachable-from-good cycle)?
print("\n=== SYSTEM CONSTRUCTION CHECK ===")

# Take the first few cycles and try to build a system
for idx in range(min(5, len(ec_free_cycles))):
    cyc = ec_free_cycles[idx]
    path = cyc['path']
    movers = cyc['movers']
    L = len(path)

    # Build transition functions from the cycle constraints
    # For each proc p: contexts seen as mover → fire (toggle for binary, some val for ternary)
    # contexts seen as nonmover → identity
    # unseen contexts → identity (safe default)
    rules = {}
    for p in range(n):
        rules[p] = {}
        for k, role in cyc['cons'].items():
            if k[0] != p: continue
            _, Lv, Sv, Rv = k
            if role == 'mover':
                # f(L,S,R) != S. For binary: f = 1-S. For ternary: f = (S+1)%m
                if ms[p] == 2:
                    rules[p][(Lv, Sv, Rv)] = 1 - Sv
                else:
                    rules[p][(Lv, Sv, Rv)] = (Sv + 1) % ms[p]
            else:
                rules[p][(Lv, Sv, Rv)] = Sv  # identity

        # Fill unseen contexts with identity
        for Lv in range(ms[(p-1)%n]):
            for Sv in range(ms[p]):
                for Rv in range(ms[(p+1)%n]):
                    if (Lv, Sv, Rv) not in rules[p]:
                        rules[p][(Lv, Sv, Rv)] = Sv

    # Check: which configs are "good" (some proc privileged)?
    good_configs = set()
    for ci, c in enumerate(all_configs):
        for p in range(n):
            Lv = c[(p-1)%n]; Sv = c[p]; Rv = c[(p+1)%n]
            if rules[p][(Lv, Sv, Rv)] != Sv:
                good_configs.add(ci)
                break

    # The cycle configs should all be good
    cycle_configs = set(path)
    cycle_in_good = cycle_configs.issubset(good_configs)

    # Build the full transition graph
    # From each config: find all privileged procs, each gives a successor
    succs = {}
    for ci, c in enumerate(all_configs):
        privs = []
        for p in range(n):
            Lv = c[(p-1)%n]; Sv = c[p]; Rv = c[(p+1)%n]
            if rules[p][(Lv, Sv, Rv)] != Sv:
                new_c = list(c)
                new_c[p] = rules[p][(Lv, Sv, Rv)]
                new_ci = cidx[tuple(new_c)]
                privs.append((p, new_ci))
        succs[ci] = privs

    # Check: are there bad configs that can't reach any good config?
    # BFS backwards from good configs
    can_reach_good = set(good_configs)
    frontier = list(good_configs)
    # Need reverse graph
    rev_succs = {ci: [] for ci in range(total)}
    for ci in range(total):
        for p, nci in succs[ci]:
            rev_succs[nci].append(ci)

    # BFS forward from good configs in reverse graph = BFS backward
    # Actually: config X can reach good if there's a path X -> ... -> good
    # So we want: which configs have a path to good?
    # BFS backward from good: X -> good exists if good -> X exists in reverse
    # No wait: we want forward reachability TO good.
    # Non-deterministic: from X, scheduler picks ANY privileged proc.
    # Converges means: for ALL schedulers, eventually reach good.
    # That's harder. Let's just check: is there a trap (SCC with no good config)?

    # Find SCCs using iterative Tarjan's
    bad_configs = set(range(total)) - good_configs

    # For bad configs: check if there's a cycle among them
    # Simple: BFS from each bad config, see if it can reach only bad configs
    bad_sccs = 0
    visited_bad = set()
    for start_ci in bad_configs:
        if start_ci in visited_bad: continue
        # BFS from start_ci through bad configs only
        queue = [start_ci]
        component = set()
        has_cycle = False
        while queue:
            ci = queue.pop()
            if ci in component: continue
            component.add(ci)
            for p, nci in succs[ci]:
                if nci in component:
                    has_cycle = True
                if nci in bad_configs and nci not in component:
                    queue.append(nci)
        visited_bad |= component
        if has_cycle and len(component) > 0:
            bad_sccs += 1

    print(f"\nCycle {idx}: len={L}, fc={cyc['fc']}")
    print(f"  Good configs: {len(good_configs)}/{total}")
    print(f"  Cycle configs all good: {cycle_in_good}")
    print(f"  Bad config clusters with internal cycles: {bad_sccs}")

    if bad_sccs > 0:
        print(f"  *** BAD TRAP EXISTS: system doesn't converge! ***")
    else:
        print(f"  No bad traps — system might converge")

    # For convergence: need to check if there's a scheduler that avoids good
    # This is more complex. For now, just report trap existence.
