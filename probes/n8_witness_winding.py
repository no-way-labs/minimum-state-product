#!/usr/bin/env python3
"""Analyze the n=8 witness: winding number and context structure."""
import itertools, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from collections import Counter, defaultdict

ms = [2, 2, 3, 4, 3, 3, 2, 3]
n = 8
rules = {
    0: {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
    1: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
    2: {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
    3: {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
    4: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,(3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
    5: {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
    6: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,(2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
    7: {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
}

def f(i, L, S, R):
    return rules[i][(L, S, R)]

# Find good cycle
all_configs = list(itertools.product(*(range(m) for m in ms)))
sp_set = set()
sp_mover = {}
for c in all_configs:
    priv = [i for i in range(n) if f(i, c[(i-1)%n], c[i], c[(i+1)%n]) != c[i]]
    if len(priv) == 1:
        sp_set.add(c)
        sp_mover[c] = priv[0]

succ = {}
for c in sp_set:
    mv = sp_mover[c]
    nc = list(c); nc[mv] = f(mv, c[(mv-1)%n], c[mv], c[(mv+1)%n]); nc = tuple(nc)
    succ[c] = (nc, mv)

good = set(sp_set)
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in good:
        nc, _ = succ[c]
        if nc not in good:
            to_remove.add(c)
    if to_remove:
        good -= to_remove; changed = True

print(f'Good configs: {len(good)}')

start = min(good)
cycle = [start]
movers = [succ[start][1]]
c = succ[start][0]
while c != start:
    cycle.append(c)
    movers.append(succ[c][1])
    c = succ[c][0]

CL = len(cycle)
print(f'Cycle length: {CL}')

# Winding: classify each step direction
cw = ccw = stay = jump = 0
for i in range(CL):
    prev_mv = movers[(i-1) % CL]
    mv = movers[i]
    diff = (mv - prev_mv) % n
    if diff == 1: cw += 1
    elif diff == n - 1: ccw += 1
    elif diff == 0: stay += 1
    else: jump += 1

print(f'Direction: CW={cw}, CCW={ccw}, stay={stay}, jump={jump}')
print(f'Winding = (CW-CCW)/n = ({cw}-{ccw})/{n} = {(cw-ccw)/n:.2f}')
print(f'Non-zero winding: {cw != ccw}')

fc = Counter(movers)
print(f'Fire counts: {dict(sorted(fc.items()))}')

# Entry conflict (must be 0)
mover_ctx = defaultdict(set)
nonmover_ctx = defaultdict(set)
for idx in range(CL):
    c = cycle[idx]; mv = movers[idx]
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if p == mv: mover_ctx[p].add((L,S,R))
        else: nonmover_ctx[p].add((L,S,R))

ec = sum(len(mover_ctx[p] & nonmover_ctx[p]) for p in range(n))
print(f'\nEntry conflicts: {ec}')
print(f'Per-proc context usage (|M|=distinct mover, |N|=distinct nonmover):')
for p in range(n):
    overlap = mover_ctx[p] & nonmover_ctx[p]
    m_ctx = len(mover_ctx[p]); n_ctx = len(nonmover_ctx[p])
    ctx_size = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
    frac_used = (m_ctx + n_ctx) / ctx_size
    print(f'  P{p}: m={ms[p]}, ctx={ctx_size}, |M|={m_ctx}, |N|={n_ctx}, '
          f'|M|+|N|={m_ctx+n_ctx}, ctx_frac={frac_used:.3f}, EC={len(overlap)}')

# Context-dependent transitions: how many contexts have different outputs
# depending on whether the proc is mover or not?
# Answer: NONE (EC=0 means no context appears as both mover and nonmover)
# But within mover contexts, how many distinct OUTPUTS are there per S value?
print(f'\nTransition analysis (context-dependent transitions):')
for p in range(n):
    # For each S value, count distinct mover outputs
    s_to_outputs = defaultdict(set)
    for idx in range(CL):
        if movers[idx] == p:
            c = cycle[idx]; c_next = cycle[(idx+1)%CL]
            S = c[p]; new_S = c_next[p]
            s_to_outputs[S].add(new_S)
    cd_count = sum(1 for s, outs in s_to_outputs.items() if len(outs) > 1)
    print(f'  P{p}: states with >1 mover output: {cd_count} '
          f'(total states={ms[p]}, detail: {dict(s_to_outputs)})')
