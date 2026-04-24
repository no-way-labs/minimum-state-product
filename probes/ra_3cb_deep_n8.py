#!/usr/bin/env python3
"""Deep n=8 3CB analysis: examine ALL possible good cycles, not just sweep/bounce."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'docs'))

from itertools import product as cartesian
from collections import defaultdict, Counter
from verifier import all_configs as gen_configs, apply_move, privileged_set, verify_system

ms = [2, 2, 2, 3, 3, 3, 3, 4]
n = 8
mid = 1
product = 2592
configs = list(gen_configs(ms))
print(f'n=8, ms={ms}, product={product}')

# 1. For each context at mid binary, count how many configs share it
# and what the "far" state space looks like
all_8 = [(L, S, R) for L in range(2) for S in range(2) for R in range(2)]
ctx_configs = defaultdict(list)
for c in configs:
    ctx = (c[(mid-1)%n], c[mid], c[(mid+1)%n])
    ctx_configs[ctx].append(c)

print(f'\nConfigs per context at proc {mid}:')
for ctx in sorted(all_8):
    print(f'  {ctx}: {len(ctx_configs[ctx])}')

# 2. Key insight: if mid fires (is mover), its output is DETERMINED by (L,S,R).
# Binary proc: f(L,S,R) in {0,1}. If it fires, output != S, so output = 1-S.
# So mover contexts are those where S flips: (L,0,R)->1 and (L,1,R)->0.
# But which (L,R) pairs trigger firing? That's the transition function's choice.

# For a VALID cycle, mid fires on exactly those contexts that appear as mover steps.
# From n=4..7 data: always exactly 2 mover contexts, always with S=0 and S=1 paired.
# Specifically: one context (a,1,b) where mid fires 1->0, one (c,0,d) where 0->1.

# 3. Analyze: how many distinct (L,R) pairs appear at mid across all configs?
# L = c[0] in {0,1} (binary), R = c[2] in {0,1} (binary)
# So (L,R) in {(0,0), (0,1), (1,0), (1,1)} = 4 pairs
# S in {0,1} gives 8 contexts total. Each has product/(m_L*m_S*m_R) = 2592/8 = 324 configs.

print(f'\nAll neighbors of proc {mid} are binary, so 4 (L,R) pairs x 2 S values = 8 contexts')
print(f'Each context has exactly {product//8} configs.')

# 4. The packing constraint:
# For mid to fire on context (L,S,R), the transition function says f(L,S,R) = 1-S.
# For mid NOT to fire on context (L,S,R), f(L,S,R) = S.
# Each context (L,S,R) can be either mover or non-mover, but not both (= 0 overlap at n=4..7).
#
# For a cycle of length C where mid fires k times:
# - k contexts used as mover (each used potentially multiple times)
# - Mid can fire on at most 8 distinct contexts
# - Each firing drains some bad configs from that context's pool of 324

# 5. ENTRY CONFLICT analysis: the real constraint
# If a context (L,S,R) is used as both mover and non-mover in the cycle,
# we need f(L,S,R) = 1-S (mover) AND f(L,S,R) = S (non-mover).
# This is impossible unless S = 1-S, i.e., never.
# So ZERO overlap is FORCED, not just observed.

print(f'\nENTRY CONFLICT: zero overlap between mover and non-mover contexts is FORCED')
print(f'(f(L,S,R)=1-S for mover, f(L,S,R)=S for non-mover; both impossible for same (L,S,R))')

# 6. Mid fires 2 times per cycle (from data: always ms[mid]=2, fires m_mid=2 times)
# Total cycle steps per proc = m_p (each proc fires exactly m_p times in good cycle)
# Wait - is that true? Let me check.

print(f'\nFiring counts in good cycles:')
print('From n=4..7 data:')
# n=4: cycle=12, n=4 procs with ms=(2,2,2,4). 2+2+2+4=10 != 12.
# Actually the fire count per proc doesn't have to equal m_p.
# Let me check from the actual data.

# Re-analyze n=4 to get fire counts
from verify_witnesses import witness_n4, witness_n5, witness_n6, witness_n7

for name, wfn in [('n=4', witness_n4), ('n=5', witness_n5), ('n=6', witness_n6), ('n=7', witness_n7)]:
    ms_w, rules = wfn()
    n_w = len(ms_w)
    fs = []
    for table in rules:
        def make_f(t):
            def f(L, S, R): return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    result = verify_system(list(ms_w), fs)
    if result['valid']:
        cycle = result['cycle']
        priv_map = {c: privileged_set(c, fs, list(ms_w)) for c in cycle}
        fire_counts = Counter()
        for c in cycle:
            p = priv_map[c]
            assert len(p) == 1
            fire_counts[p[0]] += 1

        # Find 3CB middle
        binary_pos = None
        for i in range(n_w):
            if ms_w[i] == 2 and ms_w[(i+1)%n_w] == 2 and ms_w[(i+2)%n_w] == 2:
                binary_pos = [i, (i+1)%n_w, (i+2)%n_w]
                break
        mid_w = binary_pos[1] if binary_pos else None

        fc_list = [fire_counts[i] for i in range(n_w)]
        print(f'  {name}: ms={list(ms_w)}, cycle={len(cycle)}, fires={fc_list}, mid_fires={fire_counts[mid_w]}')
        print(f'    fires/m_p: {[fc_list[i]/ms_w[i] for i in range(n_w)]}')

# 7. CRITICAL: how does the "far" config space factor?
# A config is (c_0, c_1, c_2, c_3, ..., c_{n-1})
# Context at mid=1: (c_0, c_1, c_2)
# "Far" state: (c_3, c_4, ..., c_{n-1})
# For n=8: far = (c_3, c_4, c_5, c_6, c_7) with ms = (3,3,3,3,4) -> 324 states
#
# The mover function at proc 1 sees ONLY (c_0, c_1, c_2).
# It CANNOT distinguish between different far states with the same local context.
# So if (c_0, c_1, c_2) = (1, 0, 0), mid fires regardless of far state.
# ALL 324 configs with this context either ALL fire or ALL don't fire.
#
# This is the SATURATION effect: 324 configs move identically at proc 1,
# but they scatter to different successor contexts depending on far state.

print(f'\n=== SATURATION EFFECT ===')
print(f'When mid fires on a context, ALL {product//8} configs with that context fire.')
print(f'But their successors depend on far state -> scatter across contexts.')
print(f'This means firing mid cannot selectively drain specific bad configs.')
print(f'')
print(f'At n=7: 108 configs per context. Mid fires 2 contexts -> 216 configs affected.')
print(f'At n=8: 324 configs per context. Mid fires 2 contexts -> 648 configs affected.')
data_n8_bad = 2576
print(f'But total bad ~ {data_n8_bad} at n=8.')

print(f'')
print(f'DRAIN EFFICIENCY:')
print(f'Bad configs draining via mid = configs where mid is privileged AND successor is good.')
print(f'At n=7: 37/789 = 4.7% of bad drain via mid.')
print(f'Mid fires on 216 configs total (108 per mover ctx * 2 ctx).')
print(f'But only 37 of those reach good -> 37/216 = 17.1% efficiency.')
print(f'')
print(f'At n=8 with 324 per context:')
print(f'Mid fires on 648 configs (324 * 2 mover ctx).')
print(f'If same 17% efficiency: ~110 drain -> 110/2576 = 4.3%')
print(f'But the bad graph at n=8 has SCCs, so even this draining cannot empty.')
