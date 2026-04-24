#!/usr/bin/env python3
"""Compute key ratios and growth analysis for 3CB context saturation."""

# Data from analysis runs
# n, product, cfg/ctx, cycle_len, mover_ctx, bad, max_depth, mid_drain, valid
data = {
    4: {'product': 32, 'cfg_ctx': 4, 'cycle': 12, 'mctx': 2, 'bad': 19, 'depth': 11, 'drain_pct': 26.3, 'valid': True},
    5: {'product': 96, 'cfg_ctx': 12, 'cycle': 18, 'mctx': 2, 'bad': 77, 'depth': 21, 'drain_pct': 15.6, 'valid': True},
    6: {'product': 288, 'cfg_ctx': 36, 'cycle': 35, 'mctx': 2, 'bad': 231, 'depth': 43, 'drain_pct': 15.2, 'valid': True},
    7: {'product': 864, 'cfg_ctx': 108, 'cycle': 52, 'mctx': 2, 'bad': 789, 'depth': 65, 'drain_pct': 4.7, 'valid': True},
    8: {'product': 2592, 'cfg_ctx': 324, 'cycle': 16, 'mctx': 2, 'bad': 2576, 'depth': None, 'drain_pct': None, 'valid': False,
        'recurrent_bad': 384, 'n_sccs': 75},
}

print('=' * 110)
print('3CB CONTEXT SATURATION TABLE')
print('=' * 110)

print(f'{"n":>3} {"prod":>6} {"total":>6} {"cfg/ctx":>8} {"cycle":>6} {"mctx":>5} {"good":>6} {"bad":>6} {"depth":>6} {"bottleneck":>11} {"drain%":>7} {"valid":>6}')
print('-' * 110)

for n in sorted(data):
    d = data[n]
    good = d['product'] - d['bad']
    bottleneck = d['bad'] / (d['cycle'] * d['mctx'])
    depth_str = str(d['depth']) if d['depth'] is not None else 'INF'
    drain_str = f"{d['drain_pct']:.1f}" if d['drain_pct'] is not None else 'N/A'
    valid_str = 'YES' if d['valid'] else 'NO'
    print(f"{n:3d} {d['product']:6d} {d['product']:6d} {d['cfg_ctx']:8d} {d['cycle']:6d} {d['mctx']:5d} {good:6d} {d['bad']:6d} {depth_str:>6} {bottleneck:11.2f} {drain_str:>7} {valid_str:>6}")

print()
print('GROWTH ANALYSIS:')
print(f'{"n":>3} {"cfg/ctx_ratio":>14} {"cycle_ratio":>12} {"bad_ratio":>10} {"bottleneck_ratio":>16}')
print('-' * 60)
prev = None
for n in sorted(data):
    d = data[n]
    bn = d['bad'] / (d['cycle'] * d['mctx'])
    if prev is not None:
        cr = d['cfg_ctx'] / prev['cfg_ctx']
        cycr = d['cycle'] / prev['cycle']
        br = d['bad'] / prev['bad']
        bnr = bn / prev_bn
        print(f"{n:3d} {cr:14.2f}x {cycr:12.2f}x {br:10.2f}x {bnr:16.2f}x")
    prev = d
    prev_bn = bn

print()
print('KEY FINDINGS:')
print()
print('1. MOVER CONTEXTS FIXED: Always exactly 2/8 at middle binary proc (n=4..8)')
print('   The middle binary proc fires on exactly 2 context triples: (0,1,x) and (1,0,y)')
print('   These are the "transition" contexts where the binary value changes.')
print()
print('2. ZERO OVERLAP: Mover and non-mover contexts never overlap at middle binary')
print('   This means the transition function at mid is FULLY DETERMINED by the cycle:')
print('   mover contexts -> flip, non-mover contexts -> keep')
print()
print('3. CONFIGS PER CONTEXT: Grows as 3x per n')
print('   cfg/ctx = product / 8 = product / (m_L * m_S * m_R)')
print('   Since product triples each n (adding a ternary proc), cfg/ctx triples.')
print()
print('4. CYCLE LENGTH: Grows sublinearly')
print('   n=4: 12, n=5: 18, n=6: 35, n=7: 52, n=8: ~16 (best found)')
print('   Ratio cycle/n: 3.0, 3.6, 5.8, 7.4')
print()
print('5. BOTTLENECK RATIO = bad / (cycle * mover_ctx):')
print('   n=4: 0.79, n=5: 2.14, n=6: 3.30, n=7: 7.59, n=8: 80.5')
print('   The ratio measures how many bad configs each mover-context step must drain.')
print('   At n=8 it jumps 10.6x (vs ~2-3x for prior steps).')
print()
print('6. MID DRAIN RATE: Fraction of bad configs that drain via mid firing')
print('   n=4: 26.3%, n=5: 15.6%, n=6: 15.2%, n=7: 4.7%')
print('   Declining rapidly. The middle binary proc becomes less and less')
print('   effective at draining bad configs as n grows.')
print()
print('7. RECURRENT BAD at n=8: 384 configs in 75 SCCs')
print('   Context distribution in SCCs is UNIFORM across all 8 contexts (~15% each)')
print('   This means the trap is not localized to specific contexts.')
print()

# Key quantitative threshold
print('QUANTITATIVE THRESHOLD PREDICTION:')
print()
print('The bottleneck ratio grows as: product / (cycle_len * 2)')
print('Product ~ 4 * 3^(n-2), cycle_len ~ O(n)')
print('So bottleneck ~ 2 * 3^(n-2) / n')
print()
for n in range(4, 12):
    theoretical_bn = 2 * 3**(n-2) / n
    print(f'  n={n}: theoretical bottleneck ~ {theoretical_bn:.1f}')
print()
print('The transition happens when bottleneck exceeds ~10:')
print('  n=7: 7.59 (works)')
print('  n=8: 80.5 (fails)')
print()
print('But the REAL threshold is the convergence depth vs bad DAG depth.')
print('At n=7: depth=65, product=864 -> depth/product = 7.5%')
print('At n=8: depth=INF (SCCs exist) -> convergence impossible')
print()
print('The cfg/ctx = 324 at n=8 means each of 2 mover contexts must drain')
print('~162 bad configs. The cycle gives only ~8 steps per mover context.')
print('That is 162/8 = 20.25 bad configs per cycle step per context.')
print('The transition function has only 2 possible outputs per context.')
print('This creates a PACKING PROBLEM: too many bad configs sharing the same')
print('context need different drain paths, but the binary proc has only 2 states.')
