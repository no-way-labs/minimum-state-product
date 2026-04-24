"""
RA12 v9: Fix the cycle-closing issue.

The double-sweep word [0,8,7,...,2,1,0,8,7,...,2,1] at n=9 has each ternary
proc firing exactly 2 times. With m=3, to return to initial after 2 fires:
  +1 then +2 = +3 ≡ 0 mod 3 ✓
  +2 then +1 = +3 ≡ 0 mod 3 ✓
  +1 then +1 = +2 ✗
  +2 then +2 = +4 ≡ 1 ✗

So for each ternary proc, the first fire must be +1 and second +2, or vice versa.
This is a context-dependent transition.

Let me rebuild with these choices and check EC.
"""

import sys
from itertools import product as iprod
from collections import Counter

def check_double_sweep_n9():
    n = 9
    ms = [2, 2, 2, 3, 3, 3, 3, 3, 3]

    word = []
    for _ in range(2):
        word.append(0)
        for p in range(n-1, 0, -1):
            word.append(p)
    L = len(word)

    print(f"n={n}, ms={ms}, L={L}")
    print(f"Word: {word}")

    # Ternary procs: 3-8, each fires 2 times
    ternary_pos = list(range(3, 9))
    ternary_fire_steps = {}
    for p in ternary_pos:
        ternary_fire_steps[p] = [k for k in range(L) if word[k] == p]
        print(f"Ternary proc {p} fires at steps: {ternary_fire_steps[p]}")

    # For cycle closure with 2 fires: first fire +1, second +2 OR first +2, second +1
    # Try all 2^6 = 64 combos (for each ternary proc: choice 0 = (+1,+2), choice 1 = (+2,+1))
    # Also try all 3^6 = 729 initial values

    # Total: 729 * 64 = 46656, very feasible

    ec_free_count = 0
    ec_free_examples = []

    for t_init in iprod(range(3), repeat=6):
        for t_order in iprod(range(2), repeat=6):
            # Build ternary value sequences
            vals = [[0]*L for _ in range(n)]

            # Binary values
            current_bin = [0, 0, 0]
            for k in range(L):
                for p in range(3):
                    vals[p][k] = current_bin[p]
                if word[k] < 3:
                    current_bin[word[k]] = 1 - current_bin[word[k]]

            # Ternary values
            current_tern = {p: t_init[i] for i, p in enumerate(ternary_pos)}
            fire_count = {p: 0 for p in ternary_pos}

            for k in range(L):
                for p in ternary_pos:
                    vals[p][k] = current_tern[p]
                if word[k] in ternary_pos:
                    p = word[k]
                    idx = ternary_pos.index(p)
                    if fire_count[p] == 0:
                        # First fire
                        if t_order[idx] == 0:
                            delta = 1  # +1 first
                        else:
                            delta = 2  # +2 first
                    else:
                        # Second fire
                        if t_order[idx] == 0:
                            delta = 2  # +2 second
                        else:
                            delta = 1  # +1 second
                    current_tern[p] = (current_tern[p] + delta) % 3
                    fire_count[p] += 1

            # Check cycle closes
            closes = True
            for p in range(3):
                if current_bin[p] != 0:
                    closes = False
                    break
            if closes:
                for p in ternary_pos:
                    if current_tern[p] != t_init[ternary_pos.index(p)]:
                        closes = False
                        break

            if not closes:
                continue

            # Build configs
            configs = [tuple(vals[p][k] for p in range(n)) for k in range(L)]

            # Check distinct
            if len(set(configs)) != L:
                continue

            # Check EC at all procs
            has_ec = False
            for p in range(n):
                mc = set()
                nc = set()
                for k in range(L):
                    lv = configs[k][(p-1) % n]
                    sv = configs[k][p]
                    rv = configs[k][(p+1) % n]
                    ctx = (lv, sv, rv)
                    if word[k] == p:
                        mc.add(ctx)
                    else:
                        nc.add(ctx)
                if mc & nc:
                    has_ec = True
                    break

            if not has_ec:
                ec_free_count += 1
                if ec_free_count <= 3:
                    ec_free_examples.append({
                        'init': t_init,
                        'order': t_order,
                        'configs': configs,
                    })

    print(f"\nResults: {ec_free_count} EC-free valid cycles found")
    for ex in ec_free_examples:
        print(f"\n  Init: {ex['init']}, Order: {ex['order']}")
        print(f"  Configs: {ex['configs'][:5]}...")

        # Verify all hypotheses
        configs = ex['configs']

        # Check ri=1 isolation + gap parity
        ri_steps = [k for k in range(L) if word[k] == 1]
        gaps = []
        for idx in range(len(ri_steps)):
            a = ri_steps[idx]
            b = ri_steps[(idx+1) % len(ri_steps)]
            g = (b - a) % L
            if g == 0: g = L
            gaps.append((a, b, g))

        min_g = min(g for _, _, g in gaps)
        for a, b, g in gaps:
            if g != min_g: continue
            lf = rf = 0
            for off in range(1, g):
                s = (a + off) % L
                if word[s] == 0: lf += 1
                if word[s] == 2: rf += 1
            print(f"  Gap ({a},{b},{g}): Lf={lf}({['even','odd'][lf%2]}), Rf={rf}({['even','odd'][rf%2]})")

    if ec_free_count > 0:
        print(f"\n*** EC-FREE CYCLES EXIST AT n=9! ***")
        print("The sorry case is REAL and not closable by entry conflict.")
    else:
        print(f"\nAll valid cycles have EC at n=9 for double-sweep word.")

def check_triple_sweep_n9():
    """Try a triple sweep: 3 full sweeps so each ternary fires 3 times (divisible by 3)."""
    n = 9
    ms = [2, 2, 2, 3, 3, 3, 3, 3, 3]

    word = []
    for _ in range(3):
        word.append(0)
        for p in range(n-1, 0, -1):
            word.append(p)
    L = len(word)

    print(f"\n{'='*60}")
    print(f"Triple sweep at n=9")
    print(f"Word: {word} (L={L})")

    fc = Counter(word)
    print(f"Fire counts: {dict(sorted(fc.items()))}")

    # ri=1 fires 3 times. Is it isolated?
    ri_steps = [k for k in range(L) if word[k] == 1]
    isolated = all(word[(k+1)%L] != 1 for k in ri_steps)
    print(f"ri=1 fires at: {ri_steps}, isolated={isolated}")

    # With increment transitions: ternary fires 3 times -> returns to 0 ✓
    # Binary fires 3 times -> 3 % 2 = 1 ✗ (odd!)
    print(f"Binary fire counts: {[fc[p] for p in range(3)]} (need even)")
    print("Binary fire counts are ODD -> not a valid cycle with these fire counts")

    # Need EVEN binary fire counts. Try 4 sweeps.

def check_quad_sweep_n9():
    """4 full sweeps: binary fires 4 (even), ternary fires 4 (not div 3)."""
    n = 9
    ms = [2, 2, 2, 3, 3, 3, 3, 3, 3]

    # Actually, we can mix sweep directions.
    # CW sweep: 0, n-1, n-2, ..., 1
    # CCW sweep: 0, 1, 2, ..., n-1

    # Two CW + context-dependent ternary to close cycle
    # OR: one CW + one CCW

    # CW: [0, 8, 7, 6, 5, 4, 3, 2, 1]
    # CCW: [0, 1, 2, 3, 4, 5, 6, 7, 8]

    # CW+CCW: each proc fires 2 times, binary even ✓
    # Ternary fires 2 times, can close with (+1,+2) or (+2,+1)

    word = [0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8]
    L = len(word)

    print(f"\n{'='*60}")
    print(f"CW+CCW sweep at n=9")
    print(f"Word: {word} (L={L})")

    fc = Counter(word)
    print(f"Fire counts: {dict(sorted(fc.items()))}")

    ri_steps = [k for k in range(L) if word[k] == 1]
    isolated = all(word[(k+1)%L] != 1 for k in ri_steps)
    print(f"ri=1 fires at: {ri_steps}, isolated={isolated}")

    # MinFiringGap
    gaps = []
    for idx in range(len(ri_steps)):
        a = ri_steps[idx]
        b = ri_steps[(idx+1) % len(ri_steps)]
        g = (b - a) % L
        if g == 0: g = L
        gaps.append((a, b, g))
    min_g = min(g for _, _, g in gaps)
    print(f"Gaps: {gaps}, min={min_g}")

    for a, b, g in gaps:
        if g != min_g: continue
        lf = rf = 0
        for off in range(1, g):
            s = (a + off) % L
            if word[s] == 0: lf += 1
            if word[s] == 2: rf += 1
        print(f"Gap ({a},{b},{g}): Lf={lf}({['even','odd'][lf%2]}), Rf={rf}({['even','odd'][rf%2]})")

    # Check EC with ternary freedom
    ternary_pos = list(range(3, 9))
    ternary_fire_steps = {p: [k for k in range(L) if word[k] == p] for p in ternary_pos}

    ec_free_count = 0

    for t_init in iprod(range(3), repeat=6):
        for t_order in iprod(range(2), repeat=6):
            # Build values
            vals = [[0]*L for _ in range(n)]
            current_bin = [0, 0, 0]
            for k in range(L):
                for p in range(3):
                    vals[p][k] = current_bin[p]
                if word[k] < 3:
                    current_bin[word[k]] = 1 - current_bin[word[k]]

            current_tern = {p: t_init[i] for i, p in enumerate(ternary_pos)}
            fire_count = {p: 0 for p in ternary_pos}

            for k in range(L):
                for p in ternary_pos:
                    vals[p][k] = current_tern[p]
                if word[k] in ternary_pos:
                    p = word[k]
                    idx = ternary_pos.index(p)
                    if fire_count[p] == 0:
                        delta = 1 if t_order[idx] == 0 else 2
                    else:
                        delta = 2 if t_order[idx] == 0 else 1
                    current_tern[p] = (current_tern[p] + delta) % 3
                    fire_count[p] += 1

            closes = all(current_bin[p] == 0 for p in range(3))
            if closes:
                for p in ternary_pos:
                    if current_tern[p] != t_init[ternary_pos.index(p)]:
                        closes = False
                        break
            if not closes:
                continue

            configs = [tuple(vals[p][k] for p in range(n)) for k in range(L)]
            if len(set(configs)) != L:
                continue

            has_ec = False
            for p in range(n):
                mc = set()
                nc = set()
                for k in range(L):
                    lv = configs[k][(p-1) % n]
                    sv = configs[k][p]
                    rv = configs[k][(p+1) % n]
                    ctx = (lv, sv, rv)
                    if word[k] == p:
                        mc.add(ctx)
                    else:
                        nc.add(ctx)
                if mc & nc:
                    has_ec = True
                    break

            if not has_ec:
                ec_free_count += 1
                if ec_free_count <= 2:
                    print(f"\n  EC-FREE: init={t_init}, order={t_order}")
                    # Show gap parity
                    for a, b, g in gaps:
                        if g != min_g: continue
                        lf = rf = 0
                        for off in range(1, g):
                            s = (a + off) % L
                            if word[s] == 0: lf += 1
                            if word[s] == 2: rf += 1
                        print(f"    Gap Lf={lf}, Rf={rf}")

    print(f"\nEC-free valid cycles for CW+CCW: {ec_free_count}")
    if ec_free_count > 0:
        print("*** EC-FREE CYCLES EXIST ***")

if __name__ == '__main__':
    print("=" * 60)
    print("RA12 v9: Cycle closure fix")
    print("=" * 60)

    check_double_sweep_n9()
    check_triple_sweep_n9()
    check_quad_sweep_n9()
