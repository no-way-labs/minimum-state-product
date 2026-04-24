#!/usr/bin/env python3
"""CIC Exploration 4b: Analyze WHY MNU holds for bounce cycles.

Key finding from 4a: MNU holds for CLB bounce cycles (n=5..9).
This script investigates the structural reason.

The bounce cycle has movers [0,1,...,n-1,n-2,...,1,0,1,...,n-1].
Unlike the waterfall (sweep) structure, what ensures uniqueness?

Hypothesis: The bounce cycle has a "V-waterfall" structure where
configs form two half-waterfalls (up and down), and the V-shape
guarantees that post-move neighborhoods are unique.
"""

from itertools import product as iproduct
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))


def build_clb_bounce(n):
    """Build CLB bounce cycle for ms=(2,3,...,3,2)."""
    ms = tuple([2] + [3] * (n - 2) + [2])
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    movers = None
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            return None, None, None
        visited.add(nc)
        cycle.append(nc)
    return ms, cycle, movers


def build_sweep_cycle(ms, n, v_vals=None):
    """Build uniform sweep cycle for given ms."""
    if v_vals is None:
        v_vals = [1] * n
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    sweep = list(range(n)) * 10
    movers = None
    for step, mover in enumerate(sweep):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = sweep[:step + 1]
            break
        if nc in visited:
            return None, None
        visited.add(nc)
        cycle.append(nc)
    return cycle, movers


# ============================================================
# Analyze bounce cycle structure for n=5,6,7,9
# ============================================================
print("=" * 70)
print("BOUNCE CYCLE STRUCTURE ANALYSIS")
print("=" * 70)

for n in [5, 6, 7, 9]:
    ms, cycle, movers = build_clb_bounce(n)
    if cycle is None:
        print(f"\nn={n}: FAILED")
        continue

    L = len(cycle)
    print(f"\nn={n}, ms={list(ms)}, L={L}")
    print(f"  Movers: {movers}")

    # Show configs with movers
    print(f"\n  Step  Mover  Config")
    for idx in range(L):
        c = cycle[idx]
        mv = movers[idx]
        c_next = cycle[(idx + 1) % L]
        print(f"  {idx:3d}   P{mv}     {list(c)}"
              f"  → [{','.join(str(x) for x in c_next)}]")

    # For each mover step, show the post-move neighborhood (L, S', R)
    print(f"\n  Step  Mover  Pre-nbhd (L,S,R)  Post-nbhd (L,S',R)")
    post_move_nbhds = {}  # (proc, L, S', R) → step
    for step in range(L):
        p = movers[step]
        gc = cycle[step]
        gc_next = cycle[(step + 1) % L]
        L_val = gc[(p - 1) % n]
        S = gc[p]
        S_prime = gc_next[p]
        R = gc[(p + 1) % n]
        pre = (L_val, S, R)
        post = (L_val, S_prime, R)

        key = (p, L_val, S_prime, R)
        dup = ""
        if key in post_move_nbhds:
            dup = f"  *** DUPLICATE of step {post_move_nbhds[key]}"
        post_move_nbhds[key] = step

        print(f"  {step:3d}   P{p}     {pre}             {post}{dup}")

    # Check: for each step, is the post-move (L, S', R) triple unique in C?
    violations = 0
    for step in range(L):
        p = movers[step]
        gc_next = cycle[(step + 1) % L]
        L_val = cycle[step][(p - 1) % n]
        S_prime = gc_next[p]
        R = cycle[step][(p + 1) % n]

        matches = sum(1 for j, gj in enumerate(cycle)
                      if gj[(p - 1) % n] == L_val
                      and gj[p] == S_prime
                      and gj[(p + 1) % n] == R)
        if matches != 1:
            violations += 1
            print(f"  !! Step {step} P{p}: ({L_val},{S_prime},{R})"
                  f" has {matches} matches in C")

    print(f"\n  MNU: {'OK' if violations == 0 else f'{violations} violations'}")

    # Analyze firing pattern per processor
    from collections import Counter
    fire_count = Counter(movers)
    print(f"  Firings: {dict(sorted(fire_count.items()))}")

    # For each processor, show its state trajectory through the cycle
    print(f"\n  Processor state trajectories:")
    for p in range(n):
        traj = [cycle[idx][p] for idx in range(L)]
        fire_steps = [idx for idx in range(L) if movers[idx] == p]
        print(f"    P{p} (m={ms[p]}): states={traj}, "
              f"fires at steps {fire_steps}")


# ============================================================
# Compare: sweep cycle structure
# ============================================================
print(f"\n{'=' * 70}")
print("SWEEP CYCLE STRUCTURE COMPARISON")
print("=" * 70)

for n in [5, 7]:
    # Build sweep on all-ternary (Sol 3 type)
    ms_t = tuple([3] * n)
    cycle, movers = build_sweep_cycle(ms_t, n)
    if cycle is None:
        continue

    L = len(cycle)
    print(f"\nn={n}, ms={list(ms_t)}, L={L}")
    print(f"  Movers: {movers}")

    print(f"\n  Step  Mover  Config")
    for idx in range(min(L, 30)):
        c = cycle[idx]
        mv = movers[idx]
        print(f"  {idx:3d}   P{mv}     {list(c)}")

    # State trajectories
    print(f"\n  Processor state trajectories:")
    for p in range(n):
        traj = [cycle[idx][p] for idx in range(L)]
        fire_steps = [idx for idx in range(L) if movers[idx] == p]
        print(f"    P{p}: states={traj}, fires at {fire_steps}")


# ============================================================
# Key structural comparison: determinacy per processor
# ============================================================
print(f"\n{'=' * 70}")
print("ENTRY DETERMINACY: BOUNCE vs SWEEP")
print("=" * 70)

for n in [5, 7, 9]:
    # Bounce
    ms_b, cycle_b, movers_b = build_clb_bounce(n)
    if cycle_b is None:
        continue

    # Count determined entries per processor
    det_b = {}
    for idx in range(len(cycle_b)):
        c = cycle_b[idx]
        c_next = cycle_b[(idx + 1) % len(cycle_b)]
        mv = movers_b[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det_b[key] = c_next[p]
            else:
                det_b[key] = S

    # Count per processor
    det_per_proc_b = {}
    total_per_proc_b = {}
    for p in range(n):
        m_L = ms_b[(p - 1) % n]
        m_S = ms_b[p]
        m_R = ms_b[(p + 1) % n]
        total = m_L * m_S * m_R
        determined = sum(1 for L in range(m_L) for S in range(m_S)
                         for R in range(m_R) if (p, L, S, R) in det_b)
        det_per_proc_b[p] = determined
        total_per_proc_b[p] = total

    # Sweep on same ms
    cycle_s, movers_s = build_sweep_cycle(ms_b, n)
    if cycle_s is not None:
        det_s = {}
        for idx in range(len(cycle_s)):
            c = cycle_s[idx]
            c_next = cycle_s[(idx + 1) % len(cycle_s)]
            mv = movers_s[idx]
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                if p == mv:
                    det_s[key] = c_next[p]
                else:
                    det_s[key] = S

        det_per_proc_s = {}
        for p in range(n):
            m_L = ms_b[(p - 1) % n]
            m_S = ms_b[p]
            m_R = ms_b[(p + 1) % n]
            determined = sum(1 for L in range(m_L) for S in range(m_S)
                             for R in range(m_R) if (p, L, S, R) in det_s)
            det_per_proc_s[p] = determined

        print(f"\nn={n}, ms={list(ms_b)}")
        print(f"  {'Proc':>4}  {'Total':>5}  {'Bounce':>6}  {'Sweep':>5}"
              f"  {'Diff':>4}")
        for p in range(n):
            total = total_per_proc_b[p]
            b = det_per_proc_b[p]
            s = det_per_proc_s.get(p, 0)
            print(f"  P{p:>2}   {total:>5}  {b:>6}  {s:>5}  {b-s:>+4}")

        total_b = sum(det_per_proc_b.values())
        total_s = sum(det_per_proc_s.values())
        total_all = sum(total_per_proc_b.values())
        print(f"  ALL   {total_all:>5}  {total_b:>6}  {total_s:>5}"
              f"  {total_b-total_s:>+4}")
    else:
        print(f"\nn={n}, ms={list(ms_b)}: sweep cycle failed")


# ============================================================
# CRITICAL: Test MNU for OTHER non-sweep cycles
# ============================================================
print(f"\n{'=' * 70}")
print("TEST: MNU FOR VARIED CYCLE TYPES ON ms=(2,3,3,3,2)")
print("=" * 70)

n = 5
ms = (2, 3, 3, 3, 2)

# Type 1: Bounce (already known to work)
_, cycle_bounce, movers_bounce = build_clb_bounce(n)

# Type 2: Reversed bounce (movers go n-1,n-2,...,0,1,...,n-2,n-1,...)
up_down_rev = list(range(n - 1, -1, -1)) + list(range(1, n - 1))
config = [0] * n
cycle_rev = [tuple(config)]
visited = {tuple(config)}
full = up_down_rev * 10
movers_rev = None
for step, mover in enumerate(full):
    config = list(cycle_rev[-1])
    config[mover] = (config[mover] + 1) % ms[mover]
    nc = tuple(config)
    if nc == cycle_rev[0]:
        movers_rev = full[:step + 1]
        break
    if nc in visited:
        break
    visited.add(nc)
    cycle_rev.append(nc)

# Type 3: Zigzag (0,2,4,1,3,0,2,4,1,3,...)
zigzag = [0, 2, 4, 1, 3]
config = [0] * n
cycle_zz = [tuple(config)]
visited = {tuple(config)}
full = zigzag * 20
movers_zz = None
for step, mover in enumerate(full):
    config = list(cycle_zz[-1])
    config[mover] = (config[mover] + 1) % ms[mover]
    nc = tuple(config)
    if nc == cycle_zz[0]:
        movers_zz = full[:step + 1]
        break
    if nc in visited:
        break
    visited.add(nc)
    cycle_zz.append(nc)

# Type 4: Double sweep (each proc fires twice before moving on)
double_sweep = []
for p in range(n):
    double_sweep.extend([p, p])
config = [0] * n
cycle_ds = [tuple(config)]
visited = {tuple(config)}
full = double_sweep * 10
movers_ds = None
for step, mover in enumerate(full):
    config = list(cycle_ds[-1])
    config[mover] = (config[mover] + 1) % ms[mover]
    nc = tuple(config)
    if nc == cycle_ds[0]:
        movers_ds = full[:step + 1]
        break
    if nc in visited:
        break
    visited.add(nc)
    cycle_ds.append(nc)

candidates = [
    ("Bounce", cycle_bounce, movers_bounce),
    ("Reverse bounce", cycle_rev if movers_rev else None, movers_rev),
    ("Zigzag", cycle_zz if movers_zz else None, movers_zz),
    ("Double sweep", cycle_ds if movers_ds else None, movers_ds),
]

for name, cyc, mvrs in candidates:
    if cyc is None or mvrs is None:
        print(f"\n  {name}: no cycle found")
        continue

    L = len(cyc)
    # Check MNU
    violations = 0
    for step in range(L):
        p = mvrs[step]
        gc_next = cyc[(step + 1) % L]
        L_val = cyc[step][(p - 1) % n]
        S_prime = gc_next[p]
        R = cyc[step][(p + 1) % n]
        matches = sum(1 for j, gj in enumerate(cyc)
                      if gj[(p - 1) % n] == L_val
                      and gj[p] == S_prime
                      and gj[(p + 1) % n] == R)
        if matches != 1:
            violations += 1

    # Check escape
    det = {}
    for idx in range(L):
        c = cyc[idx]
        c_next = cyc[(idx + 1) % L]
        mv = mvrs[idx]
        for p in range(n):
            Lv = c[(p - 1) % n]
            S = c[p]
            Rv = c[(p + 1) % n]
            key = (p, Lv, S, Rv)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    good_set = set(cyc)
    escape_fails = 0
    total_forced = 0
    for c in iproduct(*[range(m) for m in ms]):
        if c in good_set:
            continue
        for i in range(n):
            Lv, S, Rv = c[(i - 1) % n], c[i], c[(i + 1) % n]
            key = (i, Lv, S, Rv)
            if key in det and det[key] != S:
                total_forced += 1
                new_c = list(c)
                new_c[i] = det[key]
                if tuple(new_c) in good_set:
                    escape_fails += 1

    print(f"\n  {name}: L={L}, movers={mvrs}")
    print(f"    MNU: {'OK' if violations == 0 else f'{violations} violations'}")
    print(f"    Escape: {escape_fails}/{total_forced} failures")
    print(f"    Determined: {len(det)}/87 entries")
