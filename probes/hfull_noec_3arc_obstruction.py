#!/usr/bin/env python3
"""
3-ARC OBSTRUCTION: Why can't the walk extend to 3 active procs at n≥7?

The walk is ring-adjacent under ¬EC. It's always found to be a 2-proc
oscillation. What happens when we FORCE 3 procs?

Method: Generate random systems, run daemon that FORCES the walk to
visit 3 procs, then check if the resulting cycle has EC.
If it ALWAYS has EC when 3+ procs fire, that's the obstruction.

Also: check WHERE the EC occurs (at which proc, mover or boundary).
"""
import random
from collections import Counter

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def ec_at_proc(configs, movers, n, p):
    CL = len(configs)
    mt = set()
    nmt = set()
    for k in range(CL):
        triple = (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n])
        if movers[k] == p:
            mt.add(triple)
        else:
            nmt.add(triple)
    return mt & nmt

def has_entry_conflict(configs, movers, n):
    for p in range(n):
        if ec_at_proc(configs, movers, n, p):
            return True
    return False

def force_3proc_cycle(n, ms, proc_triple, num_trials=500000):
    """Try to find a good cycle where exactly procs a,b,c fire, with ¬EC."""
    a, b, c = proc_triple
    target = {a, b, c}
    found_cycles = 0
    found_noec = 0
    ec_location = Counter()

    for trial in range(num_trials):
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        history = [config]
        history_movers = []
        config_to_step = {config: 0}

        for step in range(5000):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break

            # Force: only fire procs in target set
            target_privs = [p for p in privs if p in target]
            if not target_privs:
                break
            p = random.choice(target_privs)

            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)

            if config in config_to_step:
                cs = config_to_step[config]
                cycle_configs = history[cs:]
                cycle_movers = history_movers[cs:] + [p]
                CL = len(cycle_configs)

                fc = [0]*n
                for m in cycle_movers:
                    fc[m] += 1
                active = {i for i in range(n) if fc[i] > 0}

                if active == target or (len(active) >= 3 and active.issubset(target)):
                    found_cycles += 1
                    ec = has_entry_conflict(cycle_configs, cycle_movers, n)
                    if not ec:
                        found_noec += 1
                    else:
                        for pp in range(n):
                            conflict = ec_at_proc(cycle_configs, cycle_movers, n, pp)
                            if conflict:
                                rel = 'active' if pp in active else 'inactive'
                                ec_location[f'P{pp}({rel},m={ms[pp]})'] += 1
                break

            config_to_step[config] = step + 1
            history.append(config)
            history_movers.append(p)

    return found_cycles, found_noec, ec_location

def main():
    print("3-ARC OBSTRUCTION ANALYSIS")
    print("="*70)

    for n in [7, 9]:
        if n == 7:
            ms = [2, 3, 2, 3, 2, 3, 3]
        else:
            ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]

        binary_pos = [i for i in range(n) if ms[i] == 2]

        print(f"\nn={n}, ms={ms}")
        print(f"Binary at: {binary_pos}")

        # Try 3-proc arcs: {p-1, p, p+1} for various p
        # Include arcs that cross binary procs
        arcs = []
        for p in range(n):
            arc = ((p-1)%n, p, (p+1)%n)
            contains_binary = any(ms[q] == 2 for q in arc)
            arcs.append((arc, contains_binary))

        for arc, has_bin in arcs:
            a, b, c = arc
            types = f"({ms[a]},{ms[b]},{ms[c]})"
            label = f"[P{a},P{b},P{c}] types={types}"
            if has_bin:
                label += " *binary*"

            found, noec, ec_loc = force_3proc_cycle(n, ms, arc, num_trials=200000)
            print(f"\n  Arc {label}:")
            print(f"    3-active cycles found: {found}")
            print(f"    ¬EC: {noec}")
            if ec_loc:
                top3 = ec_loc.most_common(3)
                print(f"    EC location: {dict(top3)}")

    print("\n" + "="*70)
    print("INTERPRETATION")
    print("="*70)
    print("""
If ALL 3-proc arcs have 0 ¬EC cycles, the walk cannot extend to 3 procs.

The EC location tells us WHERE the conflict arises:
- If EC is always at the BINARY proc in the arc: binary crossing is the obstruction.
- If EC is at the MIDDLE proc: the intermediate proc gets trapped.
- If EC is at an INACTIVE proc: even procs that don't fire get conflicted.
""")

if __name__ == '__main__':
    main()
