#!/usr/bin/env python3
"""Deep investigation: WHY does the mechanism always fire?

For every valid system with ≥3 binary, sub-threshold, hno_safe, n≥5:
- Extract ALL phases of ALL procs with both binary neighbors
- Check if mechanism fires
- If normal form: print detailed diagnostics

Also check: does the no-pivot case ever occur?
And: what makes the mechanism always fire?
"""
import random
from collections import defaultdict

def random_transition(m_left, m_self, m_right):
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f

def privileged(config, sys_f, ms, n, i):
    return sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]

def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    return privs[0] if len(privs) == 1 else None

def apply_move(config, sys_f, ms, n, i):
    nc = list(config)
    nc[i] = sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])]
    return tuple(nc)

def find_good_cycle(sys_f, ms, n, max_steps=5000):
    config = tuple(random.randint(0, ms[i]-1) for i in range(n))
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start = visited[config]
            cycle = []
            c = config
            for _ in range(step - start):
                p = find_unique_privileged(c, sys_f, ms, n)
                if p is None: return None
                cycle.append((c, p))
                c = apply_move(c, sys_f, ms, n, p)
            for c2, _ in cycle:
                if find_unique_privileged(c2, sys_f, ms, n) is None:
                    return None
            return cycle
        visited[config] = step
        p = find_unique_privileged(config, sys_f, ms, n)
        if p is None: return None
        config = apply_move(config, sys_f, ms, n, p)
    return None

def check_hno_safe(cycle, ms, n):
    movers = [p for _, p in cycle]
    for q in range(n):
        visited = any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers)
        if not visited:
            return False
    return True

def analyze_all_phases(cycle, ms, n):
    """Analyze all phases of all procs with both binary neighbors."""
    L = len(cycle)
    movers = [p for _, p in cycle]

    results = {
        'total_phases': 0,
        'mechanism_phases': 0,
        'normal_form_phases': 0,
        'pivot_exists': False,
        'phase_details': []
    }

    for t in range(n):
        lt, rt = (t-1)%n, (t+1)%n
        if ms[lt] != 2 or ms[rt] != 2:
            continue

        # t has both binary neighbors
        fire_steps = [k for k in range(L) if movers[k] == t]
        fc = len(fire_steps)
        if fc == 0:
            continue

        results['pivot_exists'] = True

        if fc < 2:
            continue  # fireCount_ne_one should prevent fc=1

        # Analyze each phase (gap between consecutive fires)
        for idx in range(len(fire_steps)):
            s = fire_steps[idx]
            prev_fire = fire_steps[(idx - 1) % len(fire_steps)]

            # Phase [a, s) where a = prev_fire + 1 (mod L)
            if prev_fire < s:
                a = prev_fire + 1
                phase_steps = list(range(a, s))
            else:
                # Wrap-around phase
                phase_steps = list(range(prev_fire + 1, L)) + list(range(0, s))

            if not phase_steps:
                continue

            # Count J (left fires) and K (right fires) in phase
            J = sum(1 for k in phase_steps if movers[k] == lt)
            K = sum(1 for k in phase_steps if movers[k] == rt)

            results['total_phases'] += 1

            # Check mechanism
            both_even = (J % 2 == 0) and (K % 2 == 0)
            toggle_l = (J >= 2) and (K == 0)
            toggle_r = (J == 0) and (K >= 2)

            if both_even or toggle_l or toggle_r:
                results['mechanism_phases'] += 1
            else:
                results['normal_form_phases'] += 1
                results['phase_details'].append({
                    't': t, 'J': J, 'K': K,
                    'phase_len': len(phase_steps),
                    'movers_in_phase': [movers[k] for k in phase_steps],
                    'a': phase_steps[0] if phase_steps else -1,
                    's': s
                })

    return results

def main():
    random.seed(42)

    configs = [
        (5, [2,2,2,3,3]),
        (5, [2,3,2,3,3]),
        (7, [2,2,2,3,3,3,3]),
        (7, [2,3,2,3,3,3,3]),
        (9, [2,2,2,3,3,3,3,3,3]),
        (9, [2,3,2,3,3,3,3,3,3]),
        (9, [2,2,3,2,3,3,3,3,3]),
    ]

    total_nf = 0
    total_phases = 0
    total_cycles_nosafe = 0
    nf_by_jk = defaultdict(int)
    nf_by_phaselen = defaultdict(int)

    for n, ms in configs:
        local_nf = 0
        local_phases = 0
        local_cycles = 0

        for trial in range(200000 if n <= 7 else 50000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

            cycle = find_good_cycle(sys_f, ms, n)
            if cycle is None:
                continue

            if not check_hno_safe(cycle, ms, n):
                continue

            local_cycles += 1
            results = analyze_all_phases(cycle, ms, n)
            local_phases += results['total_phases']
            local_nf += results['normal_form_phases']

            for detail in results['phase_details']:
                nf_by_jk[(detail['J'], detail['K'])] += 1
                nf_by_phaselen[detail['phase_len']] += 1
                if local_nf <= 5:
                    print(f"  NORMAL FORM! n={n} ms={ms} t={detail['t']} "
                          f"J={detail['J']} K={detail['K']} plen={detail['phase_len']}")
                    print(f"    movers: {detail['movers_in_phase']}")

        print(f"n={n} ms={ms}: {local_cycles} cycles w/nosafe, "
              f"{local_phases} phases, {local_nf} normal-form")
        total_nf += local_nf
        total_phases += local_phases
        total_cycles_nosafe += local_cycles

    print(f"\n=== TOTALS: {total_cycles_nosafe} cycles, {total_phases} phases, "
          f"{total_nf} normal-form ===")

    if total_nf > 0:
        print(f"\nNormal form by (J,K): {dict(nf_by_jk)}")
        print(f"Normal form by phase_len: {dict(nf_by_phaselen)}")
    else:
        print("\nMECHANISM ALWAYS FIRES with hno_safe!")
        print("The normal form case is genuinely dead code.")
        print("\nTo close the sorry: prove that with hno_safe + n >= 9,")
        print("every phase has (Even J ∧ Even K) ∨ (J>=2 ∧ K=0) ∨ (J=0 ∧ K>=2).")

    # Now investigate WITHOUT hno_safe to understand what makes it work
    print("\n\n=== WITHOUT hno_safe ===")
    nf_nosafe = 0
    phases_nosafe = 0
    nf_details_nosafe = []

    for n, ms in [(5, [2,2,2,3,3]), (7, [2,2,2,3,3,3,3])]:
        for trial in range(200000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

            cycle = find_good_cycle(sys_f, ms, n)
            if cycle is None:
                continue

            results = analyze_all_phases(cycle, ms, n)
            phases_nosafe += results['total_phases']
            nf_nosafe += results['normal_form_phases']

            for detail in results['phase_details']:
                if len(nf_details_nosafe) < 20:
                    nf_details_nosafe.append((n, ms, detail))

    print(f"Without hno_safe: {phases_nosafe} phases, {nf_nosafe} normal-form")
    if nf_details_nosafe:
        print(f"\nSample normal-form phases (without hno_safe):")
        for n, ms, d in nf_details_nosafe[:10]:
            print(f"  n={n} t={d['t']} J={d['J']} K={d['K']} plen={d['phase_len']} "
                  f"movers={d['movers_in_phase']}")

if __name__ == '__main__':
    main()
