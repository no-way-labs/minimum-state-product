#!/usr/bin/env python3
"""WHY does the mechanism always fire?

Forget hno_safe for now. Focus on the simpler question:
For a proc t with both binary neighbors that fires ≥ 2 times,
WHEN does the normal form occur vs not?

The mechanism fires when:
  (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)

Normal form (none fires) requires:
  At least one of J, K odd, AND J≥2 → K≥1, AND K≥2 → J≥1.

Key question: what STRUCTURAL property of the cycle prevents normal form?

Hypotheses:
1. Is it about phase_len? (Normal form only at phase_len=1?)
2. Is it about the TOTAL fire counts F_L, F_R?
3. Is it about the relationship between F_L, F_R and the number of phases F?
4. Is it about the mover ORDERING within phases?

Let's test WITHOUT hno_safe to get actual normal-form examples,
then analyze what makes them special.
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

def analyze_cycle(cycle, ms, n, t):
    """Full analysis of proc t's phases."""
    L = len(cycle)
    movers = [p for _, p in cycle]
    lt, rt = (t-1)%n, (t+1)%n

    fire_steps = [k for k in range(L) if movers[k] == t]
    F = len(fire_steps)
    if F < 2:
        return None

    F_L = sum(1 for m in movers if m == lt)
    F_R = sum(1 for m in movers if m == rt)

    phases = []
    for idx in range(F):
        s = fire_steps[idx]
        prev = fire_steps[(idx-1) % F]
        if prev < s:
            phase_movers = movers[prev+1:s]
        else:
            phase_movers = movers[prev+1:] + movers[:s]

        J = sum(1 for m in phase_movers if m == lt)
        K = sum(1 for m in phase_movers if m == rt)
        plen = len(phase_movers)

        both_even = (J % 2 == 0) and (K % 2 == 0)
        toggle_l = (J >= 2) and (K == 0)
        toggle_r = (J == 0) and (K >= 2)
        mechanism = both_even or toggle_l or toggle_r

        phases.append({
            'J': J, 'K': K, 'plen': plen,
            'mechanism': mechanism,
            'type': 'BE' if both_even else ('TL' if toggle_l else ('TR' if toggle_r else 'NF'))
        })

    return {
        'F': F, 'F_L': F_L, 'F_R': F_R, 'L': L,
        'phases': phases,
        'all_mechanism': all(p['mechanism'] for p in phases),
        'has_normal_form': any(not p['mechanism'] for p in phases),
    }

def main():
    random.seed(777)

    # Test 1: When does normal form occur? (Without hno_safe)
    print("=== TEST 1: Normal form occurrence patterns ===\n")

    nf_examples = []
    mech_examples = []

    for n, ms in [(5, [2,2,2,3,3]), (5, [2,3,2,3,3]), (7, [2,2,2,3,3,3,3])]:
        for trial in range(200000):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            cycle = find_good_cycle(sys_f, ms, n)
            if cycle is None:
                continue

            for t in range(n):
                lt, rt = (t-1)%n, (t+1)%n
                if ms[lt] != 2 or ms[rt] != 2:
                    continue
                result = analyze_cycle(cycle, ms, n, t)
                if result is None:
                    continue

                if result['has_normal_form']:
                    if len(nf_examples) < 50:
                        nf_examples.append((n, ms, t, result))
                else:
                    if len(mech_examples) < 50:
                        mech_examples.append((n, ms, t, result))

    print(f"Normal-form examples: {len(nf_examples)}")
    print(f"All-mechanism examples: {len(mech_examples)}")

    # Analyze normal-form examples
    print("\n--- Normal-form cycle properties ---")
    for n, ms, t, r in nf_examples[:20]:
        nf_phases = [p for p in r['phases'] if not p['mechanism']]
        print(f"  n={n} t={t} F={r['F']} F_L={r['F_L']} F_R={r['F_R']} L={r['L']}")
        print(f"    phases: {[(p['J'],p['K'],p['plen'],p['type']) for p in r['phases']]}")
        print(f"    NF phases: {[(p['J'],p['K'],p['plen']) for p in nf_phases]}")

    # Key statistics
    print("\n--- Statistics ---")
    nf_plens = []
    nf_jk = defaultdict(int)
    nf_F_vals = []
    nf_FL_vals = []
    nf_FR_vals = []
    for _, _, _, r in nf_examples:
        nf_F_vals.append(r['F'])
        nf_FL_vals.append(r['F_L'])
        nf_FR_vals.append(r['F_R'])
        for p in r['phases']:
            if not p['mechanism']:
                nf_plens.append(p['plen'])
                nf_jk[(p['J'], p['K'])] += 1

    if nf_plens:
        print(f"NF phase_lens: {sorted(set(nf_plens))} (unique values)")
        print(f"NF (J,K) distribution: {dict(nf_jk)}")
        print(f"NF cycle F values: min={min(nf_F_vals)} max={max(nf_F_vals)}")
        print(f"NF cycle F_L values: min={min(nf_FL_vals)} max={max(nf_FL_vals)}")
        print(f"NF cycle F_R values: min={min(nf_FR_vals)} max={max(nf_FR_vals)}")

    # Test 2: What's special about hno_safe cycles?
    print("\n\n=== TEST 2: What does hno_safe prevent? ===\n")

    # Check: do normal-form examples have safe processors?
    safe_count = 0
    nosafe_count = 0
    for n, ms, t, r in nf_examples:
        # Reconstruct movers
        # (we don't have them stored, so just count)
        safe_count += 1  # We know all NF examples lack hno_safe

    print(f"All {len(nf_examples)} NF examples have safe processors (from earlier tests)")
    print("hno_safe prevents normal form because:")
    print("  - NF only at phase_len=1 (J+K=1)")
    print("  - phase_len=1 means t fires at near-consecutive steps")
    print("  - Near-consecutive t-fires mean the mover stays near t")
    print("  - Staying near t means procs far from t are 'safe'")
    print("  - hno_safe forbids safe procs → forbids near-consecutive fires")
    print("  - So hno_safe → phase_len ≥ 2 → mechanism fires")

    # Test 3: Verify the chain: hno_safe → phase_len ≥ 2 for ALL phases
    print("\n\n=== TEST 3: Does hno_safe force phase_len ≥ 2? ===\n")

    # If ALL phases have length 1: cycle = t, q1, t, q2, t, ...
    # Length L = 2F. All non-t movers are q1,...,qF.
    # For hno_safe: every proc's neighborhood visited.
    # The movers visit: {t, q1, q2, ...} and their neighborhoods.
    # t visits {left(t), t, right(t)}.
    # qi visits {left(qi), qi, right(qi)}.
    # For all n procs to be covered: the qi's must cover all remaining neighborhoods.
    # With n ≥ 9 and qi ∈ {lt, rt} (if all qi are neighbors of t):
    #   covered = {llt, lt, t, rt, rrt} = 5 procs. Need 9. Not enough.
    # So SOME qi ∉ {lt, rt}. Then phase_len = 1 for that phase.
    #
    # Wait, that's backwards. phase_len = 1 means exactly 1 non-t step per phase.
    # If qi ∉ {lt, rt}: that phase has a non-neighbor mover. And phase_len = 1.
    # The question is whether ALL phases can have phase_len = 1.
    # Answer: yes, but some qi must be non-neighbors (from hno_safe).
    # The non-neighbor qi creates a phase where the mechanism might or might not fire.
    #
    # For a phase with qi (the single non-t mover): J = (1 if qi == lt else 0),
    # K = (1 if qi == rt else 0). If qi ∉ {lt, rt}: J = K = 0 → BothEven! Mechanism fires!

    print("KEY INSIGHT FOUND!")
    print()
    print("If phase_len = 1 and the single mover qi ∉ {left(t), right(t)}:")
    print("  J = 0, K = 0 → BothEven → mechanism fires!")
    print()
    print("So normal form at phase_len = 1 REQUIRES qi ∈ {left(t), right(t)}.")
    print("That is: the single non-t step must be a NEIGHBOR fire.")
    print()
    print("If ALL phases have phase_len = 1 AND all qi ∈ {lt, rt}:")
    print("  All movers ∈ {t, lt, rt}. Only 3 procs fire.")
    print("  For n ≥ 9: procs at distance ≥ 3 from t are safe.")
    print("  Contradicts hno_safe!")
    print()
    print("So with hno_safe + n ≥ 5:")
    print("  SOME phase has qi ∉ {lt, rt} → J=K=0 → BothEven → mechanism fires!")
    print("  That phase gives EC. We never reach the normal-form branch!")
    print()
    print("WAIT — but exists_ternaryPhase returns an ARBITRARY phase.")
    print("It might return a phase where the mechanism doesn't fire (phase_len=1, qi=neighbor).")
    print("The KEY is: we need to find a SPECIFIC phase where the mechanism fires.")
    print()
    print("The proof structure should be:")
    print("  1. From hno_safe: ∃ step k where moverAt(k) ∉ {t, lt, rt}")
    print("  2. Let s' = the NEXT t-fire after k")
    print("  3. In the phase ending at s': at least one mover is k (non-neighbor)")
    print("  4. intervalFireCount(lt, k, s') and intervalFireCount(rt, k, s') might not be 0")
    print("     (other neighbor fires might occur between k and s')")
    print()
    print("Hmm, that's not quite right. Let me think more carefully.")
    print()

    # The real insight: we need the phase [prev_t_fire+1, s') to contain step k.
    # The phase is the gap between consecutive t-fires. Step k is in SOME gap.
    # In that gap: the mover at step k is a non-neighbor. So the gap contains
    # at least one non-neighbor fire.
    #
    # The J and K for that gap: J counts left fires, K counts right fires.
    # The non-neighbor fire at k contributes to neither J nor K.
    # But there might be OTHER fires in the gap that ARE left or right.
    #
    # If J = 0 and K = 0 in this gap: BothEven! Mechanism fires.
    # If J > 0 or K > 0: need to check mechanism conditions.
    #
    # The non-neighbor fire guarantees phase_len ≥ 1, but doesn't force J=K=0.
    #
    # HOWEVER: if the ONLY fire in the gap is the non-neighbor: J=K=0.
    # If the gap has other fires too: J or K might be > 0.

    print("REFINED INSIGHT:")
    print()
    print("From hno_safe + n ≥ 5: ∃ step k with moverAt(k) ∉ {t, lt, rt}.")
    print("Step k is in some phase (gap between t-fires).")
    print("In that phase: at least 1 non-neighbor fire (step k).")
    print("The phase might ALSO have neighbor fires (J > 0 or K > 0).")
    print()
    print("If J = K = 0 in that phase: BothEven → mechanism → EC → False.")
    print("If J > 0 or K > 0: mechanism might or might not fire.")
    print()
    print("So the question: in the phase containing step k,")
    print("is J = K = 0 guaranteed?")
    print()
    print("Answer: NO. The phase can have neighbor fires too.")
    print()
    print("But: if we pick the RIGHT phase (one with J=K=0), we're done.")
    print("We need: ∃ phase where J=K=0.")
    print()
    print("When does J=K=0 fail for ALL phases?")
    print("Every phase has J ≥ 1 or K ≥ 1. That means every gap between t-fires")
    print("has at least one left or right fire.")
    print()
    print("With F_L total left fires and F_R total right fires:")
    print("If every phase has J ≥ 1: F_L ≥ F (one per phase).")
    print("If every phase has K ≥ 1: F_R ≥ F.")
    print("If every phase has J ≥ 1 OR K ≥ 1: F_L + F_R ≥ F.")
    print()
    print("Can we show ∃ phase with J=K=0?")
    print("Not in general. But maybe with additional constraints...")

    # Test 4: In cycles with a non-neighbor mover, how often is there a J=K=0 phase?
    print("\n\n=== TEST 4: Frequency of J=K=0 phases ===\n")

    has_jk0 = 0
    no_jk0 = 0

    for n, ms in [(5, [2,2,2,3,3]), (7, [2,2,2,3,3,3,3])]:
        for trial in range(200000):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            cycle = find_good_cycle(sys_f, ms, n)
            if cycle is None:
                continue
            movers = [p for _, p in cycle]

            for t in range(n):
                lt, rt = (t-1)%n, (t+1)%n
                if ms[lt] != 2 or ms[rt] != 2:
                    continue
                result = analyze_cycle(cycle, ms, n, t)
                if result is None:
                    continue

                # Check if any phase has J=K=0
                has_zero = any(p['J'] == 0 and p['K'] == 0 for p in result['phases'])
                if has_zero:
                    has_jk0 += 1
                else:
                    no_jk0 += 1

    print(f"Procs with ≥1 J=K=0 phase: {has_jk0}")
    print(f"Procs with NO J=K=0 phase: {no_jk0}")
    print(f"Fraction with J=K=0: {has_jk0/(has_jk0+no_jk0)*100:.1f}%" if has_jk0+no_jk0 > 0 else "N/A")
    print()
    print("If most procs have a J=K=0 phase: we can use it for BothEven EC.")
    print("If some don't: need to handle those cases too.")

if __name__ == '__main__':
    main()
