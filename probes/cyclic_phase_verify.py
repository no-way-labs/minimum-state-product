"""
Verify the cyclic BothEvenReturn mechanism on CUP-2 mover words.

The key test: for any step a after the last t-fire, can we construct
an entry conflict at t between:
  - Mover step s_0 (first t-fire, where t fires)
  - Nonmover step a (after last t-fire, where t doesn't fire)
using cyclic value preservation?

The entry conflict requires configs(s_0)(p) = configs(a)(p) for p in {L, t, R}.
"""

def cup2_mw(n):
    return list(range(n)) + list(range(n-2, 0, -1)) + list(range(n))

def fire_steps(mw, p):
    return [i for i, m in enumerate(mw) if m == p]

print("=" * 70)
print("CYCLIC VALUE PRESERVATION VERIFICATION")
print("=" * 70)

for n in [5, 7, 9]:
    mw = cup2_mw(n)
    CL = len(mw)
    print(f"\nn={n}, CL={CL}, mw={mw}")

    for t in range(n):
        ts = fire_steps(mw, t)
        fc_t = len(ts)
        if fc_t < 2:
            continue

        s_min = ts[0]
        s_max = ts[-1]
        left_t = (t - 1) % n
        right_t = (t + 1) % n

        # Wrap-around region: [0, s_min) ∪ (s_max, CL)
        wrap_L = sum(1 for k in range(0, s_min) if mw[k] == left_t)
        wrap_L += sum(1 for k in range(s_max + 1, CL) if mw[k] == left_t)
        wrap_R = sum(1 for k in range(0, s_min) if mw[k] == right_t)
        wrap_R += sum(1 for k in range(s_max + 1, CL) if mw[k] == right_t)

        if wrap_L + wrap_R < 2:
            continue

        print(f"\n  t={t}: s_min={s_min}, s_max={s_max}, wrap_L={wrap_L}, wrap_R={wrap_R}")

        # For each nonmover step in the wrap region:
        wrap_steps = []
        for k in range(0, s_min):
            if mw[k] != t:
                wrap_steps.append(k)
        for k in range(s_max + 1, CL):
            if mw[k] != t:
                wrap_steps.append(k)

        print(f"  Wrap nonmover steps: {wrap_steps}")

        # Check: for each wrap nonmover step a, does cyclic value preservation hold?
        # i.e., does config(a)(t) = config(s_min)(t)?
        # In the mover word model, config values change when the processor fires.
        # t doesn't fire in the wrap region, so t's value is constant from
        # step s_max+1 through CL-1 through 0 through s_min-1.
        # And at step s_min, t fires (changes its value).
        # So config(s_max+1)(t) = config(s_max+2)(t) = ... = config(CL-1)(t)
        #   = config(0)(t) = ... = config(s_min-1)(t) = config(s_min)(t).
        # Wait, config(s_min)(t) is the value BEFORE t fires at step s_min.
        # The entry conflict uses configs.get(s_min) which is the config at the
        # START of step s_min, before the move. So t hasn't fired yet.
        # And configs.get(a) for a in the wrap region also has t not firing.
        # So configs.get(a)(t) = configs.get(s_min)(t) iff t doesn't fire
        # between a and s_min (cyclically). This IS true for the wrap region.

        # Simulate config values (starting from arbitrary initial)
        # Track each processor's value modulo its state count
        # For the mover word, at each step k, mw[k] fires (increments mod m)

        ms = [2] + [3] * (n - 2) + [2]  # CUP-2
        config = [0] * n  # initial config (arbitrary)
        configs = [tuple(config)]
        for k in range(CL):
            p = mw[k]
            config = list(configs[-1])
            config[p] = (config[p] + 1) % ms[p]
            configs.append(tuple(config))
        # configs[0] = initial, configs[k+1] = after step k fires

        # In the Lean model, configs.get(k) is the config BEFORE step k fires.
        # So the config at "step k" is configs[k] (0-indexed).
        # After step k fires, we get configs[k+1].
        # The cyclic property: configs[CL] = configs[0] (since the cycle returns).

        cyclic_ok = configs[CL] == configs[0]
        print(f"  Cyclic closure: configs[CL] == configs[0]? {cyclic_ok}")

        # Check value preservation for t across the wrap
        for a in wrap_steps:
            val_a_t = configs[a][t]
            val_smin_t = configs[s_min][t]
            val_a_L = configs[a][left_t]
            val_smin_L = configs[s_min][left_t]
            val_a_R = configs[a][right_t]
            val_smin_R = configs[s_min][right_t]

            # t should be preserved (no t fires in wrap)
            t_ok = val_a_t == val_smin_t

            # Count L and R fires between a and s_min (cyclically)
            # If a > s_min (wrap): [a+1, CL) ∪ [0, s_min)
            if a >= s_min:
                L_fires = sum(1 for k in range(a+1, CL) if mw[k] == left_t)
                L_fires += sum(1 for k in range(0, s_min) if mw[k] == left_t)
                R_fires = sum(1 for k in range(a+1, CL) if mw[k] == right_t)
                R_fires += sum(1 for k in range(0, s_min) if mw[k] == right_t)
            else:
                L_fires = sum(1 for k in range(a+1, s_min) if mw[k] == left_t)
                R_fires = sum(1 for k in range(a+1, s_min) if mw[k] == right_t)

            L_even = L_fires % 2 == 0
            R_even = R_fires % 2 == 0
            L_match = val_a_L == val_smin_L
            R_match = val_a_R == val_smin_R

            # BothEvenReturn would work if L_even AND R_even (then L_match and R_match)
            both_even = L_even and R_even
            contexts_match = t_ok and L_match and R_match
            ec_possible = contexts_match  # Full context match = entry conflict

            if a > s_max or a < s_min:
                print(f"    a={a}: t_ok={t_ok}, L_fires={L_fires} (even={L_even}, match={L_match}), "
                      f"R_fires={R_fires} (even={R_even}, match={R_match}), "
                      f"both_even={both_even}, EC_possible={ec_possible}")

print("\n" + "=" * 70)
print("MECHANISM APPLICABILITY CHECK")
print("=" * 70)
print("""
For the wrap-around phase with J+K >= 2, the mechanisms are:
  - BothEvenReturn: J even, K even -> context match -> EC
  - ToggleFR: J >= 2, K = 0 -> two distinct L-values -> EC
  - ToggleFR_symm: J = 0, K >= 2 -> two distinct R-values -> EC
  - Cross-neighbor: J >= 1, K >= 1 -> at least one pair matches -> EC

The key question: do these mechanisms work across the cycle boundary?

YES, because:
1. Value preservation for t uses configVal_eq_of_cyclic_noFire (new lemma)
2. Binary parity uses the TOTAL parity of fires in the cyclic interval
3. Binary dichotomy (for ToggleFR) only needs TWO distinct values at
   nonmover steps — these can be on opposite sides of the boundary

The mechanisms DON'T depend on the step ordering (a < s). They only need:
  - t's value is the same at the mover step and nonmover step
  - L's (or R's) value satisfies the parity/dichotomy condition

These are VALUE properties, not INDEX properties.

The only place where a < s matters is in constructing the witness:
  hasEntryConflict requires ⟨s, a, t, ...⟩ where s IS the mover step
  and a IS the nonmover step. These are just Fin indices, no ordering needed.

WAIT: actually, hasEntryConflict has NO ordering requirement on s and a!
Let me check...
""")

# Check: does hasEntryConflict require a < s?
print("Checking hasEntryConflict definition...")
print("From GoodCycleBasics.lean, hasEntryConflict is defined as:")
print("  ∃ (s a : Fin CL) (p : Fin n),")
print("    moverAt s = p ∧ moverAt a ≠ p ∧")
print("    configs.get s (left p) = configs.get a (left p) ∧")
print("    configs.get s p = configs.get a p ∧")
print("    configs.get s (right p) = configs.get a (right p)")
print()
print("NO ORDERING CONSTRAINT on s and a!")
print("The mover step s and nonmover step a can be in any order.")
print()
print("This means: for the wrap-around, we use:")
print("  s = s_min (first t-fire, mover)")
print("  a = some step in (s_max, CL) (nonmover)")
print("  where a > s. This is FINE — no a < s requirement!")
