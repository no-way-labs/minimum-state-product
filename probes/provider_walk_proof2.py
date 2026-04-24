"""
Debug the provider check. Examine a specific counter-example:
word=[0, 4, 3, 2, 1, 0, 0, 1, 2, 3, 4], fc=[3, 2, 2, 2, 2], n=5, ms=[2,3,2,3,2]

The mover word is: 0 4 3 2 1 0 0 1 2 3 4
This is: go CCW (0->4->3->2->1->0), stay at 0, then go CW (0->1->2->3->4).
Back to start (4->0 CW). fc(0)=3, rest=2.

TernaryPhases: for each proc t, we need a pair (a, s) where:
- s: t fires at step s
- a < s: t is nonmover at step a
- t doesn't fire in (a, s)

Let me manually trace this.
"""
import sys
sys.path.insert(0, './claude')

n = 5
ms = [2, 3, 2, 3, 2]

# word=[0, 4, 3, 2, 1, 0, 0, 1, 2, 3, 4]
word = [0, 4, 3, 2, 1, 0, 0, 1, 2, 3, 4]
L = len(word)

print(f"Word: {word}")
print(f"L={L}, n={n}, ms={ms}")
print(f"Binary procs: {[i for i in range(n) if ms[i] == 2]}")

# Print step-by-step
print("\nStep-by-step:")
for i in range(L):
    left_m = (word[i] - 1) % n
    right_m = (word[i] + 1) % n
    print(f"  Step {i}: mover={word[i]}, left_neighbor={left_m}, right_neighbor={right_m}")

# Fire counts
fc = [0] * n
for m in word:
    fc[m] += 1
print(f"\nFire counts: {fc}")

# Fire steps for each proc
fire_steps = {p: [] for p in range(n)}
for i, m in enumerate(word):
    fire_steps[m].append(i)
print(f"Fire steps: {fire_steps}")

# Now find ALL valid TernaryPhases
print("\n=== All TernaryPhases ===")
phases = []
for t in range(n):
    fsteps = fire_steps[t]
    if not fsteps:
        continue

    for s in fsteps:
        # Find the latest non-mover step a < s such that t doesn't fire in (a, s)
        # Actually, a can be ANY step < s where t is nonmover and t doesn't fire in (a,s)
        # Let's find ALL valid a values
        for a in range(s):
            if word[a] == t:
                continue  # a must be nonmover for t

            # Check t doesn't fire in (a, s) exclusive
            no_fire = all(word[k] != t for k in range(a + 1, s))
            if not no_fire:
                continue

            # Valid phase!
            left_t = (t - 1) % n
            right_t = (t + 1) % n

            # Count neighbor fires in [a, s)
            left_fires = sum(1 for k in range(a, s) if word[k] == left_t)
            right_fires = sum(1 for k in range(a, s) if word[k] == right_t)

            is_provider = False
            reason = ""

            # Check provider conditions
            if left_fires == 0 and ms[right_t] == 2 and right_fires >= 2 and right_fires % 2 == 0:
                is_provider = True
                reason = f"left_silent, right(={right_t}) binary fires={right_fires}"
            if right_fires == 0 and ms[left_t] == 2 and left_fires >= 2 and left_fires % 2 == 0:
                is_provider = True
                reason = f"right_silent, left(={left_t}) binary fires={left_fires}"

            phases.append((t, a, s, left_fires, right_fires, is_provider, reason))

            if is_provider:
                print(f"  PROVIDER: t={t}, a={a}, s={s}, "
                      f"left({left_t}) fires={left_fires}, right({right_t}) fires={right_fires} | {reason}")

print(f"\nTotal phases found: {len(phases)}")
print(f"Provider phases: {sum(1 for p in phases if p[5])}")

# Let's look at what phases exist more carefully
print("\n=== Phase analysis for each proc ===")
for t in range(n):
    left_t = (t - 1) % n
    right_t = (t + 1) % n
    t_phases = [(a, s, lf, rf, prov, r) for (tt, a, s, lf, rf, prov, r) in phases if tt == t]
    if t_phases:
        print(f"\nProc {t} (m={ms[t]}), left={left_t}(m={ms[left_t]}), right={right_t}(m={ms[right_t]}):")
        for a, s, lf, rf, prov, r in t_phases:
            pstr = " *** PROVIDER" if prov else ""
            print(f"  a={a}, s={s}: left_fires={lf}, right_fires={rf}{pstr}")

# NOW: let's think about what the provider SHOULD be
print("\n=== Manual analysis ===")
print("Word: 0 4 3 2 1 0 0 1 2 3 4")
print("       CW:            ^----->")
print("       CCW: <-------^")
print()
print("Reversals: at step 5 (mover 0, was going CCW, then goes CW)")
print("Actually steps 4->5: 1->0 (CCW), steps 5->6: 0->0 (STAY)")
print("Steps 6->7: 0->1 (CW)")
print()
print("The walk: 0 ->4(CCW) ->3 ->2 ->1 ->0 ->0(stay) ->1(CW) ->2 ->3 ->4")
print("Then wraps: 4->0 (CW)")
print()
print("Between proc 0's firings at steps 0 and 5:")
print("  Excursion: 4, 3, 2, 1 (goes CCW through all other procs)")
print("  This excursion visits ALL procs on the ring!")
print()
print("Between proc 0's firings at steps 5 and 6:")
print("  Excursion: empty (stay step)")
print()
print("Between proc 0's firings at steps 6 and L (wrapping to 0):")
print("  Excursion: 1, 2, 3, 4 (goes CW through all procs)")
print()
print("ISSUE: The excursions from proc 0 visit ALL procs, so they're not one-sided!")
print("But proc 0 is the one with fc=3. Let's look at binary procs (0, 2, 4).")
print()

# Look at binary proc excursions specifically
for b in [0, 2, 4]:
    print(f"\n--- Binary proc {b} (fc={fc[b]}) ---")
    fsteps = fire_steps[b]
    print(f"  Fire steps: {fsteps}")

    for idx in range(len(fsteps)):
        s1 = fsteps[idx]
        s2 = fsteps[(idx + 1) % len(fsteps)]

        if s2 <= s1:
            s2_adj = s2 + L
        else:
            s2_adj = s2

        exc = [word[k % L] for k in range(s1 + 1, s2_adj)]
        print(f"  Excursion [{s1} -> {s2}]: {exc}")

        # Check one-sided
        exc_set = set(exc)
        left_of_b = set()
        right_of_b = set()
        for d in range(1, n):
            right_of_b.add((b + d) % n)
            left_of_b.add((b - d) % n)

        if exc_set <= left_of_b:
            print(f"    ONE-SIDED (left): {exc_set} ⊆ {left_of_b}")
        elif exc_set <= right_of_b:
            print(f"    ONE-SIDED (right): {exc_set} ⊆ {right_of_b}")
        else:
            print(f"    BOTH-SIDED: visits {exc_set}")
