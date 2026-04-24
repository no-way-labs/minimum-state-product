"""
Analyze the counterexamples: what structural feature enables non-adj H-1?
"""

# Counterexample 1:
# step 0: (0, 0, 1) mover=1
# step 1: (0, 2, 1) mover=2
# step 2: (0, 2, 0) mover=0
# step 3: (1, 2, 0) mover=2
# step 4: (1, 2, 2) mover=2
# step 5: (1, 2, 1) mover=1
# step 6: (1, 1, 1) mover=0
# step 7: (0, 1, 1) mover=1
# Non-adj H-1: j=1,k=5,p=0,d=4
# Non-adj H-1: j=1,k=7,p=1,d=6
# Non-adj H-1: j=3,k=5,p=2,d=2

# At j=3,k=5,p=2,d=2:
# g_3 = (1,2,0), g_5 = (1,2,1). Differ at proc 2.
# Arc steps 3,4: movers = 2,2.
# So proc 2 fires twice (a_2 = 2 out of m_2 = 3).
# Proc 2 goes: 0 → 2 → 1 in 2 steps. NOT returning to start.
# This is correct: p=2 doesn't need to return (it's the defect).
# Procs 0,1: a_0=0, a_1=0. Both return. ✓

# The key: d=2 with a ternary proc firing twice consecutively.
# m_p = 3, a_p = 2. d = 2 = a_p + 0 (no other procs fire).

# When does a ternary proc fire twice consecutively?
# At step 3: mover=2. Config changes at proc 2.
# At step 4: mover=2 again. Proc 2 fires again.
# After step 3: g_4 = (1,2,2). Proc 2's value changed from 0 to 2.
# At step 4: proc 2's context is (2, 2, ?). Wait, let me compute.

# g_3 = (1, 2, 0). Mover = 2. Context of proc 2: L=g_3[1]=2, S=g_3[2]=0, R=g_3[0]=1.
# f_2(2, 0, 1) = 2 (fires: 2 != 0). → g_4[2] = 2.
# g_4 = (1, 2, 2). Mover = 2. Context of proc 2: L=g_4[1]=2, S=g_4[2]=2, R=g_4[0]=1.
# f_2(2, 2, 1) = 1 (fires: 1 != 2). → g_5[2] = 1.
# g_5 = (1, 2, 1).

# So proc 2: value goes 0 → 2 → 1 in 2 fires. a_p = 2.
# Value Coverage: in the full cycle, proc 2 fires 3 times, visiting all 3 values.

# The d=2 non-adjacent H-1 pair arises because a TERNARY proc fires
# twice CONSECUTIVELY, advancing 2 steps along its value cycle.
# During these 2 steps, no other proc fires, so all other procs return
# trivially (they didn't fire at all).

# This is a generic phenomenon: whenever a ternary proc fires 2 times
# in a row, the configs at positions (step_before, step_before+2) are
# Hamming-1 at that proc.

# The question for the LB proof: does this matter?
# The LB proof uses H-1 Uniqueness for sweep non-consecutive binary.
# In SWEEP cycles (where the mover goes around the ring), does a
# ternary proc ever fire twice consecutively?

# In a pure sweep: mover sequence is 0,1,2,...,n-1,0,1,... (or reverse).
# No proc fires twice consecutively. So d=2 doesn't arise.

# But the mover word doesn't have to be a pure sweep to have high displacement.
# A "sweep with stutters" could have a ternary proc firing twice.

# Let me check: in the actual LB proof, is the sweep case restricted
# to pure sweeps?

print("ANALYSIS OF COUNTEREXAMPLES")
print()
print("All counterexamples have d=2 with a ternary proc firing 2x consecutively.")
print("This is the ONLY mechanism for non-adjacent H-1 with d=2 when gcd=1.")
print()
print("For the d=2 mechanism to work:")
print("  - Position p must be ternary (m_p = 3)")
print("  - p fires at both steps j and j+1 (consecutive)")
print("  - No other proc fires in these 2 steps")
print("  - p's value changes v → v' → v'', with v'' ≠ v")
print()
print("In SWEEP cycles (|displacement| ≥ 2n):")
print("  The mover advances through all n procs multiple times.")
print("  If n ≥ 5: between consecutive fires of the same proc,")
print("  at least n-1 ≥ 4 other procs fire. So NO consecutive same-proc fires.")
print()
print("For n = 3: a sweep has CL = 8, displacement ≥ 6.")
print("  Mover word with displacement 6: e.g., (0,1,2,0,1,2,0,1).")
print("  But wait, fc = (2,3,3) requires proc 0 to fire 2x, procs 1,2 to fire 3x each.")
print("  CL = 8. Displacement = CW - CCW. Max displacement = 8 (all CW).")
print("  For displacement ≥ 6: CW - CCW ≥ 6 with CW + CCW ≤ 8.")
print("  CW ≥ 7 → at most 1 CCW or stay step.")
print()

# Check: do any sweep words at n=3 have consecutive same-proc fires?
import itertools

ms = [2, 3, 3]
n = 3
CL = 8

def enumerate_mover_words(ms):
    base = []
    for i in range(len(ms)):
        base.extend([i]*ms[i])
    return set(itertools.permutations(base))

words = list(enumerate_mover_words(ms))

sweep_words = []
for word in words:
    cw = sum(1 for s in range(CL) if word[s] == (word[(s-1)%CL] + 1) % n)
    ccw = sum(1 for s in range(CL) if word[s] == (word[(s-1)%CL] - 1) % n)
    if abs(cw - ccw) >= 2 * n:
        sweep_words.append(word)

print(f"Sweep words at n=3: {len(sweep_words)}")

for word in sweep_words[:10]:
    # Check for consecutive same-proc fires
    consec = []
    for s in range(CL):
        if word[s] == word[(s+1) % CL]:
            consec.append(s)
    if consec:
        print(f"  {word}: consecutive fires at steps {consec}")
    else:
        print(f"  {word}: no consecutive same-proc fires")

# Now check for n >= 5
print()
for n_test in [5, 7, 9]:
    ms_test = [2, 3, 3, 3, 3] + [3] * (n_test - 5)
    ms_test = ms_test[:n_test]
    CL_test = sum(ms_test)
    print(f"\nn={n_test}, ms={ms_test}, CL={CL_test}")

    # In a sweep at n >= 5: consecutive same-proc fires are impossible
    # because the mover must traverse at least n-1 other procs between
    # consecutive fires of the same proc.
    #
    # In a sweep with displacement >= 2n: there are at most
    # (CL - 2n) non-forward steps. For n >= 5 with CL = 2 + 3(n-1):
    # CL = 3n - 1. Displacement >= 2n. CW >= (CL + 2n) / 2 = (3n-1+2n)/2 = (5n-1)/2.
    # CCW <= CL - CW <= (3n-1) - (5n-1)/2 = (n-1)/2.
    # So at most (n-1)/2 ≈ 2 non-forward steps.
    #
    # For same-proc consecutive: both steps fire the same proc p.
    # The proc before p fires at step s, then p fires at s and s+1.
    # The "displacement" from step s to s+1 is 0 (stay), not +1 (CW).
    # So each consecutive pair costs 1 CW step → up to (n-1)/2 ≈ 2 possible.
    #
    # But with n ≥ 5 and CW ≥ (5*5-1)/2 = 12 for n=5:
    # CL = 14, CW >= 12, CCW <= 2. At most 2 non-CW transitions.
    # A consecutive same-proc fire is a non-CW transition (stay or backwards).
    # With at most 2: we could have up to 2 consecutive same-proc fires.
    # So the issue ISN'T eliminated by sweep structure alone!

    print(f"  CL = {CL_test}")
    print(f"  Sweep threshold: 2n = {2*n_test}")
    print(f"  In a sweep: CW >= {(CL_test + 2*n_test + 1)//2}, CCW <= {(CL_test - 2*n_test)//2}")
    print(f"  Max non-CW steps: {(CL_test - 2*n_test)//2}")
    print(f"  Could have consecutive same-proc fires: possible if non-CW > 0")

# ============================================================
# CONCLUSION
# ============================================================
print("\n" + "=" * 70)
print("CONCLUSIONS")
print("=" * 70)
print("""
1. The H-1 Uniqueness Lemma as stated is FALSE.
   Counterexample: n=3, ms=(2,3,3), gcd=1, valid self-stabilizing system
   with non-adjacent H-1 pairs at d=2.

2. The d=2 mechanism: a ternary proc fires twice consecutively.
   This creates H-1 pairs spaced 2 apart. No amount of GCD argument prevents it.

3. For PURE SWEEPS (mover goes strictly around the ring): consecutive
   same-proc fires don't occur, so d=2 non-adj H-1 is impossible.
   But the LB proof's sweep case includes "wiggle" cycles with stutters.

4. The lb_complete_proof.md's divergence argument (line 210) is wrong:
   movers can disagree while H-1 is preserved via defect propagation.

5. The correct statement should be: "In a good cycle where no proc fires
   consecutively (which holds for pure sweeps), H-1 implies adjacency."
   Or: the ShadowTrap construction should be modified to handle the
   consecutive-fire case separately.

6. For the LB Lean formalization: the sorry tokens for "H-1 sub-lemmas"
   correspond to a genuine proof gap. The fix is either:
   (A) Add "no consecutive same-proc fires" as a hypothesis, or
   (B) Handle the consecutive-fire case directly in the shadow construction.

IMPACT ON THE MAIN THEOREM:
   The LB proof uses H-1 Uniqueness only in Case D2 (sweep non-consecutive binary).
   In sweep cycles with displacement >= 2n: consecutive same-proc fires CAN occur
   (up to ~n/2 of them). So the gap IS relevant.

   However: the shadow trap construction may work even WITH non-adjacent H-1 pairs,
   because the shadow orbit still closes and stays non-good — the H-1 Uniqueness
   was being used to show "shifted config is non-good", but there might be an
   alternative argument for this.
""")
