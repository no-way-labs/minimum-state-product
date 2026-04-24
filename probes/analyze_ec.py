#!/usr/bin/env python3
"""Analyze adjacent-step EC for the left residue structure."""

n = 9
t = 4
lt, rt = (t-1)%n, (t+1)%n

# Concrete mover word with residue structure
mw = [0, 7, 8, 7, 8, 0, 1, 4, 5, 6, 4, 5, 6, 2, 1, 2, 3, 2, 3, 2]
L = len(mw)

print(f"Mover word: {mw}")
print(f"Length: {L}")

fc = [0]*n
for p in mw: fc[p] += 1
print(f"Fire counts: {fc}")
print(f"All fire >= 2: {all(f >= 2 for f in fc)}")

# t fires at:
t_steps = [i for i,p in enumerate(mw) if p == t]
print(f"t={t} fires at: {t_steps}")

# Check adjacent-step EC
for s in t_steps:
    prev = (s - 1) % L
    pm = mw[prev]
    works = pm not in {lt, t, rt}
    print(f"  Step {s}: prev mover={pm}, EC={'YES' if works else 'no'}")

# Check phases
for idx in range(len(t_steps)):
    s1 = t_steps[idx]
    s2 = t_steps[(idx+1) % len(t_steps)]
    phase = []
    k = (s1 + 1) % L
    while k != s2:
        phase.append(k)
        k = (k + 1) % L
    J = sum(1 for k in phase if mw[k] == lt)
    K = sum(1 for k in phase if mw[k] == rt)
    norm = not (J%2==0 and K%2==0) and not (J>=2 and K==0) and not (J==0 and K>=2)
    print(f"  Phase {idx}: [{s1}->{s2}] J={J} K={K} normal={norm}")

print()
print("=== KEY FINDING ===")
print("Adjacent-step EC at t works when step j+1 (mover=lllt=1) is")
print("immediately followed by t firing. The residue structure guarantees")
print("moverAt(j+1) = lllt. If moverAt(j+2) = t: EC!")
print()
print("The question: does the phase structure prevent t from firing at j+2?")
print("Answer: NO. The 6-set allows t to fire anywhere in [j+2, k_out-1].")
print("The normal form constraint doesn't restrict WHEN t fires, only the")
print("fire counts J,K in each phase interval.")
print()
print("BUT: the proof needs to handle the case where t does NOT fire at j+2.")
print("In that case: step j+2 has some mover q in 6-set with q != t.")
print("If q not in {lt, rt} = {3, 5}: adjacent EC at t when t eventually fires?")
print("No — the EC is between consecutive steps, not between j+1 and the t-fire.")
print()
print("Correct adjacent-step EC: at t-fire step s, check mw[s-1].")
print("If mw[s-1] not in {lt, t, rt}: EC at t between s and s-1.")
print("This works regardless of what happens at j+1.")
print()
print("So: if ANY t-fire step has prev mover not in {3,4,5}: EC.")
print("The only failure case: ALL t-fire steps have prev mover in {3,5}.")
print("(prev mover = 4 = t is impossible since t can't fire twice in a row)")
print()
print("With the left residue structure: step j+1 has mover 1.")
print("If t fires at j+2: prev = step j+1 = mover 1, not in {3,5}. EC!")
print("What if t fires later?")
print("The FIRST t-firing after j is in the first phase after step j+1.")
print("This phase starts from a previous t-firing (or wraps from the last one).")
print("The last mover before the t-firing in each phase is the 'tail' of the phase.")
print()
print("In normal form with J>=1 or K>=1: at least one of {lt, rt} fires per phase.")
print("If both J>=1 and K>=1: both fire. The LAST one before t could be either.")
print("If J>=1, K=0 (impossible: normal form says not (J>=2,K=0) and not (J=0,K>=2)).")
print("Actually: normal form allows (1,0). So J=1,K=0 is normal form!")
print("In this case: lt fires once, rt doesn't. lt=3 is the only neighbor firing.")
print("The step before t fires could be lt=3 (in {3,5}). Adjacent EC fails.")
print()
print("Similarly (0,1): rt=5 fires once. Step before t = 5. Fails.")
print("And (1,1): one of lt=3 or rt=5 fires last. Step before t could be 3 or 5. Fails.")
print()
print("BUT: there could be OTHER movers between the last neighbor firing and t's firing!")
print("In a phase: movers include {1,2,6} (from 6-set minus {3,4,5}).")
print("If proc 2 fires AFTER the last lt/rt firing and BEFORE t: step before t = 2.")
print("2 not in {3,5}. ADJACENT EC!")
print()
print("So: adjacent EC at t fails only if the last mover before t in each phase")
print("is ALWAYS lt=3 or rt=5 (no other processor fires between last neighbor and t).")
print("This means: in each phase, movers {1,2,6} all fire BEFORE both lt and rt.")
print("I.e., the phase order is: ..., {1,2,6} movers, ..., lt/rt, t.")
print("This is a very specific ordering constraint.")
print()
print("With the residue structure where step j+1 = mover 1:")
print("The phase containing step j+1 has mover 1 at step j+1.")
print("If 1 fires AFTER lt and rt in this phase: then the step before t")
print("would be 1 (not in {3,5}). EC!")
print("If 1 fires BEFORE lt and rt: then the step before t is lt or rt. No EC.")
print()
print("KEY: proc 1 = lllt fires at step j+1 (from residue). This is the START")
print("of the middle section. The phase containing step j+1 starts from the")
print("PREVIOUS t-firing (which is in the prefix [0, j-1] or wrapping around).")
print("Step j+1 = mover 1 is in the middle of this phase.")
print("After step j+1: other movers in 6-set fire, then eventually t fires.")
print("If lt=3 fires between j+1 and t's first firing: the step before t's")
print("first firing is lt=3 (if it's the last mover before t). Adjacent EC fails.")
print("But if lt=3 fires BEFORE step j+1 (in the prefix): then after j+1,")
print("lt hasn't fired again. The step before t could be mover 1 or 2 or 6.")
print("If 2 or 6: adjacent EC!")
print()
print("CONCLUSION: The adjacent-step EC approach works in MOST cases.")
print("The only hard case: every t-firing is preceded by lt or rt,")
print("with no other movers between the last neighbor and t.")
print("The residue structure's refinements (30 steps!) were designed to")
print("eliminate this possibility. The sorry is the final step where")
print("the proof author needed to show this can't happen.")
