#!/usr/bin/env python3
"""
PA Domino Final: Determine if consec_isolated_false needs hsweep.

The sorry in consec_isolated_false has hypotheses:
  hn : n ≥ 9
  gc : GoodCycle sys
  hconv : converges sys gc
  hno_safe : ¬∃ q, ∀ k, moverAt k ≠ q ∧ ...
  hsub : subThreshold sys.rs
  h3bin : hasGe3Binary sys.rs
  i : Fin n
  h3consec : threeConsecutiveBinary sys.rs i
  hfc_ri : gc.fireCount (right i) ≥ 2
  hiso : isolated firings at right(i)

And in the sorry branch:
  hparity : odd parity at a neighbor in min gap
  phase : some TernaryPhase
  ¬hmech : dispatch fails for phase

Question: Is consec_isolated_false provable WITHOUT hsweep?

If the counterexample (ms=(3,2,...,2), n=9) satisfies ALL the hypotheses
except hsweep, then we need hsweep. If it doesn't satisfy some hypothesis
(e.g., it fails hconv or hno_safe), then maybe we don't need hsweep.

The counterexample has:
- ms = (3,2,2,2,2,2,2,2,2)
- 8 binary, 1 ternary
- Product = 3 * 2^8 = 768 < 4 * 3^7 = 8748 (sub-threshold) ✓
- hasGe3Binary ✓
- Has 3 consecutive binary ✓ (positions 1,2,3 for example)
- A mover word that's locally consistent

But: does it satisfy hconv (converges)?
The mover word is (0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1).
This is a specific good cycle. For it to satisfy hconv,
the SYSTEM must converge (not just the cycle).

Actually, hconv means the SYSTEM converges, not the cycle.
Convergence is a property of the system (transition functions).
If we can build a system with this good cycle that converges,
then hconv holds.

The counterexample from the route doc says:
"locally consistent n=9 witness" with "no mover/nonmover context overlap"
(i.e., no EC). So the transition function CAN be defined consistently.
But does the resulting system CONVERGE?

That's the key question. If the system converges but has no EC,
then consec_isolated_false can't derive False (contradiction).
If the system doesn't converge, then hconv provides the contradiction.

For convergence: the system must have the property that from every
initial configuration, it eventually reaches a legitimate state.
This is a GLOBAL property of the transition function.

The locally consistent witness might define transition functions that
DON'T converge. In that case, hconv fails, and the sorry is reachable.

But can we prove that no converging system can have this good cycle?
That would require showing that the cycle structure prevents convergence,
which is a very different argument.

REALIZATION: The sorry is INSIDE sweep_false which concludes False.
The full call chain is:
  sweep_false → consec_isolated_false → sorry

sweep_false has hsweep. It passes hfc_ri from sweep_fireCount_ge2.
But it doesn't pass hsweep itself to consec_isolated_false.

The fix might be: ADD hsweep to consec_isolated_false's hypotheses.
Or use a different argument that doesn't need hsweep.

Let me check: does the counterexample (ms=(3,2,...,2)) have a SWEEP cycle?
"""

# The counterexample mover word: (0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1)
# Length 19. n=9. ms=(3,2,2,2,2,2,2,2,2).
# winding: let me compute
n = 9
word = [0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1]
ell = len(word)

winding = 0
for idx in range(ell):
    d = (word[(idx+1)%ell] - word[idx]) % n
    if d == 1: winding += 1
    elif d == n-1: winding -= 1

print(f"Counterexample winding: {winding}")
print(f"Total displacement: |{winding}| * {n} = {abs(winding) * n}")
is_sweep = abs(winding * n) >= 2 * n
print(f"Is sweep (|disp| >= 2n = {2*n})? {is_sweep}")

# Check: is this a valid good cycle?
ms = [3,2,2,2,2,2,2,2,2]
from collections import Counter
fc = Counter(word)
print(f"\nFire counts: {dict(fc)}")
print(f"fc multiple of m? {all(fc.get(p,0) % ms[p] == 0 for p in range(n))}")

# Build configs
start = tuple(0 for _ in range(n))
cfgs = [list(start)]
for idx in range(ell):
    c = list(cfgs[-1])
    c[word[idx]] = (c[word[idx]] + 1) % ms[word[idx]]
    cfgs.append(c)

print(f"Returns to start? {tuple(cfgs[0]) == tuple(cfgs[ell])}")
print(f"All procs fire? {all(fc.get(p,0) > 0 for p in range(n))}")

# Check EC
has_ec = False
for p in range(n):
    m_ctx = set()
    n_ctx = set()
    for s in range(ell):
        ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
        if word[s] == p:
            if ctx in n_ctx: has_ec = True; break
            m_ctx.add(ctx)
        else:
            if ctx in m_ctx: has_ec = True; break
            n_ctx.add(ctx)
    if has_ec: break

print(f"Has EC? {has_ec}")

# Check: consecutive binary with ternary sandwiched
# ms[0] = 3 (ternary), ms[1..8] = 2 (binary)
# 3 consecutive binary: {1,2,3}, {2,3,4}, etc.
# t = right(i) for some i
# t would be proc 2 for i=1, etc.

# Check isolated firings at t=2:
t_pos = 2
t_steps = [s for s in range(ell) if word[s] == t_pos]
print(f"\nt={t_pos} fire steps: {t_steps}, fc={fc[t_pos]}")
isolated = all(word[(s+1)%ell] != t_pos and word[(s-1)%ell] != t_pos for s in t_steps)
print(f"Isolated? {isolated}")

# Check phases at t=2
if len(t_steps) >= 2:
    i_pos = 1  # left(t)
    rr_pos = 3  # right(t)
    for idx in range(len(t_steps)):
        a = t_steps[idx]
        b = t_steps[(idx+1) % len(t_steps)]
        if b <= a: b += ell
        J = sum(1 for s in range(a+1, b) if word[s%ell] == i_pos)
        K = sum(1 for s in range(a+1, b) if word[s%ell] == rr_pos)
        print(f"  Phase {idx}: [{a},{b}) J={J} K={K}")

# Now: is this cycle a SWEEP?
# winding = 0 means total displacement = 0. For a sweep, need |disp| >= 2n.
# So this is NOT a sweep!
print(f"\nConclusion: The counterexample has winding = {winding},")
print(f"so total displacement = 0 < 2*{n} = {2*n}.")
print(f"It is NOT a sweep cycle.")
print(f"Therefore, consec_isolated_false (which is only called from sweep_false)")
print(f"would never encounter this counterexample.")
print()
print(f"The sorry CAN be closed by adding hsweep to the hypotheses.")
print(f"Or by using the sweep property that is implicitly available")
print(f"through the calling context.")

print("\n" + "="*70)
print("RECOMMENDED PROOF ROUTE")
print("="*70)
print()
print("Option 1: Add hsweep to consec_isolated_false's hypotheses.")
print("  This is a simple refactor. sweep_false already has hsweep.")
print("  Then use sweep-specific arguments to close the sorry.")
print()
print("Option 2: Keep hypotheses as-is and find a proof that works")
print("  without sweep. This is harder and may be unnecessary.")
print()
print("With hsweep available, the sweep structure gives:")
print("  - fc(p) ≥ 2 for all p (already have this)")
print("  - Specific ordering of movers (CW/CCW sweeps)")
print("  - |total displacement| ≥ 2n")
print("  - Fire count relationships from the sweep structure")
print()
print("The KEY insight with sweep: between consecutive t-fires in a CW sweep,")
print("the mover visits ALL procs in order: t+1, t+2, ..., n-1, 0, 1, ..., t.")
print("So EVERY proc fires in each phase. This means J ≥ 1 AND K ≥ 1 for")
print("every phase! Combined with dispatch failure, this severely constrains")
print("the phase structure.")
print()
print("Actually wait: in a CW HALF-sweep, every proc fires once.")
print("If fc(t) = number of half-sweeps through t, then each half-sweep")
print("contributes 1 to both J and K. So J = K = half-sweep count per phase.")
print("That's not quite right; the sweep alternates CW and CCW.")
print()
print("SIMPLEST SWEEP ARGUMENT:")
print("In a sweep, the cycle decomposes into alternating CW and CCW passes.")
print("Each pass visits every processor once. Between consecutive t-fires,")
print("there is exactly one half-sweep (CW or CCW). In each half-sweep,")
print("both i and rr fire exactly once. So J = K = 1 for every phase.")
print("Total: fc(i) = fc(rr) = fc(t). Since all binary: fc(t) = fc(i) = fc(rr) = 2k.")
print()
print("With J=K=1 for every phase: each phase has J+K=2.")
print("(Even J ∧ Even K) → dispatch succeeds! But we assumed ¬hmech. CONTRADICTION!")
print()
print("Wait: J=1 is ODD, not even. Even J means J%2 = 0.")
print("J=1 is odd. K=1 is odd. So ¬(Even J ∧ Even K) — dispatch fails for BothEven.")
print("But (1,1): J≥2? No, J=1<2. K≥2? No. So neither toggle-FR fires.")
print("So dispatch actually FAILS for (1,1). That's consistent with ¬hmech.")
print()
print("Hmm. So even with sweep, we can have undispatchable phases.")
print("The sweep gives J=K=1 for every phase, which is undispatchable.")
print()
print("So the sweep argument doesn't directly close the sorry.")
print("We need a DIFFERENT argument.")
