"""
Verify generalized provider at n=6 and analyze the structure.

The generalized provider:
  t fires at s, is nonmover at a, doesn't fire in (a,s).
  One neighbor fires 0 in [a,s) (silent side).
  Other neighbor fires k*m_p times for k >= 1 in [a,s) (return side).

For binary: k*2 >= 2 (even >= 2).
For ternary: k*3 >= 3 (multiple of 3).

Claim: the generalized provider ALWAYS exists.

PROOF STRATEGY: Use the excursion decomposition.

In a ZW walk, each binary proc b partitions its fire steps into excursions.
Each excursion from b goes to one side. The KEY: if a binary b has an excursion
that stays on one side AND the excursion visits the adjacent ternary arc
completely (hitting the neighbor on b's excursion side enough times), then:

t = neighbor on the NON-excursion side of b
phase = (start of excursion, firing step of t after excursion returns)

This gives: b fires (active binary with even count), t as center, silent = other side.

But the CEs show: sometimes the active side is TERNARY, not binary!
The walk oscillates back and forth at a ternary proc, and the ternary proc's
fc in the phase is 3 = multiple of m=3.

Actually, let me think about this differently. The CEs show:
  word=[1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2]
The walk oscillates: 1-0-1-0-1 (back and forth between 0 and 1),
then sweeps CW 1-2-3-4, then oscillates 4-3-4-3, then CCW 3-2.

The generalized provider at t=2, a=0, s=5:
  - left(2)=1 (ternary, m=3) fires 3 times in [0,5)
  - right(2)=3 fires 0 times in [0,5)
  - t=2 fires at step 5, nonmover at step 0

So the walk oscillates at proc 1 three times (fire count 3 = multiple of 3),
proc 3 is silent, and proc 2 fires once after all this.

The ternary proc 1 fires 3 times in the phase, returning to its original value.
This is the GENERALIZED analog of binary_config_eq_of_even_intervalFireCount.

KEY THEOREM NEEDED:
  If proc p fires exactly k*m_p times (k >= 1) in an interval and its
  value cycles through all states, then its value returns to original.

This is TRUE for binary (m=2, even fires). But for ternary (m=3):
  The proc fires 3 times. If each firing increments by 1 mod 3, then
  0 -> 1 -> 2 -> 0 (returns). But the transition function could be
  NON-incrementing! The transition depends on (L, S, R).

Wait. In a GOOD CYCLE, the transition function determines the value change.
Binary: after even fires, value returns (regardless of transition, since
binary value toggles each fire: 0->1->0 or 1->0->1).

But ternary: after 3 fires, value returns ONLY IF the transition is a
cyclic permutation 0->1->2->0 or 0->2->1->0. If the transition is
0->1, 1->0, 2->2 (not cyclic), then 3 fires of 0: 0->1->0->1, NOT returned!

So the generalized provider for ternary is WRONG in general!

Unless... the walk structure forces a specific pattern. Let me check.

Actually, the question is about GOOD CYCLES, where configs are distinct.
In the phase [a, s), proc t doesn't fire, so t's value is constant.
The neighbor p fires k times. Each time p fires, its (L, S, R) context is
different because configs are distinct. So the transition applied could
vary each time.

Hmm. Let me check: in the CE, does the ternary proc's value actually return?

Actually wait. For the PROVIDER to produce an entry conflict, we need:
  config(a)[left(t)] = config(s)[left(t)]
  config(a)[t] = config(s)[t]           (t doesn't fire, automatic)
  config(a)[right(t)] = config(s)[right(t)]

For the SILENT side, the neighbor doesn't fire, so its value IS preserved.
For the ACTIVE side, we need its value to return. For binary, even fires
guarantees return (binary_config_eq_of_even_intervalFireCount). For ternary,
we'd need a ternary_config_eq theorem, which requires the ternary proc's
transition to be cyclic over the phase.

Actually, the proof doesn't DIRECTLY need the value to return. The provider
is an INTERMEDIATE step. The actual entry conflict construction uses
bothEvenReturn_ec or toggleFR_ec, which directly check value equality.

So the question is really: does the generalized provider actually lead to
an entry conflict in ALL cases?

Let me check: in the CE, does the ternary neighbor's value actually return
to its original value at the end of the phase?

We can't check that from just the walk (we need the actual configs). But
in a good cycle, configs ARE distinct, and the walk determines the movers.
The configs depend on the transition function.

IMPORTANT REALIZATION: We're looking at ABSTRACT walks (mover words), not
actual good cycles. An abstract walk might not correspond to any valid
system. So the fact that the generalized provider exists for all abstract
walks doesn't mean it works for all actual good cycles.

But wait — the theorem we're proving is about good cycles, not abstract walks.
And the existing proof structure (CaseObstructionsCore.lean) already works
at the walk level for the ORIGINAL provider. The issue is that the original
provider doesn't cover all walks.

Let me re-examine what the LEAN code actually needs.

Looking at CaseObstructionsCore.lean:
  exists_zw_oneSided_provider produces:
    - t, phase
    - Left case: m(left t) = 2, even fires >= 2, right silent
    - Right case: symmetric

  zeroWinding_no_fireCount_ge3 uses this to construct entry conflict via
  binary_config_eq_of_even_intervalFireCount.

So the existing code requires BINARY active side. The generalized provider
with ternary active side would need a NEW theorem: ternary value return.

But ternary value return is NOT universally true (depends on transition).

DIFFERENT APPROACH: prove that the ORIGINAL (binary) provider always exists.

The CEs where only the generalized provider works have active ternary side.
But maybe those walk patterns can NEVER occur in actual good cycles?

Or maybe I need a completely different proof strategy.

Let me look more carefully at the CE walks.
"""
import sys
sys.path.insert(0, './claude')


def check_binary_provider(word, ms, n):
    """Original binary provider."""
    L = len(word)
    fire_steps = {}
    for p in range(n):
        fire_steps[p] = []
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    for t in range(n):
        fsteps = fire_steps[t]
        for s in fsteps:
            prev_fire = -1
            for k in range(s - 1, -1, -1):
                if word[k] == t:
                    prev_fire = k
                    break

            left_t = (t - 1) % n
            right_t = (t + 1) % n
            left_acc = 0
            right_acc = 0

            for a in range(s - 1, prev_fire, -1):
                if word[a] == t:
                    continue
                if word[a] == left_t:
                    left_acc += 1
                elif word[a] == right_t:
                    right_acc += 1
                lf = left_acc
                rf = right_acc

                if lf == 0 and ms[right_t] == 2 and rf >= 2 and rf % 2 == 0:
                    return True
                if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                    return True
    return False


def analyze_binary_ce_structure():
    """Look at CEs where binary provider fails but generalized works."""
    n = 5
    ms = [2, 3, 2, 3, 2]
    binary = [i for i in range(n) if ms[i] == 2]
    ternary = [i for i in range(n) if ms[i] == 3]

    print(f"n={n}, ms={ms}")
    print(f"Binary: {binary}, Ternary: {ternary}")

    ces = []
    for L in range(11, 16):
        def gen(word):
            if len(word) == L:
                disp = 0
                cw = 0
                for i in range(L):
                    nxt = word[(i + 1) % L]
                    diff = (nxt - word[i]) % n
                    if diff == 1:
                        cw += 1
                        disp += 1
                    elif diff == n - 1:
                        disp -= 1
                if disp != 0 or cw == 0:
                    return
                fc = [0] * n
                for m in word:
                    fc[m] += 1
                if any(f < 2 for f in fc):
                    return
                if max(fc) < 3:
                    return
                touched = set()
                for m in word:
                    touched.add(m)
                    touched.add((m-1)%n)
                    touched.add((m+1)%n)
                if len(touched) < n:
                    return

                if not check_binary_provider(word, ms, n):
                    ces.append((L, list(word), list(fc)))
                return

            last = word[-1]
            for nxt in [(last - 1) % n, last, (last + 1) % n]:
                word.append(nxt)
                gen(word)
                word.pop()

        for start in range(n):
            gen([start])

    print(f"\nTotal CEs (no binary provider): {len(ces)}")

    # Analyze structure of CEs
    # Key question: what do these walks look like?
    # Specifically: where are the oscillations?

    patterns = {}
    for L, word, fc in ces[:100]:
        # Find oscillation segments (back-and-forth at same proc pair)
        osc = []
        i = 0
        while i < L - 1:
            # Check if word[i] and word[i+1] differ by 1 and word[i+2] = word[i]
            if i + 2 < L:
                if word[i+2] == word[i] and abs((word[i+1] - word[i]) % n) in [1, n-1]:
                    # Oscillation start
                    j = i
                    while j + 2 < L and word[j+2] == word[j] and abs((word[j+1] - word[j]) % n) in [1, n-1]:
                        j += 2
                    osc.append((i, j+1, word[i], word[i+1]))
                    i = j + 1
                    continue
            i += 1

        # Which binary procs are involved in oscillations?
        osc_binary = set()
        osc_ternary = set()
        for start, end, p1, p2 in osc:
            if ms[p1] == 2:
                osc_binary.add(p1)
            else:
                osc_ternary.add(p1)
            if ms[p2] == 2:
                osc_binary.add(p2)
            else:
                osc_ternary.add(p2)

        key = (frozenset(osc_binary), frozenset(osc_ternary), tuple(fc))
        patterns[key] = patterns.get(key, 0) + 1

    print("\nCE patterns (osc_binary, osc_ternary, fc) -> count:")
    for key, count in sorted(patterns.items(), key=lambda x: -x[1])[:20]:
        ob, ot, fc = key
        print(f"  osc_binary={sorted(ob)}, osc_ternary={sorted(ot)}, fc={list(fc)}: {count}")

    # KEY QUESTION: In the CEs, are there excursions from binary procs
    # where the active side has even fires (but not binary)?
    print("\n\nDetailed CE analysis (first 5):")
    for L, word, fc in ces[:5]:
        print(f"\n  word={word}, fc={fc}")
        for b in binary:
            fsteps = [i for i in range(L) if word[i] == b]
            print(f"  Binary {b}: fires at {fsteps}")
            for idx in range(len(fsteps)):
                s1 = fsteps[idx]
                s2 = fsteps[(idx+1) % len(fsteps)]
                if s2 <= s1:
                    s2 += L
                exc = [word[k % L] for k in range(s1+1, s2)]
                left_b = (b-1) % n
                right_b = (b+1) % n
                lf = sum(1 for p in exc if p == left_b)
                rf = sum(1 for p in exc if p == right_b)
                print(f"    Excursion [{s1}->{s2%L}]: {exc}, left({left_b})={lf}, right({right_b})={rf}")


if __name__ == "__main__":
    analyze_binary_ce_structure()
