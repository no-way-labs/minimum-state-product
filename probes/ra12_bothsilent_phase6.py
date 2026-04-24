#!/usr/bin/env python3
"""
RA12 Part 6: Focused analytical proof check.

THEOREM TO PROVE: In any ZW good cycle with >=3 binary, all fc>=2, sub-threshold:
  There exists proc p with a phase where one neighbor fires 0 and
  the other (binary) neighbor fires >= 2.

APPROACH: Look at a binary proc b adjacent to another binary proc b'.
  - Both have fc = 2 (only valid even fc for binary).
  - b has 2 phases. b' fires 2 times across b's 2 phases.
  - Case 1: b' fires once in each phase of b -> J=1 or K=1 in both.
  - Case 2: b' fires twice in one phase -> J=0 in one phase, J=2 in other.
  - In Case 2: the J=2 phase has the binary neighbor b' firing 2 times.
    And in the OTHER phase, b' fires 0. The other neighbor fires >= 1 (J+K>=1).
    So we have (J=2, K>=1) in one phase and (J=0, K>=1) in the other.
    The J=2 phase has binary neighbor b' firing >=2 AND K>=1.
    But we need one side to be 0. The J=0 phase has K>=1.
    We want (J=0, K>=2): need K>=2. Not guaranteed.

Actually I'm overcomplicating this. Let me look from the TERNARY proc's perspective.

INSIGHT: The ternary procs are at positions n-2, n-1 (in sorted multiset).
They're adjacent to each other and to binary procs.

Let me look at the ternary-ternary pair boundary and the ternary-binary boundary.

Actually, the cleanest approach:

Consider the ternary proc q with fc(q) = 3 that's adjacent to a binary b (fc = 2).
q has 3 phases. b fires 2 times, so b fires in at most 2 of q's 3 phases.
By pigeonhole, at least 1 phase has b firing 0 (silent side).
In that phase, the other neighbor fires >= 1 (J+K >= 1).

Now: the OTHER neighbor of q is either ternary (the other ternary) or binary.

If other neighbor is binary (fc=2):
  The other binary fires >= 1 in the b-silent phase. Could be 1 or 2.
  If it's 2: we have (0, 2) - one-sided >=2 with binary active. Done.
  If it's 1: we have (0, 1) - normalForm. Not sufficient.

If other neighbor is ternary (fc >= 2):
  It fires >= 1 in the b-silent phase. But it's ternary, not binary.
  So even if it fires >= 2, the active neighbor is ternary. Doesn't help
  for the binary-neighbor criterion.

So the question reduces to: when the b-silent phase has only K=1 (normalForm),
does some OTHER proc provide the binary-one-sided >=2?

Let me verify this by looking at the actual walk structure.
For n=5 ms=[2,2,2,3,3], the walk [0,1,2,3,4,0,4,3,4,3,2,1]:
  fc = [2,2,2,3,3]
  Ternary at 3,4. Binary at 0,1,2.

  q=3 (ternary, fc=3), left=2(binary,fc=2), right=4(ternary,fc=3)
  Phases: [(2,0), (0,2), (0,1)]
  - Phase 0: left fires 2, right fires 0 -> right is ternary
  - Phase 1: left fires 0, right fires 2 -> left is binary(2), right fires 2
    BUT right is ternary! So active neighbor is ternary.
    Wait: J=0 means LEFT fires 0. LEFT=2 is binary. K=2 means RIGHT=4 fires 2.
    Right is ternary. So the ACTIVE side is ternary, not binary.
    For phase_dispatch_ec we need the ACTIVE neighbor to be binary (fc=2 means
    it fires all fires in this phase).
    Hmm but right=4 is ternary with fc=3, K=2 means it fires 2 out of 3.
    Not all fires. So this doesn't give the clean dispatch.

  q=4 (ternary, fc=3), left=3(ternary,fc=3), right=0(binary,fc=2)
  Phases: [(2,1), (0,1), (1,0)]
  - Phase 2: K=0 -> right=0(binary) fires 0. J=1 -> left=3(ternary) fires 1.
    One-sided (1,0) - but J=1 not >=2.

So at the fc>=3 ternary procs themselves, there's NO one-sided >=2 with binary active.

But the CYCLE has it somewhere. WHERE?

Let me check every proc:
word = [0,1,2,3,4,0,4,3,4,3,2,1]

p=0 (binary, fc=2), phases: left=4(ternary), right=1(binary)
p=1 (binary, fc=2), phases: left=0(binary), right=2(binary)
p=2 (binary, fc=2), phases: left=1(binary), right=3(ternary)

Look at p=1: both neighbors are binary. fc(0)=2, fc(2)=2.
p fires at steps where word[t]=1: t=1 and t=11.
Phase 0: interval from step 11+1=0 to step 1.
  word[0] = 0 -> left(1)=0 fires. J=1, K=0.
Phase 1: interval from step 1+1=2 to step 11.
  word[2..10] = [2,3,4,0,4,3,4,3,2]. left=0 fires at step 5 (word=0). right=2 fires
  at steps 2 and 10 (word=2). J=1 (0 fires once), K=2 (2 fires twice).
  So phase 1 at proc 1: (J=1, K=2). Both sides active. Not one-sided.

Phase 0: (1, 0) -> right=2 fires 0. J=1 only.

Hmm. Let me just be precise and trace all procs.

This needs actual computation. Let me simplify.
"""

from itertools import product as iproduct
from collections import Counter
import time


def enumerate_state_sequences(m, k):
    if k == 0:
        return [[0]]
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1:
            cw += 1
        elif diff == n - 1:
            ccw += 1
    return cw, ccw


def analyze_phases(word, n, q):
    L = len(word)
    left_q = (q - 1) % n
    right_q = (q + 1) % n
    fire_steps = [t for t in range(L) if word[t] == q]
    fc_q = len(fire_steps)
    if fc_q == 0:
        return []
    phases = []
    for idx in range(fc_q):
        s = fire_steps[idx]
        a = fire_steps[(idx - 1) % fc_q]
        J = K = 0
        t = (a + 1) % L
        while t != s:
            if word[t] == left_q:
                J += 1
            if word[t] == right_q:
                K += 1
            t = (t + 1) % L
        phases.append((J, K))
    return phases


def main():
    print("RA12 Part 6: Detailed walk tracing")
    print("=" * 70)

    # Trace the canonical example in detail
    n = 5
    ms = [2, 2, 2, 3, 3]
    w = [0, 1, 2, 3, 4, 0, 4, 3, 4, 3, 2, 1]
    L = len(w)
    fc = [0] * n
    for p in w:
        fc[p] += 1
    print(f"  word = {w}")
    print(f"  fc = {fc}")
    print(f"  ms = {ms}")

    for p in range(n):
        left_p = (p - 1) % n
        right_p = (p + 1) % n
        phases = analyze_phases(w, n, p)
        fire_steps = [t for t in range(L) if w[t] == p]

        print(f"\n  Proc {p} (m={ms[p]}, fc={fc[p]}), "
              f"left={left_p}(m={ms[left_p]},fc={fc[left_p]}), "
              f"right={right_p}(m={ms[right_p]},fc={fc[right_p]})")
        print(f"    Fire steps: {fire_steps}")

        for idx, (J, K) in enumerate(phases):
            s = fire_steps[idx]
            a = fire_steps[(idx - 1) % len(fire_steps)]
            interval = []
            t = (a + 1) % L
            while t != s:
                interval.append((t, w[t]))
                t = (t + 1) % L

            left_silent = J == 0
            right_silent = K == 0
            label = ""
            if left_silent and ms[left_p] == 2:
                label = f"LEFT-BINARY-SILENT, K={K}"
                if K >= 2 and ms[right_p] == 2:
                    label += " + RIGHT-BINARY-ACTIVE >= 2 *** BINGO ***"
                elif K >= 2:
                    label += f" + right-ternary-active"
            elif right_silent and ms[right_p] == 2:
                label = f"RIGHT-BINARY-SILENT, J={J}"
                if J >= 2 and ms[left_p] == 2:
                    label += " + LEFT-BINARY-ACTIVE >= 2 *** BINGO ***"
                elif J >= 2:
                    label += f" + left-ternary-active"
            else:
                label = f"J={J}, K={K}"

            print(f"    Phase {idx}: ({a}..{s}) interval={interval} -> {label}")

    # Now check: for ALL distinct walks at n=5, which proc provides the binary one-sided >=2?
    print(f"\n\n{'='*70}")
    print("  All distinct ZW walks with fc>=3 at n=5")
    print(f"{'='*70}")

    threshold = 4 * (3 ** (n - 2))

    from ra12_bothsilent_phase import generate_subthreshold_multisets, _enumerate_walks_dfs

    multisets = generate_subthreshold_multisets(n, threshold)

    for ms in multisets:
        max_len = min(sum(ms), 4 * n)
        min_len = 2 * n + 1
        for cycle_len in range(min_len, max_len + 1):
            walks = _enumerate_walks_dfs(n, cycle_len, ms)
            for w in walks:
                fc = [0] * n
                for p in w:
                    fc[p] += 1

                # Find provider
                providers = []
                for p in range(n):
                    if fc[p] < 2:
                        continue
                    left_p = (p - 1) % n
                    right_p = (p + 1) % n
                    phases = analyze_phases(w, n, p)
                    for J, K in phases:
                        if J == 0 and K >= 2 and ms[right_p] == 2:
                            providers.append((p, 'right-binary', K))
                            break
                        if K == 0 and J >= 2 and ms[left_p] == 2:
                            providers.append((p, 'left-binary', J))
                            break

                if providers:
                    prov = providers[0]
                    print(f"  ms={list(ms)}, word={w}, fc={fc}")
                    print(f"    Provider: proc {prov[0]} (m={ms[prov[0]]}, fc={fc[prov[0]]}), "
                          f"side={prov[1]}, active_fires={prov[2]}")
                    # What is the provider proc's m value?
                    prov_m = ms[prov[0]]
                    prov_fc = fc[prov[0]]
                    print(f"    Provider is {'binary' if prov_m == 2 else 'ternary'} "
                          f"with fc={prov_fc}")
                else:
                    print(f"  ms={list(ms)}, word={w}, fc={fc} -> NO PROVIDER!")


if __name__ == "__main__":
    main()
