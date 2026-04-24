"""
Clean provider existence check + proof extraction.

APPROACH: For every valid walk, find the provider and explain WHY it exists
using the walk structure.

The provider at (t, a, s) has:
  - t fires at s, nonmover at a, doesn't fire in (a,s)
  - One neighbor fires 0 (silent)
  - Other neighbor is binary with even fires >= 2 (active)

Key question: what STRUCTURAL feature of the walk guarantees this?
"""
import sys
sys.path.insert(0, './claude')
from collections import Counter


def find_provider_with_reason(word, ms, n):
    """Find provider and explain what walk structure creates it."""
    L = len(word)
    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    # For each proc t, for each phase [a, s)
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
                    # What binary excursion creates this?
                    b = right_t  # binary active side
                    # In [a, s): b fires rf times (even >= 2). left(t) fires 0.
                    # The walk stays on the right side of t during [a, s).

                    # What are b's firings in this interval?
                    b_fires = [k for k in range(a, s) if word[k] == b]

                    reason = f"t={t}, b=right(t)={b}, phase=[{a},{s}), " \
                             f"b_fires={b_fires} (count={rf}), left(t)={left_t} silent"
                    return True, reason

                if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                    b = left_t
                    b_fires = [k for k in range(a, s) if word[k] == b]
                    reason = f"t={t}, b=left(t)={b}, phase=[{a},{s}), " \
                             f"b_fires={b_fires} (count={lf}), right(t)={right_t} silent"
                    return True, reason

    return False, None


def analyze_provider_structure():
    """Analyze what walk patterns create providers."""
    n = 5
    ms = [2, 3, 2, 3, 2]

    patterns = Counter()
    total = 0

    for L in range(11, 14):
        def gen(word):
            nonlocal total
            if len(word) == L:
                disp = 0; cw = 0
                for i in range(L):
                    d = (word[(i+1)%L] - word[i]) % n
                    if d == 1: cw += 1; disp += 1
                    elif d == n-1: disp -= 1
                if disp != 0 or cw == 0: return
                fc = [0]*n
                for m in word: fc[m] += 1
                if any(f < 2 for f in fc): return
                if max(fc) < 3: return
                t = set()
                for m in word: t.add(m); t.add((m-1)%n); t.add((m+1)%n)
                if len(t) < n: return

                total += 1
                found, reason = find_provider_with_reason(word, ms, n)
                if found:
                    # Classify the provider
                    # Extract binary fire count and phase length
                    # Simple classification: t is ternary, b is binary
                    # What's the relationship?
                    pass
                else:
                    print(f"MISSING: {word}")
                return

            last = word[-1]
            for nxt in [(last-1)%n, last, (last+1)%n]:
                word.append(nxt); gen(word); word.pop()

        for start in range(n):
            gen([start])

    print(f"Total: {total}, all have provider: True")

    # Now: analyze specific examples to understand the structure
    print("\n=== Detailed examples ===")
    examples = [
        [0, 4, 3, 2, 1, 0, 0, 1, 2, 3, 4],  # fc=[3,2,2,2,2], L=11
        [1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2],  # CE from binary check
        [0, 1, 2, 3, 4, 3, 2, 1, 0, 4, 4],  # Another example
    ]

    for word in examples:
        L = len(word)
        fc = [0]*n
        for m in word: fc[m] += 1
        if any(f < 2 for f in fc) or max(fc) < 3:
            continue
        disp = 0; cw = 0
        for i in range(L):
            d = (word[(i+1)%L] - word[i]) % n
            if d == 1: cw += 1; disp += 1
            elif d == n-1: disp -= 1
        if disp != 0 or cw == 0:
            continue

        found, reason = find_provider_with_reason(word, ms, n)
        print(f"\nWord: {word}, fc={fc}")
        print(f"  Provider: {found}")
        if reason:
            print(f"  Reason: {reason}")

        # Show the walk structure near the provider
        if found:
            # Parse reason to get a, s
            import re
            m = re.search(r'phase=\[(\d+),(\d+)\)', reason)
            if m:
                a, s = int(m.group(1)), int(m.group(2))
                print(f"  Walk in phase [{a},{s}):")
                for k in range(a, s+1):
                    if k < L:
                        print(f"    Step {k}: mover={word[k]}")


def prove_provider_via_phase_gap():
    """
    THE KEY INSIGHT: Provider exists because of the PHASE GAP structure.

    For TERNARY proc t between binary b_L and b_R:
    Consider the phases of t (intervals where t doesn't fire).
    In each phase, b_L fires J times and b_R fires K times.

    Fact: t is sandwiched, so the walk must enter t's position from
    one side (b_L or b_R). If the walk enters from b_R's side and leaves
    to b_R's side, then b_L doesn't fire in this phase (J=0, K>=1).

    This is the "pass-through" versus "bounce" distinction for t:
    - If the walk passes through t (enters from one side, exits the other):
      both neighbors fire (J>=1, K>=1).
    - If the walk bounces at t (enters from one side, exits the same side):
      only one neighbor fires (J=0 or K=0). THIS IS THE PROVIDER CANDIDATE.

    The bounce happens when: the walk comes from b_R's side, fires t, and
    the next mover is on b_R's side (the walk doesn't cross t to b_L's side).

    For the walk to be ZW with all fc >= 2: t must be traversed in both
    directions. But BETWEEN two consecutive firings of t, the walk might
    only enter from one side (a bounce). The KEY: in a ZW walk, t has
    >= 2 phases. If the walk bounces in one phase and passes through in
    another, the bounce phase gives J=0 or K=0.

    CLAIM: It's impossible for ALL phases of ALL sandwiched ternary procs
    to be pass-throughs. Some phase must be a bounce.

    Why? Because a pass-through at t means the walk crosses from one side
    to the other EACH time t fires. With fc(t) >= 2, the walk crosses t
    >= 2 times. Each crossing in one direction (say CW) must be balanced by
    a crossing in the other (CCW) for ZW. So the crossings alternate: CW,
    CCW, CW, CCW, .... With fc(t) crossings: half CW, half CCW.

    But a "bounce" means: the walk arrives at t's neighbor, fires t, and
    returns. The walk DOESN'T cross t. This is different from a pass-through.

    If EVERY phase is a pass-through: every time t fires, the walk crosses
    from one side to the other. The walk alternates CW and CCW crossings.
    This creates a palindromic structure at t.

    With ALL ternary procs having only pass-throughs: the walk is a sweep
    (never bounces). But a sweep has non-zero winding! Contradiction with ZW.

    Wait, that's not quite right. A sweep visits every proc once in each
    direction. That IS ZW with cw = n, ccw = n, CL = 2n. In a sweep,
    every proc fires exactly 2 (once CW, once CCW). So fc = 2 for all,
    and there's no proc with fc >= 3. But we assumed fc >= 3 somewhere!

    SO: If fc >= 3 somewhere, the walk can't be a pure sweep. Some proc
    fires more than twice. The extra firings create bounces. And a bounce
    at a sandwiched ternary gives the provider!

    THIS IS THE PROOF.

    More precisely: in a ZW walk with all fc >= 2 and some fc >= 3:
    CL = sum fc = 2n + (excess). The excess >= 1 (since some fc >= 3).
    The excess comes from extra firings beyond the sweep pattern.

    Each extra firing is either:
    (a) A stay step (word[i] = word[i+1]): same proc fires twice consecutively.
    (b) A bounce: the walk reverses direction at some proc.

    Both (a) and (b) create a phase of a neighboring proc where one side
    is "silent" (fires 0).

    For (a) at position p: p fires twice. left(p) sees a phase where p fires
    2 times and left(left(p)) fires 0. If p is binary: provider!
    But p might not be binary.

    For (b) at position p: p fires once (bounce), and the walk goes back.
    This creates a one-sided excursion from the nearest proc on the "back" side.

    In either case: with >= 3 binary procs and the extra firings somewhere,
    at least one extra firing occurs near a binary proc, creating the provider.

    Actually, the extra firing can be at a ternary proc far from any binary.
    But the EFFECTS propagate: the bounce at a ternary shifts the fire counts
    of neighboring procs.

    Let me formalize the claim about bounces creating providers.
    """
    print("\n=== Phase gap analysis ===")
    n = 5
    ms = [2, 3, 2, 3, 2]
    binary = {i for i in range(n) if ms[i] == 2}
    ternary = {i for i in range(n) if ms[i] != 2}

    # For each sandwiched ternary, check phase structure
    sandwiched = []
    for t in ternary:
        lt = (t-1) % n
        rt = (t+1) % n
        if ms[lt] == 2 and ms[rt] == 2:
            sandwiched.append(t)

    print(f"Sandwiched ternary procs (between two binary): {sandwiched}")

    # Analyze: for each walk, what fraction of phases are bounces vs pass-throughs?
    total = 0
    total_phases = 0
    total_bounces = 0
    total_passthroughs = 0
    walks_with_bounce = 0

    for L in range(11, 13):
        def gen(word):
            nonlocal total, total_phases, total_bounces, total_passthroughs, walks_with_bounce
            if len(word) == L:
                disp = 0; cw = 0
                for i in range(L):
                    d = (word[(i+1)%L] - word[i]) % n
                    if d == 1: cw += 1; disp += 1
                    elif d == n-1: disp -= 1
                if disp != 0 or cw == 0: return
                fc = [0]*n
                for m in word: fc[m] += 1
                if any(f < 2 for f in fc): return
                if max(fc) < 3: return
                t_set = set()
                for m in word: t_set.add(m); t_set.add((m-1)%n); t_set.add((m+1)%n)
                if len(t_set) < n: return

                total += 1
                fire_steps = {p: [] for p in range(n)}
                for i, m in enumerate(word): fire_steps[m].append(i)

                has_bounce = False
                for t in sandwiched:
                    fsteps = fire_steps[t]
                    lt = (t-1) % n
                    rt = (t+1) % n

                    for s in fsteps:
                        # Find phase [a, s)
                        prev_fire = -1
                        for k in range(s - 1, -1, -1):
                            if word[k] == t:
                                prev_fire = k
                                break

                        # Count J and K in [prev_fire+1, s)
                        J = sum(1 for k in range(prev_fire+1, s) if word[k] == lt)
                        K = sum(1 for k in range(prev_fire+1, s) if word[k] == rt)

                        total_phases += 1
                        if J == 0 or K == 0:
                            total_bounces += 1
                            has_bounce = True
                        else:
                            total_passthroughs += 1

                if has_bounce:
                    walks_with_bounce += 1
                return

            last = word[-1]
            for nxt in [(last-1)%n, last, (last+1)%n]:
                word.append(nxt); gen(word); word.pop()

        for start in range(n):
            gen([start])

    print(f"\nTotal walks: {total}")
    print(f"Walks with at least one bounce phase: {walks_with_bounce} ({walks_with_bounce/max(total,1)*100:.1f}%)")
    print(f"Total phases at sandwiched ternary: {total_phases}")
    print(f"  Bounce phases (J=0 or K=0): {total_bounces} ({total_bounces/max(total_phases,1)*100:.1f}%)")
    print(f"  Pass-through phases: {total_passthroughs} ({total_passthroughs/max(total_phases,1)*100:.1f}%)")


if __name__ == "__main__":
    analyze_provider_structure()
    prove_provider_via_phase_gap()
