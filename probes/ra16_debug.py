#!/usr/bin/env python3
"""Debug the failed cases at n=5."""
import sys, os
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

def analyze_word(word, ms, n):
    """Full analysis of a word."""
    fc = Counter(word)
    CL = len(word)
    binary_pos = set(i for i in range(n) if ms[i] == 2)

    print(f"  CL={CL}, fc={dict(fc)}")
    print(f"  binary procs: {binary_pos}")
    print(f"  word: {word}")

    # Find firing steps for each proc
    firing_steps = defaultdict(list)
    for k, mover in enumerate(word):
        firing_steps[mover].append(k)

    # For each proc t with fc >= 3, show its phases
    for t in range(n):
        if fc[t] < 3:
            continue
        steps_t = firing_steps[t]
        left_t = (t - 1) % n
        right_t = (t + 1) % n
        print(f"\n  Proc {t}: fc={fc[t]}, fires at steps {steps_t}")
        print(f"    left={left_t} (m={ms[left_t]}), right={right_t} (m={ms[right_t]})")

        for phase_idx in range(len(steps_t)):
            a = steps_t[phase_idx]
            s = steps_t[(phase_idx + 1) % len(steps_t)]

            left_fires = 0
            right_fires = 0

            if s > a:
                phase_movers = [word[k] for k in range(a + 1, s)]
            else:
                phase_movers = [word[k] for k in range(a + 1, CL)] + [word[k] for k in range(0, s)]

            for m in phase_movers:
                if m == left_t:
                    left_fires += 1
                if m == right_t:
                    right_fires += 1

            is_left_good = (left_t in binary_pos and left_fires >= 2 and left_fires % 2 == 0 and right_fires == 0)
            is_right_good = (right_t in binary_pos and right_fires >= 2 and right_fires % 2 == 0 and left_fires == 0)

            status = ""
            if is_left_good:
                status = " <-- LEFT ACTIVE"
            elif is_right_good:
                status = " <-- RIGHT ACTIVE"

            print(f"    Phase {phase_idx}: [{a}..{s}), left fires {left_fires}, right fires {right_fires}, movers={phase_movers}{status}")


# Failing words from n=5, ms=[2,2,2,3,3]
ms = [2,2,2,3,3]
n = 5

failing_words = [
    (0, 4, 3, 4, 0, 4, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0),
    (0, 4, 3, 4, 0, 1, 2, 3, 4, 0, 4, 0, 4, 0, 4, 3, 2, 1, 0),
    (0, 4, 0, 4, 3, 4, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0),
]

print("=" * 70)
print(f"FAILING WORDS at ms={ms}")
print("=" * 70)

for i, w in enumerate(failing_words):
    print(f"\n--- Word {i+1} ---")
    analyze_word(w, ms, n)

# Also check: do these satisfy the "no safe processor" condition?
print("\n\n" + "=" * 70)
print("SAFE PROCESSOR CHECK")
print("=" * 70)

for i, w in enumerate(failing_words):
    fc = Counter(w)
    # A proc q is safe if it never fires AND its neighbors never fire?
    # Actually: safe = moverAt(k) != q AND moverAt(k) != left(q) AND moverAt(k) != right(q) for ALL k
    # I.e., q and both its neighbors never fire at ANY step
    safe = []
    for q in range(n):
        is_safe = True
        for mover in w:
            if mover == q or mover == (q-1)%n or mover == (q+1)%n:
                is_safe = False
                break
        if is_safe:
            safe.append(q)
    print(f"  Word {i+1}: safe procs = {safe}")

# Check: what about looking at ALL procs t (not just fc >= 3)?
# The theorem says "some proc q with fc(q) >= 3", and we need to find
# t and a TernaryPhase at t. TernaryPhase requires fc(t) >= 2.
# Actually re-read: TernaryPhase at t means t fires at least twice (creating a phase).
# The phase is between two consecutive firings of t.

print("\n\n" + "=" * 70)
print("EXTENDED SEARCH: all procs t with fc >= 2")
print("=" * 70)

for i, w in enumerate(failing_words):
    fc = Counter(w)
    print(f"\n--- Word {i+1}: CL={len(w)}, fc={dict(fc)} ---")

    for t in range(n):
        if fc[t] < 2:
            continue

        firing_steps_t = [k for k, m in enumerate(w) if m == t]
        left_t = (t - 1) % n
        right_t = (t + 1) % n

        for phase_idx in range(len(firing_steps_t)):
            a = firing_steps_t[phase_idx]
            s = firing_steps_t[(phase_idx + 1) % len(firing_steps_t)]

            if s > a:
                phase_movers = [w[k] for k in range(a + 1, s)]
            else:
                CL = len(w)
                phase_movers = [w[k] for k in range(a + 1, CL)] + [w[k] for k in range(0, s)]

            left_fires = phase_movers.count(left_t)
            right_fires = phase_movers.count(right_t)

            is_left_good = (left_t in set(j for j in range(n) if ms[j]==2) and left_fires >= 2 and left_fires % 2 == 0 and right_fires == 0)
            is_right_good = (right_t in set(j for j in range(n) if ms[j]==2) and right_fires >= 2 and right_fires % 2 == 0 and left_fires == 0)

            if is_left_good or is_right_good:
                side = "LEFT" if is_left_good else "RIGHT"
                print(f"  t={t}, phase {phase_idx}: [{a}..{s}), L_fires={left_fires}, R_fires={right_fires} <-- {side} ACTIVE")


# Also: what if we relax the phase definition?
# Maybe the phase doesn't need to be between consecutive firings of t.
# Maybe it's any interval where t fires at the boundaries?
# Let me re-read the Lean definition.
print("\n\n" + "=" * 70)
print("CHECKING: is the active side really = 2?")
print("=" * 70)
print("For all failing words, what are the neighbor fire counts per phase?")

for i, w in enumerate(failing_words[:1]):
    fc = Counter(w)
    binary_pos = set(j for j in range(n) if ms[j] == 2)
    print(f"\n--- Word {i+1}: fc={dict(fc)} ---")
    print(f"  Binary: {binary_pos}")

    for t in range(n):
        if fc[t] < 2:
            continue
        firing_steps_t = [k for k, m in enumerate(w) if m == t]
        left_t = (t - 1) % n
        right_t = (t + 1) % n

        for phase_idx in range(len(firing_steps_t)):
            a = firing_steps_t[phase_idx]
            s = firing_steps_t[(phase_idx + 1) % len(firing_steps_t)]

            if s > a:
                phase_movers = [w[k] for k in range(a + 1, s)]
            else:
                CL = len(w)
                phase_movers = [w[k] for k in range(a + 1, CL)] + [w[k] for k in range(0, s)]

            left_fires = phase_movers.count(left_t)
            right_fires = phase_movers.count(right_t)

            if left_fires == 0 or right_fires == 0:
                silent = "left" if left_fires == 0 else "right"
                active_nbr = right_t if left_fires == 0 else left_t
                active_fires = right_fires if left_fires == 0 else left_fires
                active_is_bin = active_nbr in binary_pos

                print(f"  t={t}, phase {phase_idx}: [{a}..{s}), silent={silent}, active={active_nbr}(m={ms[active_nbr]}) fires {active_fires}, bin={active_is_bin}")
