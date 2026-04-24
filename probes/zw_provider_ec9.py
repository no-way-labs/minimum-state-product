"""
Investigation part 9: Why does the matching step always exist?

For binary b with fc=2, fires at a1 and a2 (consecutive):
- Between [a1+1, a2): b doesn't fire. S_b is fixed.
- At step a2: (L, S, R) = (L_a2, S_a2, R_a2)
- Need: some k in (a1, a2) where mover != b and (L_k, S_k, R_k) = (L_a2, S_a2, R_a2)

Since S is fixed (b doesn't fire in between), S_k = S_a2 automatically.
We need: L_k = L_a2 AND R_k = R_a2.

L = left(b)'s value, R = right(b)'s value.

The key: in ZW walk between a1 and a2, the walk passes through b's position.
But b doesn't fire! So the walk must go through b's neighbors.

Actually, let's think about this differently.

In a ZW walk of length CL > 2n with fc >= 3 at some proc:
- The walk has an "excursion" — a part where it goes forward and comes back
- During this excursion, binary proc b (fc=2) has its two fires at the
  "boundaries" of the main traversal
- The excursion happens between b's two fires
- During the excursion, the walk leaves b, goes to some distance, comes back,
  then proceeds to b's second fire

The excursion guarantees that at some point the walk is "at" b's neighbor
going in one direction, then later "at" b's neighbor going in the other
direction. The neighbor's value changes are even (binary) or zero.

Let me check what EXACTLY the walk looks like between a1 and a2.
"""

def fire_counts(word, n):
    fc = [0] * n
    for p in word: fc[p] += 1
    return fc

# Example word: (0, 1, 2, 3, 4, 0, 4, 3, 4, 3, 2, 1)
# fc = [2, 2, 2, 3, 3]
# Binary: 0, 1, 2 (all fc=2)

word = (0, 1, 2, 3, 4, 0, 4, 3, 4, 3, 2, 1)
n = 5
L = len(word)
fc = fire_counts(word, n)

print("Word:", word)
print("FC:", fc)
print()

# For binary proc 2 (fc=2): fires at steps 2 and 10
b = 2
fire_steps = [k for k in range(L) if word[k] == b]
print(f"Proc {b}: fires at steps {fire_steps}")
a1, a2 = fire_steps[0], fire_steps[1]
print(f"Between steps {a1} and {a2}:")
for k in range(a1, a2+1):
    p = word[k]
    direction = "→" if word[(k+1)%L] == (p+1)%n else "←"
    left_b = (b - 1) % n  # = 1
    right_b = (b + 1) % n  # = 3
    print(f"  Step {k}: mover={p} {direction}  "
          f"(word segment: {word[k]}→{word[(k+1)%L]})")

print()
print(f"left(b) = {(b-1)%n}, right(b) = {(b+1)%n}")
print()

# How many times does left(b)=1 fire in (a1, a2)?
left_fires = sum(1 for k in range(a1+1, a2) if word[k] == (b-1)%n)
right_fires = sum(1 for k in range(a1+1, a2) if word[k] == (b+1)%n)
print(f"left(b)={1} fires {left_fires} times in ({a1},{a2})")
print(f"right(b)={3} fires {right_fires} times in ({a1},{a2})")

# The EC is at step 3 (non-mover for b=2) matching step 10 (mover for b=2)
# Between step 3 and step 10:
print(f"\nBetween EC non-mover step 3 and mover step 10:")
for k in range(3, 10+1):
    p = word[k]
    is_left = (p == 1)
    is_right = (p == 3)
    marker = ""
    if is_left: marker = " <-- left(b)"
    if is_right: marker = " <-- right(b)"
    print(f"  Step {k}: mover={p}{marker}")

left_fires_sub = sum(1 for k in range(3, 10) if word[k] == 1)
right_fires_sub = sum(1 for k in range(3, 10) if word[k] == 3)
print(f"left(b) fires {left_fires_sub} times in [3, 10)")
print(f"right(b) fires {right_fires_sub} times in [3, 10)")
print(f"left(b) is binary (m=2): {left_fires_sub} fires → Even: {left_fires_sub % 2 == 0}")
print(f"right(b) fires: {right_fires_sub}")

print()
print("=" * 70)
print("ANALYSIS: The walk between b's fires at steps 2 and 10:")
print("  Steps: 2(b=2), 3(3), 4(4), 5(0), 6(4), 7(3), 8(4), 9(3), 10(b=2)")
print()
print("  The walk goes: 2→3→4→0→4→3→4→3→2")
print("  This is: forward to 4, jump to 0, then back-and-forth 4-3-4-3, then to 2")
print()
print("  Between step 3 and step 10:")
print("  left(b)=1 fires 0 times → value preserved ✓")
print("  right(b)=3 fires 3 times → ODD! But right(b) is ternary (m=3)!")
print()
print("  Wait: right(b)=3 is TERNARY, not binary.")
print("  So 'even fires → preserved' doesn't apply for ternary.")
print("  The EC must work differently here.")
print()

# Let's check: between step 3 and 10, right(b)=3 fires 3 times.
# But the EC context at step 3 matches step 10 anyway.
# This means right(b)'s value at step 3 equals right(b)'s value at step 10.
# With 3 fires of a ternary proc, value can return: 0→1→2→0 (incrementing).

# Actually, we verified computationally that the context matches.
# The question is: what GENERAL mechanism guarantees this?

print("=" * 70)
print("NEW INSIGHT: The matching doesn't require even fires at neighbors.")
print("It requires that the neighbor VALUES happen to match.")
print("This is a consequence of the specific walk structure + transition tables.")
print()
print("But for a proof, we need a STRUCTURAL argument, not case-by-case.")
print()
print("Actually, look at the OTHER EC pair: step 2 vs step 11.")
print("Step 11 is AFTER step 10 (wrapping around).")
print("Between step 10 and step 2 (wrapping, via steps 11, 0, 1):")

for k in [10, 11, 0, 1, 2]:
    p = word[k]
    print(f"  Step {k}: mover={p}")

left_fires_wrap = sum(1 for k in [10, 11, 0, 1] if word[k] == 1)
right_fires_wrap = sum(1 for k in [10, 11, 0, 1] if word[k] == 3)
print(f"left(b) fires {left_fires_wrap} times in wrap [10, 2)")
print(f"right(b) fires {right_fires_wrap} times in wrap [10, 2)")
print()
print("left(b)=1: fires 1 time (step 11) — ODD for binary → value FLIPS")
print("But wait, EC at step 2 uses step 11 as nonmover and step 2 as mover.")
print("Between step 11 and step 2: step 11(mover=1), step 0(mover=0), step 1(mover=1), step 2(mover=2)")
print("So step 11 to step 2: left(b)=1 fires at steps 1. That's 1 fire.")
print()

# I need to be more careful about the direction of the interval.
# EC pair: mover step = 2, nonmover step = 11.
# We need L and R to match at these steps.
# The cycle wraps: step 11 comes after step 10 but before step 0 (modularly).

# Actually, the interval for preservation is: min(k1,k2) to max(k1,k2).
# For k1=2, k2=11: interval [3, 11) for one direction,
# or [11+1, 2) = [0, 2) wrapping for the other.

# Between step 2 and step 11:
print("Between step 2 (mover for b=2) and step 11 (non-mover for b=2):")
for k in range(2, 12):
    p = word[k]
    marker = ""
    if p == 1: marker = " <-- left(b)"
    if p == 3: marker = " <-- right(b)"
    print(f"  Step {k}: mover={p}{marker}")

# How about between step 11 and step 2 (wrapping)?
print("Between step 11 (non-mover) and step 2 (mover) wrapping:")
for k in [11, 0, 1, 2]:
    p = word[k]
    marker = ""
    if p == 1: marker = " <-- left(b)"
    if p == 3: marker = " <-- right(b)"
    print(f"  Step {k}: mover={p}{marker}")

l_fires = sum(1 for k in [11, 0, 1] if word[k] == 1)
r_fires = sum(1 for k in [11, 0, 1] if word[k] == 3)
print(f"  left(b)=1: {l_fires} fires → Even: {l_fires%2==0}")
print(f"  right(b)=3: {r_fires} fires")

print()
print("So between step 11 and step 2:")
print("  left(b)=1 fires 1 time (step 11) → value changes (binary flip)")
print("  right(b)=3 fires 0 times → value preserved")
print()
print("But the EC says ctx matches at steps 2 and 11!")
print("If left(b) fired once between them, how can left(b) value match?")
print()
print("Answer: the mover at step 11 IS left(b)=1.")
print("So at step 11, the config is BEFORE left(b) fires.")
print("left(b) value at step 11 = left(b) value at step 11 BEFORE firing.")
print("Then left(b) fires at step 11, changing its value.")
print("Then at steps 0 and 1: mover=0 and mover=1.")
print("left(b) fires AGAIN at step 1.")
print("So left(b) fires TWICE in (11, 2): at steps 11 and 1. That's even!")
print()
print("Wait, but step 11 is the non-mover step for b=2.")
print("The interval for preservation should be (11, 2) or (2, 11).")
print("The config at step k is the config BEFORE the firing at step k.")
print("So between steps 11 and 2, the firings that matter are at steps 11, 0, 1.")
print("left(b)=1 fires at steps 11 and 1 → 2 fires → EVEN → binary preserved!")
print("right(b)=3 fires 0 times → preserved!")
print()
print("AH HA! So the mechanism DOES rely on even fires, but counting")
print("fires in [nonmover_step, mover_step) including the nonmover step!")

# Let me verify: between step 11 and step 2 (not inclusive of 2):
# Fires of left(b)=1: steps 11 and 1 → 2 (even) ✓
# Fires of right(b)=3: 0 ✓
print()
print("CORRECT: Between nonmover step 11 and mover step 2:")
print("  left(b) fires at steps 11, 1 → 2 times (even) → binary value returns")
print("  right(b) fires 0 times → value preserved")
print("  b fires 0 times → value preserved (it fires at step 2 which is excluded)")
