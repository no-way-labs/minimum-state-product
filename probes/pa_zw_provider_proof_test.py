"""
Test the precise proof-level claim:

For proc i with binary neighbor b (left) and far neighbor f (right),
in an interval (a1, a2) between consecutive fires of i where b fires >= 2:

The mover sequence in (a1, a2) can be classified by which movers are b and f.
Let b1, b2 be the last two b-fires (in chronological order: b1 < b2 < a2).

Case A: No f fires in [b1, a2).
  Then take k2 = b1. In [b1, a2): b fires 2, f fires 0. WIN.
  (Assuming mover[b1] != i, which is true since b1 is a b-fire.)

Case B: Some f fires in [b1, a2), but no f fires in [b2, a2).
  Then take k2 = b2. In [b2, a2): b fires 1, f fires 0.
  But b fires 1 is ODD. BAD.
  However: we're taking the suffix from b2 (inclusive), so [b2, a2) has
  b firing at step b2 (count 1). Need even. So this doesn't work.

  Alternative: take k2 to be the step AFTER b2 (first non-b step).
  Then [k2, a2) has b fires 0, f fires 0.
  But k2 might equal a2 (no room). Or k2 might have mover = i (impossible).

  Actually, [b2+1, a2) has b fires 0 and f fires 0 (no f fires after b2 by assumption).
  Take k2 = b2+1 if it exists and mover != i.

  Wait but b2 < a2, so b2+1 <= a2. If b2+1 = a2, no room.
  By locality, mover[a2-1] adj to i. If b2 = a2-1, then b2+1 = a2. No room.

  But if b2 = a2-1 and there are no f-fires in [b2, a2):
  Go back to Case A: take k2 = b1. [b1, a2) has b=2, f=f_fires_between_b1_and_b2.
  If f fires in [b1, b2): that's Case B, f fires between b1 and b2.
  In [b1, a2) = [b1, b2) + [b2, a2): f fires in [b1, b2) + 0 in [b2, a2).

  Hmm, we need f fires 0 in the WHOLE suffix [k2, a2). Let me reconsider.

Actually, let me reformulate. The winning condition is:
  Suffix [k2, a2) where:
    b fires even times (0, 2, 4, ...)
    f fires 0 times
    mover[k2] != i

If b fires 0 in [k2, a2): need f fires 0 too. Take k2 right after last fire of (b or f).
But as shown above, this is hard when approach is from f.

If b fires 2 in [k2, a2): need f fires 0. Take k2 = second-to-last b-fire.
Then [k2, a2) has b >= 2 (at k2 and at the last b-fire). If no f fires after second-to-last b: WIN.

The question: is there always a pair of consecutive b-fires with no f-fire between/after?

Let me test this claim specifically.
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_claim(mover_word, moduli, n):
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word: fc[m] += 1
    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0: return None
    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None
    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None

    # For each proc i with binary neighbor b:
    for i in range(n):
        li = left(i, n)
        ri = right(i, n)

        # Try each side as the "binary" side
        for b, f in [(li, ri), (ri, li)]:
            if moduli[b] != 2: continue

            fire_steps_i = [k for k in range(CL) if mover_word[k] == i]
            if len(fire_steps_i) < 2: continue

            for idx in range(len(fire_steps_i)):
                a1 = fire_steps_i[idx]
                a2_raw = fire_steps_i[(idx + 1) % len(fire_steps_i)]
                if a2_raw <= a1: a2_raw += CL

                gap = list(range(a1 + 1, a2_raw))
                if not gap: continue

                # Find b-fires and f-fires in the interval
                b_fires_in = [k_raw for k_raw in gap if mover_word[k_raw % CL] == b]
                f_fires_in = [k_raw for k_raw in gap if mover_word[k_raw % CL] == f]

                if len(b_fires_in) < 2: continue

                # For each pair of consecutive b-fires: (b_fires_in[j], b_fires_in[j+1])
                # Check if no f fires in [b_fires_in[j], a2)
                for j in range(len(b_fires_in) - 1):
                    bj = b_fires_in[j]
                    # Check: no f fires in [bj, a2)
                    f_after_bj = [fk for fk in f_fires_in if fk >= bj]
                    if len(f_after_bj) == 0:
                        # WIN! b fires >= 2 in [bj, a2), f fires 0
                        b_in_suffix = sum(1 for bk in b_fires_in if bk >= bj)
                        if b_in_suffix % 2 == 0:
                            return (True, f"i={i}, b={b}, bj={bj}, b_in_suffix={b_in_suffix}")

    return (False, f"fc={fc}")

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]
s, f, sk = 0, 0, 0
fail_examples = []

for trial in range(500000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    r = test_claim(word, moduli, n)
    if r is None: sk += 1
    elif r[0]: s += 1
    else:
        f += 1
        if len(fail_examples) < 3:
            fail_examples.append((word, r[1]))

print(f"n=9 consec: Valid={s+f}, Pass={s}, Fail={f}")
for w, d in fail_examples:
    fc = [0]*n
    for m in w: fc[m] += 1
    print(f"  FAIL: {d}")

# Also try n=5
n = 5
moduli = [2, 2, 2, 3, 3]
s, f = 0, 0
for trial in range(500000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    r = test_claim(word, moduli, n)
    if r is None: continue
    if r[0]: s += 1
    else: f += 1
print(f"n=5 consec: Valid={s+f}, Pass={s}, Fail={f}")
