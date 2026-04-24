"""
PROOF: One-sided excursion always exists in ZW walks with fc >= 2, some fc >= 3,
>= 3 non-consecutive binary, cw > 0.

The one-sided excursion from a binary proc gives the provider.

Proof strategy:
  1. In a ZW walk with cw > 0, the walk makes at least one CW->CCW reversal
     and at least one CCW->CW reversal. (If all CW, net displacement = cw > 0;
     if all CCW, net = -ccw < 0. Both contradictions with ZW.)
  2. Consider the CW arcs and CCW arcs of the walk. These alternate.
  3. With >= 3 binary procs (non-consecutive) on the ring, the binary procs
     divide the ring into >= 3 ternary arcs. Each ternary arc has length >= 1.
  4. KEY: No CW arc can traverse the ENTIRE ring (net would be >= n, but ZW
     requires net = 0). So each CW arc traverses at most n-1 positions.
  5. A CW arc that starts at position p and ends at position q (q = p + length CW)
     traverses the segment [p, q] of the ring. It enters this segment by firing p,
     and exits by firing q, then the walk reverses.
  6. The reversal at q means: after firing q, the walk goes CCW. So the CCW arc
     starts at q and goes back toward p.
  7. Now: if p is binary and the CW arc [p, q] stays within one ternary arc
     (doesn't cross another binary), then the excursion from p stays on one side.

But the CW arc might cross multiple binary procs. The key question is whether
SOME binary proc has a one-sided excursion.

ALTERNATIVE: Instead of looking at CW arcs, look at EXCURSIONS from binary procs.

A binary proc b has consecutive firings at steps s1, s2. The excursion between
them is the sub-walk from s1 to s2. For this excursion to be one-sided, the walk
must not cross b again (it doesn't, since b only fires at the endpoints) and
must stay on one side of b on the ring.

The walk between s1 and s2 starts at b, makes some CW/CCW moves, and returns to b.
The net displacement in [s1, s2] is 0 (leaves b, returns to b). The walk could:
(a) Go CW from b, reach some point, come back — one-sided CW
(b) Go CCW from b, reach some point, come back — one-sided CCW
(c) Go both CW and CCW from b — two-sided

For (c), the excursion reaches procs on BOTH sides of b. This means the walk
crosses b's CCW neighbor AND b's CW neighbor during the excursion. Since b doesn't
fire during the excursion, the walk leaves b at step s1+1 (going to a neighbor),
eventually visits both sides, and returns at step s2-1 (from a neighbor).

With fc >= 2, the walk visits all procs. For a binary b with fc=2, the two
excursions partition the entire walk (except the firing steps of b). If one
excursion covers procs on both sides, it might still leave the other excursion
as one-sided.

LEMMA: With fc >= 2 for all and >= 3 binary (non-consecutive) on ring of n >= 5,
at least one binary has a one-sided excursion.

PROOF by contradiction: Assume every binary proc has only two-sided excursions.

For binary b with fc(b) = k: it has k excursions (or k-1 excursions for a cycle).
Actually, for a cyclic walk, binary b fires at steps s_1 < s_2 < ... < s_k.
This gives k excursions: [s_1,s_2], [s_2,s_3], ..., [s_k, s_1+L].

Claim: if ALL excursions of ALL binary procs are two-sided, then the walk has
a very specific structure (it oscillates between binary procs on opposite sides
of the ring). This severely constrains the walk and leads to a contradiction
with the hypotheses (specifically, fc >= 3 at some proc forces extra firings
that create a one-sided excursion).

Let me verify computationally that no walk with ALL binary excursions two-sided
exists under our constraints.
"""
import sys
sys.path.insert(0, './claude')


def all_excursions_two_sided(word, ms, n):
    """Check if ALL excursions from ALL binary procs are two-sided."""
    L = len(word)
    binary_procs = [i for i in range(n) if ms[i] == 2]

    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    for b in binary_procs:
        fsteps = fire_steps[b]
        if len(fsteps) < 2:
            continue

        for idx in range(len(fsteps)):
            s1 = fsteps[idx]
            s2 = fsteps[(idx + 1) % len(fsteps)]
            if s2 <= s1:
                s2 += L

            exc = [word[k % L] for k in range(s1 + 1, s2)]
            if not exc:
                # Empty excursion is vacuously one-sided
                return False  # Has one-sided (empty = trivially one-sided)

            exc_set = set(exc)
            cw_side = set()
            ccw_side = set()
            for d in range(1, n):
                cw_side.add((b + d) % n)
                ccw_side.add((b - d) % n)

            if exc_set <= cw_side or exc_set <= ccw_side:
                return False  # Has a one-sided excursion

    return True  # All two-sided


def check_all_two_sided():
    """Check if any valid walk has ALL excursions two-sided."""
    n = 5
    ms = [2, 3, 2, 3, 2]
    print(f"n={n}, ms={ms}")

    total = 0
    all_two = 0

    for L in range(11, 16):
        count = 0
        count_all_two = 0

        def gen(word):
            nonlocal count, count_all_two
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

                count += 1
                if all_excursions_two_sided(word, ms, n):
                    count_all_two += 1
                return

            last = word[-1]
            for nxt in [(last - 1) % n, last, (last + 1) % n]:
                word.append(nxt)
                gen(word)
                word.pop()

        for start in range(n):
            gen([start])

        print(f"  L={L}: {count} valid, {count_all_two} all-two-sided")
        total += count
        all_two += count_all_two

    print(f"\nTOTAL: {total} valid, {all_two} all-two-sided")
    print(f"CONCLUSION: {'ALL have one-sided' if all_two == 0 else 'SOME all-two-sided exist'}")


if __name__ == "__main__":
    check_all_two_sided()
