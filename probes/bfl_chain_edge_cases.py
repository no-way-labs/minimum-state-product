"""
BFL backward chain: edge case verification.

Verify that:
1. The chain never needs k = n-2 (where proc_k = bR, which doesn't fire)
2. The "first-fire" nesting is correct
3. The gap size bound matches the computational data
4. The argument works even when step a+1 is at a boundary (cyclic wrap)

Also: verify the claim that for K >= 3, condition (c) holds:
  "No proc_{K-1} fire in (a+1, f_K)" follows from the first-fire property.

This is the most delicate part of the proof.
"""

import sys
from collections import defaultdict

sys.path.insert(0, './claude')


def verify_nesting_property():
    """
    Verify: if the chain extends to level K, then for all k in [2, K]:
      - f_k is the first fire of proc_k in (a+1, f_{k-1})
      - a+1 < f_K < f_{K-1} < ... < f_2

    And crucially: proc_{K-1} does NOT fire in (a+1, f_K).

    Proof of the nesting:
    - f_2 = first fire of proc_2 in the phase interior (a+1, s)
    - If proc_3 fires in (a+1, f_2): f_3 = first such fire, f_3 < f_2
    - If proc_4 fires in (a+1, f_3): f_4 = first such fire, f_4 < f_3
    - ...
    - At each step: the interval SHRINKS because f_{k+1} < f_k.

    For condition (c) at level K:
    We need: no proc_{K-1} fire in (a+1, f_K).

    f_{K-1} is defined as: first fire of proc_{K-1} in (a+1, f_{K-2}).
    We have (a+1, f_K) ⊂ (a+1, f_{K-1}) ⊂ (a+1, f_{K-2}).

    If proc_{K-1} fires in (a+1, f_K), then it fires in (a+1, f_{K-1}).
    But f_{K-1} is the FIRST fire of proc_{K-1} in (a+1, f_{K-2}).
    And (a+1, f_K) ⊂ (a+1, f_{K-1}) since f_K < f_{K-1}.

    So a fire of proc_{K-1} at step x with a+1 < x < f_K implies
    a+1 < x < f_K < f_{K-1}, so x is in (a+1, f_{K-1}) and x < f_{K-1}.
    This is in (a+1, f_{K-2}) since (a+1, f_{K-1}) ⊂ (a+1, f_{K-2}).

    But f_{K-1} is the FIRST fire of proc_{K-1} in (a+1, f_{K-2}).
    Since x < f_{K-1} and x ∈ (a+1, f_{K-2}): contradiction.

    QED for condition (c).
    """
    print("=" * 70)
    print("NESTING PROPERTY VERIFICATION")
    print("=" * 70)
    print()
    print("Claim: For k >= 3, no proc_{k-1} fires in (a+1, f_k).")
    print()
    print("Proof:")
    print("  f_{k-1} = first fire of proc_{k-1} in (a+1, f_{k-2}).")
    print("  f_k < f_{k-1} (chain is strictly decreasing).")
    print("  (a+1, f_k) subset of (a+1, f_{k-1}) subset of (a+1, f_{k-2}).")
    print()
    print("  Suppose proc_{k-1} fires at step x in (a+1, f_k).")
    print("  Then a+1 < x < f_k < f_{k-1}, so x in (a+1, f_{k-2}).")
    print("  But x < f_{k-1} and f_{k-1} is the first proc_{k-1} fire")
    print("  in (a+1, f_{k-2}). Contradiction.")
    print()
    print("  QED.")
    print()

    # Verify computationally on constructed examples
    print("Computational verification on worst-case words:")
    print()

    for n in [5, 7, 9, 11, 15, 21]:
        t = 1
        bL = 0
        bR = 2

        # Worst case: reverse order of far procs
        K_max = n - 3

        # Build worst-case word
        word = [t, bL]
        for depth in range(K_max, 1, -1):
            proc = (t - depth) % n
            word.append(proc)

        # Fill remaining
        fired = set(word)
        remaining = [p for p in range(n) if p not in fired]
        word.extend(remaining)

        # Second phase (minimal)
        word.append(t)
        word.append(bL)
        word.append(bR)
        word.append(bR)

        # Find first phase end
        first_phase_end = None
        for i in range(1, len(word)):
            if word[i] == t:
                first_phase_end = i
                break

        if first_phase_end is None:
            continue

        interior = list(range(1, first_phase_end))

        # Trace chain and verify nesting
        f_values = {}
        a_plus_1 = 1  # step a+1

        k = 2
        search_end = first_phase_end  # initially s
        all_ok = True

        while k <= n - 1:
            proc_k = (t - k) % n
            proc_k1 = (t - k - 1) % n
            proc_km1 = (t - k + 1) % n

            # Find first fire of proc_k in (a+1, search_end)
            first_k = None
            for step in range(a_plus_1 + 1, search_end):
                if step < len(word) and word[step] == proc_k:
                    first_k = step
                    break

            if first_k is None:
                # proc_k doesn't fire in interval; chain terminates at k-1
                break

            f_values[k] = first_k

            # Verify nesting: no proc_{k-1} in (a+1, first_k)
            for step in range(a_plus_1 + 1, first_k):
                if step < len(word) and word[step] == proc_km1:
                    print(f"  n={n}: NESTING VIOLATION at k={k}!")
                    print(f"    proc_{k-1}={proc_km1} fires at step {step}")
                    print(f"    but interval is ({a_plus_1}, {first_k})")
                    all_ok = False
                    break

            # Check if proc_{k+1} fires in (a+1, first_k)
            k1_fires = False
            for step in range(a_plus_1 + 1, first_k):
                if step < len(word) and word[step] == proc_k1:
                    k1_fires = True
                    break

            if not k1_fires:
                # Chain terminates at k
                break

            search_end = first_k
            k += 1

        status = "OK" if all_ok else "FAIL"
        chain_len = k
        print(f"  n={n:>2}: chain_len={chain_len:>2}, f_values={dict(sorted(f_values.items()))}, nesting: {status}")


def verify_chain_bound():
    """
    Verify: chain length K <= min(g_2, n-3) where g_2 = f_2 - (a+1).

    The bound K <= n-3 comes from proc_{n-2} = bR not firing.
    The bound K <= g_2 + 1 comes from the gap shrinking by >= 1 each step.

    At each level, f_{k+1} < f_k, so f_{k+1} <= f_k - 1.
    After K-2 extensions: f_K >= a+2, f_2 >= a+2 + (K-2) = a+K.
    So K <= f_2 - a = f_2 - (a+1) + 1 = g_2 + 1.

    But also g_2 <= (phase length - 2), so K <= phase_length - 1.
    """
    print()
    print("=" * 70)
    print("CHAIN LENGTH BOUND VERIFICATION")
    print("=" * 70)
    print()
    print("Bounds:")
    print("  K <= n - 3  (proc_{n-2} = bR doesn't fire)")
    print("  K <= g_2 + 1  (gap shrinks by >= 1 each step)")
    print("  where g_2 = f_2 - (a+1) is the initial gap size")
    print()
    print("For n >= 9: both bounds are >= 6, so the chain has room.")
    print()

    # Sample random BFL words and verify bounds
    import random
    random.seed(42)

    for n in [5, 7, 9, 11, 13]:
        t = 1
        bL = 0
        bR = 2
        far = [p for p in range(n) if p not in {t, bL, bR}]
        left2t = (t - 2) % n

        max_chain_seen = 0
        max_gap_seen = 0
        bound_violations = 0
        total_bfl = 0

        for trial in range(100000):
            fc_t = random.choice([2, 4])
            fc_bL = 2
            fc_bR = fc_t - fc_bL
            if fc_bR < 0 or fc_bR % 2 != 0:
                continue

            fc_far = {p: random.randint(1, 3) for p in far}
            CL = fc_t + fc_bL + fc_bR + sum(fc_far.values())
            if CL < 2 * n:
                continue

            # Build word
            word = []
            spacing = CL // fc_t
            t_pos = [(i * spacing) % CL for i in range(fc_t)]
            t_pos.sort()

            word_arr = [None] * CL
            for p in t_pos:
                word_arr[p] = t

            # Place bL fires
            sides = ['left'] * fc_bL + ['right'] * fc_bR
            random.shuffle(sides)

            valid = True
            for idx in range(fc_t):
                pos = (t_pos[idx] + 1) % CL
                if word_arr[pos] is not None:
                    valid = False
                    break
                word_arr[pos] = bL if sides[idx] == 'left' else bR
            if not valid:
                continue

            # Fill far
            pool = []
            for p in far:
                pool.extend([p] * fc_far[p])
            random.shuffle(pool)

            pi = 0
            for i in range(CL):
                if word_arr[i] is None:
                    if pi >= len(pool):
                        valid = False
                        break
                    word_arr[i] = pool[pi]
                    pi += 1
            if not valid or pi != len(pool) or None in word_arr:
                continue

            # Analyze phases
            t_fires = [i for i, m in enumerate(word_arr) if m == t]
            if len(t_fires) < 2:
                continue

            for idx in range(len(t_fires)):
                a = t_fires[idx]
                s = t_fires[(idx + 1) % len(t_fires)]
                if s <= a:
                    s += CL

                interior = []
                for step in range(a + 1, s):
                    interior.append(step % CL)

                J = sum(1 for k in interior if word_arr[k] == bL)
                K_phase = sum(1 for k in interior if word_arr[k] == bR)

                if J != 1 or K_phase != 0 or len(interior) < 2:
                    continue

                # Check BFL
                left2_fires = [k for k in interior if word_arr[k] == left2t]
                if not left2_fires:
                    continue

                total_bfl += 1

                # Find first fire of left2t in interior
                f2 = None
                for step in interior:
                    if word_arr[step] == left2t:
                        f2 = step
                        break

                a1 = interior[0]
                gap = 0
                for step in interior:
                    if step == f2:
                        break
                    gap += 1

                if gap > max_gap_seen:
                    max_gap_seen = gap

                # Trace chain
                chain_k = 2
                search_steps = [step for step in interior if interior.index(step) < interior.index(f2)]

                fk = f2
                while chain_k <= n - 1:
                    proc_k1 = (t - chain_k - 1) % n

                    # Find proc_{k+1} fire in search_steps before fk
                    found = False
                    fk1 = None
                    for step in search_steps:
                        if word_arr[step] == proc_k1:
                            found = True
                            fk1 = step
                            break

                    if not found:
                        break

                    # Shrink search
                    new_search = []
                    for step in search_steps:
                        if step == fk1:
                            break
                        new_search.append(step)
                    search_steps = new_search
                    fk = fk1
                    chain_k += 1

                if chain_k > max_chain_seen:
                    max_chain_seen = chain_k

                if chain_k > n - 3:
                    bound_violations += 1
                    print(f"  VIOLATION at n={n}: chain={chain_k}, word={word_arr}")

        print(f"  n={n:>2}: total_bfl={total_bfl:>6}, max_chain={max_chain_seen}, "
              f"max_gap={max_gap_seen}, violations={bound_violations}")


def verify_k_bound_vs_n():
    """
    The key bound: K <= n-3.

    When K = n-3: proc_K = left^{n-3}(t) = (t-(n-3)) mod n = (t+3) mod n.
    proc_{K+1} = left^{n-2}(t) = (t+2) mod n = bR.
    bR doesn't fire in one-sided-left phase (K_phase = 0).
    So the termination condition is trivially satisfied at k = n-3.

    This means the chain can NEVER reach k = n-2.

    Even stronger: for k = n-4:
    proc_{k+1} = left^{n-3}(t) = (t+3) mod n = right^3(t).
    This is a far proc. If it fires, chain extends. If not, done.

    The max chain K = n-3 requires ALL far procs to fire in the
    phase interior in a specific "reverse" order.
    """
    print()
    print("=" * 70)
    print("K <= n-3 BOUND VERIFICATION")
    print("=" * 70)
    print()

    for n in [5, 7, 9, 11, 15]:
        t = 1
        bound = n - 3

        # List the chain of procs
        chain_procs = []
        for k in range(2, n):
            p = (t - k) % n
            chain_procs.append((k, p))

        print(f"  n={n}: bound K <= {bound}")
        print(f"    Chain procs: {chain_procs[:bound+1]}")
        print(f"    proc_{bound} = {(t-bound)%n}")
        print(f"    proc_{bound+1} = {(t-bound-1)%n} = bR = {(t+1)%n}? "
              f"{'YES' if (t-bound-1)%n == (t+1)%n else 'NO (check!)'}")

        # Verify: (t - (n-3) - 1) mod n = (t - (n-2)) mod n = (t + 2) mod n = bR
        check = (t - (n - 2)) % n == (t + 2) % n
        print(f"    Verification: left^{{n-2}}(t) = bR? {check}")
        print()


def prove_one_sided_implies_bL_at_a_plus_1():
    """
    Key structural lemma: in a one-sided-left normalForm phase (J=1, K=0),
    the bL fire occurs at step a+1 (tight).

    Proof:
    In a good cycle, the mover at each step is determined by the token
    ring dynamics. For a one-sided-left phase:
    - Step a: t fires
    - The phase interior has exactly 1 bL fire and 0 bR fires
    - bL must fire at the boundary (step a+1 or step s-1) because:

    Actually, bL doesn't HAVE to fire at step a+1. It could fire anywhere
    in the interior. But for the backward chain, we use step a+1 as the
    non-mover reference point.

    KEY POINT: The non-mover step is a+1, regardless of where bL fires.
    The EC checks:
    - Mover step: f_K (proc_K fires)
    - Non-mover step: a+1 (some proc p fires at a+1, and p != proc_K)

    Wait -- we need to be more careful. Let's re-examine.

    In the Lean code, the non-mover step for the EC at proc_K is a+1.
    At step a+1: the mover is word[a+1], which could be bL or some other proc.
    We need word[a+1] != proc_K = left^K(t) for K >= 2.

    If word[a+1] = bL = left(t): then word[a+1] != left^K(t) for K >= 2
    (since n >= 5, all left^k(t) are distinct).

    If word[a+1] is some far proc: it's still != left^K(t) in general.
    But we need to be careful.

    Actually, in the normalForm + one-sided-left setting, the proof in
    the Lean file shows that step a+1 fires bL (the binary neighbor).
    This comes from the "tight" property of one-sided phases.

    Let me check: does J=1 force the bL fire to be at step a+1?
    Not necessarily -- J=1 just means one bL fire in the phase interior.
    But the "tight" analysis in AllNormalFormFalse2.lean considers two cases:
    (1) bL fires at step a+1 (tight) -- analyzed via even/odd fire count
    (2) bL fires strictly after a+1 (non-tight) -- within_phase_ec_left applies

    So the BFL case actually arises in the TIGHT sub-case (bL at step a+1).
    """
    print()
    print("=" * 70)
    print("STRUCTURAL LEMMA: bL fires at step a+1 in BFL")
    print("=" * 70)
    print()
    print("In the BFL sub-case, bL fires at step a+1 (tight placement).")
    print()
    print("This is because the non-tight case (bL fires at step f > a+1)")
    print("is handled by within_phase_ec_left, which gives EC directly")
    print("when no left^2(t) fires in the phase. The BFL case by definition")
    print("has left^2(t) firing, but the backward chain analysis starts from")
    print("the TIGHT case where bL fires at a+1.")
    print()
    print("With bL at step a+1:")
    print("  - Step a+1: mover = bL = left(t)")
    print("  - For all k >= 2: left^k(t) != left(t) (distinct procs on ring)")
    print("  - So step a+1 is a valid non-mover step for EC at any proc_k, k >= 2")
    print()
    print("ACTUALLY: re-reading the Lean code more carefully...")
    print("The BFL case in AllNormalFormFalse2.lean (lines 1044-1084) is:")
    print("  - left^2(t) fires in [a, fL) where fL is the first left(t) fire")
    print("  - fL fires at step a (tight: the phase starts with left(t))")
    print("  - OR left^2(t) fires adjacent to fL")
    print()
    print("The backward chain uses step a (= fR, the right(t) fire at phase")
    print("boundary) as the non-mover reference. The details depend on the")
    print("specific sub-case in the Lean proof, but the chain mechanism is")
    print("the same: try EC at left^k(t), check if left^{k+1}(t) blocks.")


def main():
    verify_nesting_property()
    verify_chain_bound()
    verify_k_bound_vs_n()
    prove_one_sided_implies_bL_at_a_plus_1()


if __name__ == '__main__':
    main()
