#!/usr/bin/env python3
"""
Zero-Winding Palindromic EC Proof — PA exploration

Claim: In a zero-winding good cycle with cwStepCount > 0, fc(p) = 2 for all p,
CL = 2n, and >= 3 binary procs with n >= 9: hasEntryConflict.

Plan:
1. Enumerate ALL zero-winding mover words with fc=2 at small n (5, 7, 9).
2. Identify the palindromic structure (BAF arc) for each word.
3. For each, find the interior binary proc and the CW-nonmover / CCW-mover step pair.
4. Verify the fire-count parity argument (even fires -> value returns).
5. Prove analytically.
"""

from itertools import product as iproduct
from collections import Counter

def enumerate_zw_fc2_mover_words(n):
    """
    Enumerate all cyclic mover words of length 2n on ring Z_n where:
    - Each proc fires exactly twice (fc=2)
    - Zero winding: cwStepCount = ccwStepCount
    - cwStepCount > 0

    A mover word is w[0], w[1], ..., w[2n-1] where w[i] in {0,...,n-1}.
    Step direction: CW if w[i+1] = (w[i]+1)%n, CCW if w[i+1] = (w[i]-1)%n,
    stay if w[i+1] = w[i].

    Zero winding: sum of step directions = 0 (mod n considered as displacement).
    Actually, zero winding means total displacement = 0.
    """
    CL = 2 * n

    # We need to enumerate permutations of the mover word
    # Each proc appears exactly twice. The word is a closed walk on Z_n.
    # Step direction at position i: displacement = (w[i+1] - w[i]) mod n
    # But on a ring, displacement +1 = CW, -1 = CCW, 0 = stay
    # Zero winding: sum of displacements = 0 mod n (since it's a closed walk,
    # this is automatic: w[2n] = w[0] in cyclic sense)

    # Wait - for a GOOD CYCLE, the mover word is cyclic: w[2n] = w[0].
    # The total displacement is sum((w[i+1]-w[i]) mod n) over all i.
    # Since the walk is closed, total displacement = 0 mod n.
    # But "zero winding" means total displacement = 0 (not just mod n).
    # On a ring of size n, displacement at each step is in {-(n-1), ..., (n-1)}.
    # Canonical: +1 = CW, -1 = CCW, anything else = longer jump.

    # Actually for a token ring, at each step the mover fires and the next mover
    # is an adjacent proc. So displacement is +1, -1, or 0 (stay).
    # On the ring Z_n: right(p) = (p+1)%n, left(p) = (p-1)%n.

    # Step direction: if w[i+1] = right(w[i]) then CW (+1)
    #                 if w[i+1] = left(w[i]) then CCW (-1)
    #                 if w[i+1] = w[i] then stay (0)

    # Zero winding: #CW - #CCW = 0 (net displacement = 0).
    # cwStepCount = #CW steps, ccwStepCount = #CCW steps.
    # Zero winding with cwStepCount > 0 means #CW = #CCW > 0.

    # Total steps = 2n. #CW + #CCW + #stay = 2n.
    # Zero winding: #CW = #CCW. So #stay = 2n - 2*(#CW).

    # With fc=2, each proc fires exactly twice. The mover word is a multiset
    # permutation of {0,0,1,1,...,(n-1),(n-1)}.

    results = []

    # For small n, brute-force enumerate via recursive walk generation
    def generate_walks(pos, word, fc_count, cw_count, ccw_count):
        if pos == CL:
            # Check closure: the walk is cyclic
            # Last step goes from word[-1] to word[0]
            last_to_first = (word[0] - word[-1]) % n
            if last_to_first == 1:
                cw_final = cw_count + 1
                ccw_final = ccw_count
            elif last_to_first == n - 1:
                cw_final = cw_count
                ccw_final = ccw_count + 1
            elif last_to_first == 0:
                cw_final = cw_count
                ccw_final = ccw_count
            else:
                return  # Invalid step

            if cw_final == ccw_final and cw_final > 0:
                results.append(tuple(word))
            return

        for p in range(n):
            if fc_count[p] >= 2:
                continue

            if pos > 0:
                disp = (p - word[-1]) % n
                if disp == 1:
                    new_cw = cw_count + 1
                    new_ccw = ccw_count
                elif disp == n - 1:
                    new_cw = cw_count
                    new_ccw = ccw_count + 1
                elif disp == 0:
                    new_cw = cw_count
                    new_ccw = ccw_count
                else:
                    continue  # Not adjacent step
            else:
                new_cw = cw_count
                new_ccw = ccw_count

            fc_count[p] += 1
            word.append(p)
            generate_walks(pos + 1, word, fc_count, new_cw, new_ccw)
            word.pop()
            fc_count[p] -= 1

    fc_count = [0] * n
    generate_walks(0, [], fc_count, 0, 0)
    return results


def classify_word(word, n):
    """Classify a mover word: step directions, CW/CCW counts, winding."""
    CL = len(word)
    steps = []
    cw = 0
    ccw = 0
    stay = 0
    for i in range(CL):
        nxt = word[(i + 1) % CL]
        cur = word[i]
        disp = (nxt - cur) % n
        if disp == 1:
            steps.append(+1)
            cw += 1
        elif disp == n - 1:
            steps.append(-1)
            ccw += 1
        elif disp == 0:
            steps.append(0)
            stay += 1
        else:
            steps.append(None)
    return steps, cw, ccw, stay


def find_baf_arc(word, n, binary_procs):
    """
    Find a BAF (back-and-forth) arc in the mover word.

    A BAF arc for processor b has:
    1. CW step where b fires (cwProcStep)
    2. CW step where right(b) fires (cwNeighborStep) -- b is non-mover
    3. CCW step where right(b) fires (ccwNeighborStep)
    4. CCW step where b fires (ccwProcStep) -- b is mover

    Between steps 2 and 4: b doesn't fire, left(b) doesn't fire.
    Between steps 2 and 3: right(b) doesn't fire.
    """
    CL = len(word)
    steps, _, _, _ = classify_word(word, n)

    # For each binary proc b, find its two firing positions
    for b in binary_procs:
        rb = (b + 1) % n  # right(b)
        lb = (b - 1) % n  # left(b)

        # Find positions where b fires
        b_fires = [i for i in range(CL) if word[i] == b]
        if len(b_fires) != 2:
            continue

        # Find positions where right(b) fires
        rb_fires = [i for i in range(CL) if word[i] == rb]
        if len(rb_fires) != 2:
            continue

        # Try to find a BAF arc pattern:
        # We need: cwProcStep (b fires, CW direction)
        #          cwNeighborStep (rb fires, CW direction) after cwProcStep
        #          ccwNeighborStep (rb fires, CCW direction) after cwNeighborStep
        #          ccwProcStep (b fires, CCW direction) after ccwNeighborStep

        # Check all orderings
        for bf1 in b_fires:
            for bf2 in b_fires:
                if bf1 == bf2:
                    continue
                for rbf1 in rb_fires:
                    for rbf2 in rb_fires:
                        if rbf1 == rbf2:
                            continue

                        # Check temporal ordering (linear, not cyclic for now)
                        # cwProcStep = bf1, cwNeighborStep = rbf1
                        # ccwNeighborStep = rbf2, ccwProcStep = bf2
                        if not (bf1 < rbf1 < rbf2 < bf2):
                            continue

                        # Check directions
                        if steps[bf1] != +1:  # CW
                            continue
                        if steps[rbf1] != +1:  # CW
                            continue
                        if steps[rbf2] != -1:  # CCW
                            continue
                        if steps[bf2] != -1:  # CCW
                            continue

                        # Check no b fires between rbf1 and bf2
                        b_between = any(word[i] == b for i in range(rbf1, bf2))
                        if b_between:
                            continue

                        # Check no left(b) fires between rbf1 and bf2
                        lb_between = any(word[i] == lb for i in range(rbf1, bf2))
                        if lb_between:
                            continue

                        # Check no right(b) fires between rbf1+1 and rbf2
                        rb_between = any(word[i] == rb for i in range(rbf1 + 1, rbf2))
                        if rb_between:
                            continue

                        # Check adjacency: ccwProcStep = ccwNeighborStep + 1
                        adj = (bf2 == rbf2 + 1)

                        return {
                            'proc': b,
                            'left': lb,
                            'right': rb,
                            'cwProcStep': bf1,
                            'cwNeighborStep': rbf1,
                            'ccwNeighborStep': rbf2,
                            'ccwProcStep': bf2,
                            'adjacent': adj,
                            'word': word,
                        }
    return None


def analyze_fire_counts_between(word, n, arc):
    """
    Analyze fire counts of relevant procs between the key steps.

    For EC at proc b:
    - Between cwNeighborStep and ccwProcStep:
      * b fires 0 times (value preserved)
      * left(b) fires 0 times (value preserved)
    - right(b): fires some number of times between cwNeighborStep and ccwProcStep
      If right(b) is binary: fires 0 or 2 times -> even -> value returns
      If right(b) is ternary: fires 0 or 3 times -> value returns
    """
    b = arc['proc']
    lb = arc['left']
    rb = arc['right']
    cw_nb = arc['cwNeighborStep']
    ccw_proc = arc['ccwProcStep']

    # Count fires of each proc between cwNeighborStep (exclusive) and ccwProcStep (exclusive)
    # Actually: between cwNeighborStep and ccwProcStep means
    # steps cw_nb, cw_nb+1, ..., ccw_proc-1 for the "between" region
    # But the BAF arc says: between cwNeighborStep and ccwProcStep,
    # b and left(b) don't fire. And the values at cwNeighborStep are compared
    # to values at ccwProcStep.

    fire_counts = Counter()
    for i in range(cw_nb + 1, ccw_proc):
        fire_counts[word[i]] += 1

    # Also count: right(b) fires between cwNeighborStep+1 and ccwNeighborStep
    # (which is the "mid" region where rb doesn't fire)
    ccw_nb = arc['ccwNeighborStep']
    rb_fires_total = sum(1 for i in range(cw_nb + 1, ccw_proc) if word[i] == rb)

    return {
        'b_fires': fire_counts.get(b, 0),
        'lb_fires': fire_counts.get(lb, 0),
        'rb_fires': rb_fires_total,
        'all_fires': dict(fire_counts),
        'interval': (cw_nb + 1, ccw_proc),
    }


def find_any_ec_pair(word, n, binary_procs):
    """
    For each binary proc b, find ANY pair of steps where b sees the same
    context as mover and non-mover.

    This is the most general search: for each b, find step i (b is non-mover)
    and step j (b is mover) with same (L, S, R) context.

    We use symbolic tracking: given binary placement, track which procs fire
    between any two steps.
    """
    CL = len(word)
    steps, _, _, _ = classify_word(word, n)

    for b in binary_procs:
        # Steps where b is mover
        mover_steps = [i for i in range(CL) if word[i] == b]
        # Steps where b is non-mover (all other steps)
        nonmover_steps = [i for i in range(CL) if word[i] != b]

        # For each pair (mover_step, nonmover_step), check fire count parities
        # between the two steps for left(b), b, right(b)
        lb = (b - 1) % n
        rb = (b + 1) % n

        for ms in mover_steps:
            for nms in nonmover_steps:
                # We want: val(lb, ms) = val(lb, nms), val(b, ms) = val(b, nms),
                #          val(rb, ms) = val(rb, nms)
                #
                # For a proc p with state size m_p:
                # val(p) changes when p fires. After k fires, val(p) = initial + k (mod m_p).
                # So val(p, step_a) = val(p, step_b) iff fire_count(p, a..b) = 0 mod m_p.
                #
                # Between step nms and step ms (going forward cyclically):
                # Count fires of lb, b, rb.
                # If all are 0 mod their respective state sizes -> EC.

                # Count fires from nms to ms (exclusive of nms, inclusive of ms?
                # Actually we need config equality. Config at step i is the config
                # BEFORE step i fires. So config(ms) is the config when b is about to fire.
                # Config(nms) is the config when some other proc is about to fire.
                # Between config(nms) and config(ms), the procs that fire are
                # word[nms], word[nms+1], ..., word[ms-1].

                if ms > nms:
                    interval = range(nms, ms)
                else:
                    interval = list(range(nms, CL)) + list(range(0, ms))

                fires = Counter(word[i] for i in interval)

                # For b: b fires fires.get(b, 0) times between these steps
                # For config equality: need fire_count = 0 mod m_p
                # Here we check with ALL binary for now (m_p = 2)
                b_fires = fires.get(b, 0)
                lb_fires = fires.get(lb, 0)
                rb_fires = fires.get(rb, 0)

                yield b, ms, nms, b_fires, lb_fires, rb_fires


def main():
    print("=" * 70)
    print("ZERO-WINDING FC=2 MOVER WORD ANALYSIS")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'=' * 60}")
        print(f"n = {n}, CL = {2*n}")
        print(f"{'=' * 60}")

        words = enumerate_zw_fc2_mover_words(n)
        print(f"Total zero-winding fc=2 mover words: {len(words)}")

        # Remove cyclic rotations to count distinct words
        canonical = set()
        for w in words:
            rotations = [tuple(w[i:] + w[:i]) for i in range(len(w))]
            canonical.add(min(rotations))
        print(f"Distinct (up to rotation): {len(canonical)}")

        # Analyze structure
        binary_procs = [0, 1, 2]  # 3 consecutive binary

        baf_found = 0
        baf_not_found = 0
        ec_found = 0
        ec_not_found = 0

        for w in canonical:
            steps, cw, ccw, stay = classify_word(w, n)

            # Check for BAF arc
            arc = find_baf_arc(w, n, binary_procs)
            if arc:
                baf_found += 1
            else:
                baf_not_found += 1

            # Check for ANY EC pair (with all procs binary for simplicity)
            found_ec = False
            for b, ms, nms, bf, lbf, rbf in find_any_ec_pair(w, n, binary_procs):
                # For binary: need bf % 2 == 0, lbf % 2 == 0, rbf % 2 == 0
                if bf % 2 == 0 and lbf % 2 == 0 and rbf % 2 == 0:
                    found_ec = True
                    break

            if found_ec:
                ec_found += 1
            else:
                ec_not_found += 1

        print(f"\nBAF arc found: {baf_found}/{len(canonical)}")
        print(f"BAF arc not found: {baf_not_found}/{len(canonical)}")
        print(f"EC found (any pair, all binary): {ec_found}/{len(canonical)}")
        print(f"EC not found: {ec_not_found}/{len(canonical)}")

        # Detailed analysis of first few words
        print(f"\n--- Detailed analysis (first 5 words) ---")
        for idx, w in enumerate(sorted(canonical)[:5]):
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)
            print(f"\nWord {idx}: {w}")
            print(f"  Steps: {step_str} (CW={cw}, CCW={ccw}, Stay={stay})")

            arc = find_baf_arc(w, n, binary_procs)
            if arc:
                print(f"  BAF arc at proc {arc['proc']}:")
                print(f"    cwProcStep={arc['cwProcStep']}, cwNeighborStep={arc['cwNeighborStep']}")
                print(f"    ccwNeighborStep={arc['ccwNeighborStep']}, ccwProcStep={arc['ccwProcStep']}")
                print(f"    Adjacent: {arc['adjacent']}")

                fc = analyze_fire_counts_between(w, n, arc)
                print(f"    Between cwNeighborStep and ccwProcStep:")
                print(f"      b fires: {fc['b_fires']}")
                print(f"      left(b) fires: {fc['lb_fires']}")
                print(f"      right(b) fires: {fc['rb_fires']}")
                print(f"      All fires: {fc['all_fires']}")

            # Show all EC pairs
            ec_pairs = []
            for b, ms, nms, bf, lbf, rbf in find_any_ec_pair(w, n, binary_procs):
                if bf % 2 == 0 and lbf % 2 == 0 and rbf % 2 == 0:
                    ec_pairs.append((b, ms, nms, bf, lbf, rbf))
            if ec_pairs:
                print(f"  EC pairs (first 3):")
                for b, ms, nms, bf, lbf, rbf in ec_pairs[:3]:
                    print(f"    proc={b}: mover_step={ms}, nonmover_step={nms}, "
                          f"b_fires={bf}, lb_fires={lbf}, rb_fires={rbf}")

    # Now the deeper structural analysis
    print(f"\n\n{'=' * 70}")
    print("STRUCTURAL ANALYSIS: PALINDROMIC WALK ORDERING")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n--- n = {n} ---")
        if n <= 7:
            words = enumerate_zw_fc2_mover_words(n)
            canonical = set()
            for w in words:
                rotations = [tuple(w[i:] + w[:i]) for i in range(len(w))]
                canonical.add(min(rotations))
        else:
            # For n=9, enumerate might be slow. Use structural generation.
            canonical = set()
            # Generate BAF words: CW from 0 to k, then CCW from k back to 0
            # (and closing the cycle)
            # A BAF word with turnaround at position k:
            # 0, 1, 2, ..., k, k-1, k-2, ..., 1, 0 (but need to close and have fc=2)

            # Actually for fc=2 zero-winding: the walk visits each proc exactly twice.
            # The canonical BAF structure: go CW from proc a to proc a+d,
            # then CCW back from a+d to a. This visits exactly d+1 procs.
            # For all n procs with fc=2: need CL = 2n.
            # A single BAF arc covers 2d+1 steps (d CW + d CCW + turnaround).
            # But we need ALL n procs to fire twice.

            # The simplest structure: go CW through all n procs, then CCW back.
            # 0, 1, 2, ..., n-1, n-2, n-3, ..., 1
            # This has CW steps 0->1->...->n-1 (n-1 CW) and CCW steps n-1->n-2->...->1 (n-2 CCW).
            # Not balanced! CW = n-1, CCW = n-2.

            # Need: CW = CCW. And each proc fires twice.
            # Let's try a different approach: generate structured BAF words.

            # For the canonical BAF: start at 0, go CW to some turnaround point T,
            # go CCW back past 0 to some point -S (= n-S mod n), then CW back to 0.
            # This gives: CW = T + S steps, CCW = T + S steps. Total = 2(T+S) steps.
            # Need 2(T+S) = 2n, so T + S = n.
            # Procs visited: 0..T (CW), T..0 (CCW), 0..(n-S)=(n-T) (wait, this doesn't work)

            # Actually, for the palindromic fc=2 structure, the walk goes:
            # Phase 1 (CW): 0, 1, 2, ..., T  (T+1 procs, T CW steps)
            # Phase 2 (CCW): T, T-1, ..., 0, n-1, n-2, ..., T+1  (n CCW steps)
            # Phase 3 (CW): T+1, T+2, ..., n-1, 0  (n-T-1 CW steps)
            # Wait, this gets complicated. Let me just skip n=9 enumeration.
            print("  [Skipping full enumeration for n=9, using structural analysis]")
            continue

        # For each word, analyze the palindromic structure
        all_have_ec = True
        no_ec_words = []

        binary_procs = [0, 1, 2]

        for w in canonical:
            found_ec = False
            for b, ms, nms, bf, lbf, rbf in find_any_ec_pair(w, n, binary_procs):
                if bf % 2 == 0 and lbf % 2 == 0 and rbf % 2 == 0:
                    found_ec = True
                    break

            if not found_ec:
                all_have_ec = False
                no_ec_words.append(w)

        print(f"  All words have EC (all-binary): {all_have_ec}")
        print(f"  Words without EC: {len(no_ec_words)}")

        if no_ec_words:
            print(f"  First no-EC word: {no_ec_words[0]}")
            w = no_ec_words[0]
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)
            print(f"    Steps: {step_str}")

            # Show all pairs and their fire counts
            print(f"    All EC candidate pairs for proc 0,1,2:")
            for b in binary_procs:
                mover_steps = [i for i in range(len(w)) if w[i] == b]
                for ms in mover_steps:
                    for nms in range(len(w)):
                        if w[nms] == b:
                            continue
                        if ms > nms:
                            interval = range(nms, ms)
                        else:
                            interval = list(range(nms, len(w))) + list(range(0, ms))
                        fires = Counter(w[i] for i in interval)
                        bf = fires.get(b, 0)
                        lbf = fires.get((b-1)%n, 0)
                        rbf = fires.get((b+1)%n, 0)
                        if bf % 2 != 0 or lbf % 2 != 0 or rbf % 2 != 0:
                            continue
                        print(f"      proc={b}, ms={ms}, nms={nms}: b={bf}, lb={lbf}, rb={rbf}")

    # Now: the REAL test with mixed state sizes (3 binary, rest ternary)
    print(f"\n\n{'=' * 70}")
    print("MIXED STATE TEST: 3 binary + (n-3) ternary")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        words = enumerate_zw_fc2_mover_words(n)
        canonical = set()
        for w in words:
            rotations = [tuple(w[i:] + w[:i]) for i in range(len(w))]
            canonical.add(min(rotations))

        binary_procs = [0, 1, 2]
        ternary_procs = list(range(3, n))

        all_have_ec = True
        no_ec_count = 0

        for w in canonical:
            found_ec = False

            for b, ms, nms, bf, lbf, rbf in find_any_ec_pair(w, n, binary_procs):
                lb = (b - 1) % n
                rb = (b + 1) % n

                # For binary procs: need fire count even (mod 2)
                # For ternary procs: need fire count divisible by 3 (mod 3)
                b_ok = (bf % 2 == 0)  # b is binary

                lb_mod = 2 if lb in binary_procs else 3
                lb_ok = (lbf % lb_mod == 0)

                rb_mod = 2 if rb in binary_procs else 3
                rb_ok = (rbf % rb_mod == 0)

                if b_ok and lb_ok and rb_ok:
                    found_ec = True
                    break

            if not found_ec:
                all_have_ec = False
                no_ec_count += 1

        print(f"  All words have EC (binary 0,1,2; ternary rest): {all_have_ec}")
        print(f"  Words without EC: {no_ec_count}/{len(canonical)}")


if __name__ == '__main__':
    main()
