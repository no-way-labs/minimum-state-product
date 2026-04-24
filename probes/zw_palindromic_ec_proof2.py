#!/usr/bin/env python3
"""
Zero-Winding Palindromic EC Proof — Phase 2

Key finding from Phase 1: exactly ONE mover word at each n lacks EC
when only checking binary procs {0,1,2}: the "full traverse" word.

This word has structure: 0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1
Step directions: R, L, L, L, ..., L, R, R, ..., R (one CW, n-1 CCW, one turnaround, n-1 CW)

Deeper analysis:
1. Is this word actually valid for our setting? (3+ binary, n >= 9)
2. Does it have EC at NON-binary procs?
3. What's the actual palindromic structure?
"""

from collections import Counter

def classify_word(word, n):
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


def full_traverse_word(n):
    """The problematic word: 0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1"""
    word = [0, 1, 0]
    for p in range(n-1, 1, -1):  # n-1, n-2, ..., 2
        word.append(p)
    for p in range(1, n):  # 1, 2, ..., n-1
        word.append(p)
    return tuple(word)


def analyze_ec_all_procs(word, n, state_sizes):
    """
    Check EC at ALL processors, not just binary ones.
    state_sizes[p] = m_p (2 for binary, 3 for ternary).
    """
    CL = len(word)
    ec_pairs = []

    for b in range(n):
        lb = (b - 1) % n
        rb = (b + 1) % n

        mover_steps = [i for i in range(CL) if word[i] == b]
        nonmover_steps = [i for i in range(CL) if word[i] != b]

        for ms in mover_steps:
            for nms in nonmover_steps:
                if ms > nms:
                    interval = range(nms, ms)
                else:
                    interval = list(range(nms, CL)) + list(range(0, ms))

                fires = Counter(word[i] for i in interval)
                bf = fires.get(b, 0)
                lbf = fires.get(lb, 0)
                rbf = fires.get(rb, 0)

                # Need fire counts to be 0 mod state_size
                if bf % state_sizes[b] == 0 and \
                   lbf % state_sizes[lb] == 0 and \
                   rbf % state_sizes[rb] == 0:
                    ec_pairs.append((b, ms, nms, bf, lbf, rbf))

    return ec_pairs


def main():
    print("=" * 70)
    print("FULL-TRAVERSE WORD ANALYSIS")
    print("=" * 70)

    for n in [5, 7, 9, 11]:
        w = full_traverse_word(n)
        assert len(w) == 2*n, f"Length {len(w)} != {2*n}"
        assert all(Counter(w)[p] == 2 for p in range(n)), "Not fc=2"

        steps, cw, ccw, stay = classify_word(w, n)
        assert cw == ccw and cw > 0, "Not zero-winding"
        step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)

        print(f"\n--- n = {n} ---")
        print(f"Word: {w}")
        print(f"Steps: {step_str} (CW={cw}, CCW={ccw})")

        # Test with 3 consecutive binary at {0,1,2}, rest ternary
        state_sizes = [2 if p < 3 else 3 for p in range(n)]
        ec_pairs = analyze_ec_all_procs(w, n, state_sizes)
        print(f"EC pairs (consec binary {0,1,2}, ternary rest): {len(ec_pairs)}")
        for b, ms, nms, bf, lbf, rbf in ec_pairs[:5]:
            print(f"  proc={b} (m={state_sizes[b]}), ms={ms}, nms={nms}: "
                  f"b_fires={bf}(mod {state_sizes[b]}), "
                  f"lb_fires={lbf}(mod {state_sizes[(b-1)%n]}), "
                  f"rb_fires={rbf}(mod {state_sizes[(b+1)%n]})")

        # Test with 3 NON-consecutive binary
        # Binary at {0, 3, 6} for n >= 7, or {0, 2, 4} for n=5
        if n == 5:
            bin_pos = [0, 2, 4]
        else:
            bin_pos = [0, n//3, 2*(n//3)]
        state_sizes2 = [2 if p in bin_pos else 3 for p in range(n)]
        ec_pairs2 = analyze_ec_all_procs(w, n, state_sizes2)
        print(f"EC pairs (non-consec binary {bin_pos}, ternary rest): {len(ec_pairs2)}")
        for b, ms, nms, bf, lbf, rbf in ec_pairs2[:5]:
            print(f"  proc={b} (m={state_sizes2[b]}), ms={ms}, nms={nms}: "
                  f"b_fires={bf}(mod {state_sizes2[b]}), "
                  f"lb_fires={lbf}(mod {state_sizes2[(b-1)%n]}), "
                  f"rb_fires={rbf}(mod {state_sizes2[(b+1)%n]})")

    # CRITICAL: Now check all words, not just full-traverse
    print("\n\n" + "=" * 70)
    print("COMPREHENSIVE EC CHECK: ALL PROCS (not just binary)")
    print("=" * 70)

    from itertools import product as iproduct

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")

        # Enumerate all ZW fc=2 words
        CL = 2 * n
        results = []
        def generate_walks(pos, word, fc_count, cw_count, ccw_count):
            if pos == CL:
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
                    return
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
                        continue
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
        canonical = set()
        for w in results:
            rotations = [tuple(w[i:] + w[:i]) for i in range(len(w))]
            canonical.add(min(rotations))

        print(f"Distinct ZW fc=2 words: {len(canonical)}")

        # 3 consecutive binary at {0,1,2}
        state_sizes = [2 if p < 3 else 3 for p in range(n)]
        all_ec = True
        no_ec_words = []

        for w in sorted(canonical):
            ec_pairs = analyze_ec_all_procs(w, n, state_sizes)
            if not ec_pairs:
                all_ec = False
                no_ec_words.append(w)

        print(f"All have EC (checking all procs): {all_ec}")
        print(f"No-EC words: {len(no_ec_words)}")

        if no_ec_words:
            for w in no_ec_words:
                steps, cw, ccw, stay = classify_word(w, n)
                step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)
                print(f"  Word: {w}, Steps: {step_str}")

                # Detailed fire count analysis
                print(f"  Fire count analysis at each proc (from step 0 to step {2*n-1}):")
                for b in range(n):
                    mover_steps = [i for i in range(len(w)) if w[i] == b]
                    print(f"    proc {b} (m={state_sizes[b]}): fires at steps {mover_steps}")

                # Show ALL pairs with their fire count mod residues
                print(f"  All (mover, nonmover) pairs with residues:")
                for b in range(n):
                    lb = (b - 1) % n
                    rb = (b + 1) % n
                    for ms in [i for i in range(len(w)) if w[i] == b]:
                        best_miss = None
                        for nms in [i for i in range(len(w)) if w[i] != b]:
                            if ms > nms:
                                interval = range(nms, ms)
                            else:
                                interval = list(range(nms, len(w))) + list(range(0, ms))
                            fires = Counter(w[i] for i in interval)
                            bf = fires.get(b, 0)
                            lbf = fires.get(lb, 0)
                            rbf = fires.get(rb, 0)
                            resid = (bf % state_sizes[b],
                                     lbf % state_sizes[lb],
                                     rbf % state_sizes[rb])
                            if resid == (0, 0, 0):
                                print(f"    proc={b}, ms={ms}, nms={nms}: "
                                      f"residues=(0,0,0) -- EC!")

    # Now the key structural question
    print("\n\n" + "=" * 70)
    print("KEY STRUCTURAL ANALYSIS: BAF ARC SELECTION")
    print("=" * 70)

    print("""
The palindromic EC argument needs:
1. A BAF arc: CW pass followed by CCW return
2. An interior proc b where:
   - Between CW-nonmover step and CCW-mover step:
     * b fires 0 times (preserves self value)
     * left(b) fires 0 mod m_L times (preserves left value)
     * right(b) fires 0 mod m_R times (preserves right value)

For the BAF arc structure:
- CW pass: ..., b, right(b), ... (b fires, then right(b) fires)
- CCW pass: ..., right(b), b, ... (right(b) fires, then b fires)

Between cwNeighborStep (right(b) fires CW) and ccwProcStep (b fires CCW):
- b doesn't fire (it fires BEFORE cwNeighborStep and AT ccwProcStep)
- left(b) doesn't fire (it fires BEFORE b in the CW pass, and after b in CCW)
- right(b) fires exactly once in between (at ccwNeighborStep)

Wait -- right(b) fires once! For binary right(b), 1 mod 2 = 1 != 0.
That's why the BAF arc with adjacent CCW doesn't directly give EC.

The fix: right(b) fires at BOTH cwNeighborStep (CW) and ccwNeighborStep (CCW).
Between these two firings, right(b) fires 0 more times.
So from config at cwNeighborStep+1 to config at ccwNeighborStep, right(b)'s
value is the SAME.

But the comparison is between config at cwNeighborStep (before right(b) fires CW)
and config at ccwProcStep (before b fires CCW, AFTER right(b) fires CCW).

So right(b)'s value at cwNeighborStep vs ccwProcStep:
- At cwNeighborStep: right(b) hasn't fired yet (at this step it's about to fire)
- At ccwProcStep: right(b) has fired twice (once CW at cwNeighborStep, once CCW
  at ccwNeighborStep)

For binary right(b): 2 fires mod 2 = 0. VALUE RETURNS!

Wait, but the analysis showed right(b) fires 1 time BETWEEN cwNeighborStep
and ccwProcStep. That's because cwNeighborStep is when right(b) fires CW,
so between cwNeighborStep and ccwProcStep, right(b) fires at ccwNeighborStep
(once more).

The config at cwNeighborStep is the config BEFORE right(b) fires at that step.
The config at ccwProcStep is the config BEFORE b fires at that step.

Between these configs, right(b) fires at:
- cwNeighborStep (CW fire)
- ccwNeighborStep (CCW fire)
That's 2 fires of right(b).

No wait, I'm counting wrong. The interval [cwNeighborStep, ccwProcStep) for
the mover word is: right(b) fires at cwNeighborStep and ccwNeighborStep.
But "between step a and step b" means steps a, a+1, ..., b-1.

Config at step a = config BEFORE step a fires.
Config at step b = config BEFORE step b fires.
Changes between config(a) and config(b) come from steps a, a+1, ..., b-1.

So right(b) fires at step cwNeighborStep (included) and ccwNeighborStep
(included if < ccwProcStep). That's 2 fires total.

For binary: 2 mod 2 = 0. R-value returns!

Let me verify this computationally.
""")

    for n in [5, 7, 9]:
        if n > 7:
            print(f"\nn = {n}: using structural word")
            # Just use the canonical BAF word: 0, 0, 1, 2, ..., n-1, n-1, n-2, ..., 1
            w = tuple([0, 0] + list(range(1, n)) + list(range(n-1, 0, -1)))
        else:
            print(f"\nn = {n}: using canonical BAF word")
            w = tuple([0, 0] + list(range(1, n)) + list(range(n-1, 0, -1)))

        assert len(w) == 2*n
        assert all(Counter(w)[p] == 2 for p in range(n))

        steps, cw, ccw, stay = classify_word(w, n)
        step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)
        print(f"Word: {w}")
        print(f"Steps: {step_str}")

        # The canonical BAF: 0,0,1,2,...,n-1,n-1,n-2,...,1
        # Structure: stay at 0, CW to n-1, stay at n-1, CCW back to 1
        # CW steps: 0->1, 1->2, ..., n-2->n-1 = n-1 steps
        # CCW steps: n-1->n-2, ..., 2->1 = n-2 steps
        # Stay: 0->0, n-1->n-1 = 2 stays
        # CW-CCW = (n-1) - (n-2) = 1 != 0  NOT zero winding!

        print(f"CW={cw}, CCW={ccw} -- {'ZW' if cw==ccw else 'NOT ZW'}")

        # Fix: for ZW we need CW = CCW.
        # Better canonical: the bounce word 0,1,2,...,k,k-1,...,1,0,n-1,...,k+1,k+2,...,n-1
        # with turnaround at k and n-k positions.

    # Let me reconsider the BAF structure.
    print("\n\n" + "=" * 70)
    print("REVISED: CANONICAL BAF WORD STRUCTURE FOR ZW")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n--- n = {n} ---")

        # A zero-winding BAF with fc=2 must have CW = CCW.
        # The walk visits each proc twice and returns to start.
        # Canonical: go CW from 0 to T, then CCW from T past 0 to n-T, then CW back.
        # CW steps: T + T = 2T. CCW steps: T + (n - 2T) = n - T.
        # For ZW: 2T = n - T => T = n/3. Only works if n divisible by 3.

        # General structure: the walk is a closed path on Z_n, visiting each vertex twice.
        # With CW = CCW = k and stay = 2n - 2k.

        # The simplest ZW fc=2 word structure:
        # Two arcs, each going one direction and coming back.
        # Arc 1: go CW d steps, then CCW d steps (visits d+1 procs, 2d steps)
        # Arc 2: go CCW e steps, then CW e steps (visits e+1 procs, 2e steps)
        # For all n procs: d + e + 1 = n (with overlap at start).
        # Wait, this doesn't work simply.

        # The REAL structure (from the enumeration):
        # Looking at n=5, the 10 distinct words and their step patterns:
        # Most common: stay-CW-...-CCW-...- pattern (BAF with turnaround at proc 0)
        #
        # Observation: ALL ZW fc=2 words are "palindromic" in the sense that
        # they have a CW phase and a CCW phase of equal length.

        # Let me just enumerate and show the structure for small n
        if n <= 7:
            CL = 2 * n
            results = []
            def generate_walks(pos, word, fc_count, cw_count, ccw_count):
                if pos == CL:
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
                        return
                    if cw_final == ccw_final and cw_final > 0:
                        results.append(tuple(word))
                    return
                for p in range(n):
                    if fc_count[p] >= 2:
                        continue
                    if pos > 0:
                        disp = (p - word[-1]) % n
                        if disp not in (0, 1, n-1):
                            continue
                        if disp == 1:
                            new_cw = cw_count + 1
                            new_ccw = ccw_count
                        elif disp == n - 1:
                            new_cw = cw_count
                            new_ccw = ccw_count + 1
                        else:
                            new_cw = cw_count
                            new_ccw = ccw_count
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
            canonical = set()
            for w in results:
                rotations = [tuple(w[i:] + w[:i]) for i in range(len(w))]
                canonical.add(min(rotations))

            # Classify by reversal structure
            for w in sorted(canonical):
                steps, cw, ccw, stay = classify_word(w, n)
                step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)

                # Find reversals
                reversals = []
                for i in range(len(steps)):
                    d1 = steps[i]
                    d2 = steps[(i+1) % len(steps)]
                    if (d1 == 1 and d2 == -1) or (d1 == -1 and d2 == 1):
                        reversals.append(i)

                print(f"  {w}  {step_str}  rev={reversals}  CW={cw} CCW={ccw} S={stay}")


    # THE REAL TEST: BAF arc with correct R-value counting
    print("\n\n" + "=" * 70)
    print("CORRECT R-VALUE ANALYSIS IN BAF ARCS")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")

        CL = 2 * n
        results = []
        def generate_walks(pos, word, fc_count, cw_count, ccw_count):
            if pos == CL:
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
                    return
                if cw_final == ccw_final and cw_final > 0:
                    results.append(tuple(word))
                return
            for p in range(n):
                if fc_count[p] >= 2:
                    continue
                if pos > 0:
                    disp = (p - word[-1]) % n
                    if disp not in (0, 1, n-1):
                        continue
                    if disp == 1:
                        new_cw = cw_count + 1
                        new_ccw = ccw_count
                    elif disp == n - 1:
                        new_cw = cw_count
                        new_ccw = ccw_count + 1
                    else:
                        new_cw = cw_count
                        new_ccw = ccw_count
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
        canonical = set()
        for w in results:
            rotations = [tuple(w[i:] + w[:i]) for i in range(len(w))]
            canonical.add(min(rotations))

        # For each word, find a BAF arc and check the R-value fire count carefully
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        for w in sorted(canonical):
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)

            # For each proc b (binary), and each pair of b-firing steps:
            # Find the pair where b fires CW then CCW (or vice versa), forming a BAF arc.
            for b in range(3):  # Binary procs
                rb = (b + 1) % n
                lb = (b - 1) % n

                b_fires = [i for i in range(len(w)) if w[i] == b]
                if len(b_fires) != 2:
                    continue

                bf0, bf1 = b_fires

                # Check if b fires CW at bf0 and CCW at bf1 (or vice versa)
                # Direction of b's firing:
                d0 = steps[bf0]
                d1 = steps[bf1]

                if d0 == 1 and d1 == -1:
                    cw_step = bf0
                    ccw_step = bf1
                elif d0 == -1 and d1 == 1:
                    cw_step = bf1
                    ccw_step = bf0
                else:
                    continue  # Not a CW/CCW pair

                # Between cw_step and ccw_step: how many times does rb fire?
                # Config at cw_step vs config at ccw_step
                if ccw_step > cw_step:
                    interval = range(cw_step, ccw_step)
                else:
                    interval = list(range(cw_step, len(w))) + list(range(0, ccw_step))

                fires = Counter(w[i] for i in interval)
                b_fire_between = fires.get(b, 0)
                lb_fire_between = fires.get(lb, 0)
                rb_fire_between = fires.get(rb, 0)

                # Between ccw_step and next cw_step (wrapping):
                if cw_step > ccw_step:
                    interval2 = range(ccw_step, cw_step)
                else:
                    interval2 = list(range(ccw_step, len(w))) + list(range(0, cw_step))
                fires2 = Counter(w[i] for i in interval2)

                print(f"  Word={w}, proc b={b}: CW@{cw_step}, CCW@{ccw_step}")
                print(f"    Between CW and CCW: b={b_fire_between}, lb={lb_fire_between}, rb={rb_fire_between}")
                print(f"    Residues: b%{state_sizes[b]}={b_fire_between%state_sizes[b]}, "
                      f"lb%{state_sizes[lb]}={lb_fire_between%state_sizes[lb]}, "
                      f"rb%{state_sizes[rb]}={rb_fire_between%state_sizes[rb]}")

                # Now the BAF arc version: look at cwNeighborStep and ccwProcStep
                # cwNeighborStep: step where right(b) fires CW (next step after b fires CW)
                # Actually, in the BAF arc:
                # cwProcStep = cw_step (b fires CW)
                # cwNeighborStep = step where rb fires, after cwProcStep, in CW direction
                # ccwNeighborStep = step where rb fires, in CCW direction
                # ccwProcStep = step where b fires CCW

                rb_fires = [i for i in range(len(w)) if w[i] == rb]
                # Find rb step that's after cw_step and has CW direction
                rb_cw = [i for i in rb_fires if i > cw_step and steps[i] == 1]
                rb_ccw = [i for i in rb_fires if i < ccw_step and steps[i] == -1]

                if rb_cw and rb_ccw:
                    rbcw = rb_cw[0]
                    rbccw = rb_ccw[-1]
                    if rbcw < rbccw:
                        # Valid BAF arc ordering
                        # Between cwNeighborStep (rbcw) and ccwProcStep (ccw_step):
                        # who fires?
                        fires_baf = Counter(w[i] for i in range(rbcw, ccw_step))
                        print(f"    BAF arc: cwNb@{rbcw}, ccwNb@{rbccw}, ccwProc@{ccw_step}")
                        print(f"    Between cwNb and ccwProc: {dict(fires_baf)}")
                        print(f"    b fires: {fires_baf.get(b, 0)}, lb fires: {fires_baf.get(lb, 0)}, "
                              f"rb fires: {fires_baf.get(rb, 0)}")


if __name__ == '__main__':
    main()
