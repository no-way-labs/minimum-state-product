#!/usr/bin/env python3
"""
Zero-Winding Palindromic EC Proof — Phase 3 (Analytical)

FINDINGS FROM PHASES 1-2:
1. ALL ZW fc=2 words have EC (verified n=5,7 exhaustively, all procs checked)
2. Two word families:
   A) Words with stay steps (turnaround at a proc) -- "stay-BAF"
   B) Words without stay steps (turnaround between procs) -- "pure-BAF"
3. Family A has EC at binary procs via standard BAF arc
4. Family B: the "full traverse" type has EC at TERNARY procs adjacent to binary

STRUCTURAL CLASSIFICATION:
- Every ZW fc=2 word has exactly 0 or 2 reversals (from CW to CCW or vice versa)
- 0 reversals = "stay-BAF": uses stay steps for turnaround
- 2 reversals = "pure-BAF": instant direction reversal

KEY INSIGHT: For the pure-BAF words, the reversal point is where a proc
fires CW and then the SAME proc fires again immediately. This creates a
"U-turn" at that proc.

PROOF STRATEGY:
For any ZW fc=2 word with >=3 binary procs:
Case 1: Some binary proc b has a BAF arc with binary right(b).
  -> Standard BAF EC: right(b) fires twice (CW+CCW), 2 mod 2 = 0, value returns.
Case 2: All binary procs are at "turnaround points" or have non-binary neighbors.
  -> The word structure forces EC at some interior proc.

Let me classify all words precisely and find the universal EC mechanism.
"""

from collections import Counter

def classify_word(word, n):
    CL = len(word)
    steps = []
    cw = 0; ccw = 0; stay = 0
    for i in range(CL):
        nxt = word[(i + 1) % CL]
        cur = word[i]
        disp = (nxt - cur) % n
        if disp == 1: steps.append(+1); cw += 1
        elif disp == n - 1: steps.append(-1); ccw += 1
        elif disp == 0: steps.append(0); stay += 1
        else: steps.append(None)
    return steps, cw, ccw, stay


def enumerate_zw_fc2(n):
    CL = 2 * n
    results = []
    def gen(pos, word, fc, cw, ccw):
        if pos == CL:
            d = (word[0] - word[-1]) % n
            c, cc = cw, ccw
            if d == 1: c += 1
            elif d == n - 1: cc += 1
            elif d != 0: return
            if c == cc and c > 0:
                results.append(tuple(word))
            return
        for p in range(n):
            if fc[p] >= 2: continue
            if pos > 0:
                d = (p - word[-1]) % n
                if d not in (0, 1, n-1): continue
                nc = cw + (1 if d == 1 else 0)
                ncc = ccw + (1 if d == n-1 else 0)
            else:
                nc, ncc = cw, ccw
            fc[p] += 1; word.append(p)
            gen(pos + 1, word, fc, nc, ncc)
            word.pop(); fc[p] -= 1
    gen(0, [], [0]*n, 0, 0)
    canonical = set()
    for w in results:
        rots = [tuple(w[i:] + w[:i]) for i in range(len(w))]
        canonical.add(min(rots))
    return sorted(canonical)


def find_ec_at_proc(word, n, b, state_sizes):
    """Find an EC pair at proc b."""
    CL = len(word)
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
            if (bf % state_sizes[b] == 0 and
                lbf % state_sizes[lb] == 0 and
                rbf % state_sizes[rb] == 0):
                return (ms, nms, bf, lbf, rbf)
    return None


def main():
    print("=" * 70)
    print("UNIVERSAL EC MECHANISM IDENTIFICATION")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)

            # Find EC at some proc
            ec_proc = None
            for p in range(n):
                result = find_ec_at_proc(w, n, p, state_sizes)
                if result:
                    ec_proc = p
                    ec_data = result
                    break

            print(f"\n  Word: {w}")
            print(f"  Steps: {step_str}  CW={cw} CCW={ccw} Stay={stay}")

            if ec_proc is not None:
                ms, nms, bf, lbf, rbf = ec_data
                print(f"  EC at proc {ec_proc} (m={state_sizes[ec_proc]}): "
                      f"mover_step={ms}, nonmover_step={nms}")
                print(f"    b_fires={bf}, lb_fires={lbf}, rb_fires={rbf}")

                # Analyze the structure of the EC
                lb = (ec_proc - 1) % n
                rb = (ec_proc + 1) % n
                print(f"    left={lb}(m={state_sizes[lb]}), self={ec_proc}(m={state_sizes[ec_proc]}), "
                      f"right={rb}(m={state_sizes[rb]})")
                print(f"    At mover_step {ms}: word[{ms}]={w[ms]}, dir={steps[ms]}")
                print(f"    At nonmover_step {nms}: word[{nms}]={w[nms]}, dir={steps[nms]}")
            else:
                print(f"  NO EC FOUND!")

    # Now the KEY analysis: understand the EC mechanism for EACH word type
    print(f"\n\n{'='*70}")
    print("EC MECHANISM CLASSIFICATION")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1: 'R', -1: 'L', 0: 'S', None: '?'}[s] for s in steps)

            # Classify the word structure
            # Find turnaround points (where direction changes or stays)
            reversals = []
            for i in range(len(steps)):
                d1 = steps[i]
                d2 = steps[(i+1) % len(steps)]
                if (d1 == 1 and d2 == -1) or (d1 == -1 and d2 == 1):
                    reversals.append(i)

            stays = [i for i in range(len(steps)) if steps[i] == 0]

            # The word structure is determined by turnaround points
            # For "stay-BAF": turnarounds are at stay positions
            # For "pure-BAF": turnarounds are at reversal positions

            # Find the CW arc and CCW arc
            cw_arc = [i for i in range(len(steps)) if steps[i] == 1]
            ccw_arc = [i for i in range(len(steps)) if steps[i] == -1]

            # Which proc is the "turnaround proc" (rightmost in CW direction)?
            # For a stay at position i: proc w[i] = w[i+1] is the turnaround
            # For a reversal at position i: proc at the reversal

            if stays:
                turnaround_procs = set(w[i] for i in stays)
            else:
                turnaround_procs = set()
                for r in reversals:
                    turnaround_procs.add(w[r])

            # Find ALL EC pairs, classify by mechanism
            ec_at_binary = False
            ec_at_ternary = False
            ec_info = []

            for p in range(n):
                result = find_ec_at_proc(w, n, p, state_sizes)
                if result:
                    ms, nms, bf, lbf, rbf = result
                    is_binary = (state_sizes[p] == 2)
                    is_turnaround = (p in turnaround_procs)

                    mechanism = "binary-BAF" if is_binary else "ternary-adjacent"
                    if is_turnaround:
                        mechanism += "+turnaround"

                    ec_info.append((p, is_binary, is_turnaround, mechanism, result))
                    if is_binary:
                        ec_at_binary = True
                    else:
                        ec_at_ternary = True

            # Print classification
            if ec_at_binary:
                mech = "BINARY-BAF"
            elif ec_at_ternary:
                mech = "TERNARY-ADJACENT"
            else:
                mech = "NONE"

            # Get the first EC
            first_ec = ec_info[0] if ec_info else None
            p, is_bin, is_turn, mechanism, result = first_ec
            ms, nms, bf, lbf, rbf = result

            print(f"  {step_str}  {mech}  EC@{p}(m={state_sizes[p]}) "
                  f"ms={ms},nms={nms} fires=({bf},{lbf},{rbf}) "
                  f"{'turn' if is_turn else 'interior'}")

    # DEEP STRUCTURAL ANALYSIS: the BAF arc for interior binary procs
    print(f"\n\n{'='*70}")
    print("DEEP ANALYSIS: BAF ARC AT INTERIOR BINARY PROCS")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n--- n = {n} ---")

        if n <= 7:
            words = enumerate_zw_fc2(n)
        else:
            # Generate structural words for n=9
            words = []
            # Stay-BAF words: parameterized by turnaround proc T
            for T in range(n):
                # CW: 0, 1, ..., T, T (stay), T-1, ..., 1, 0 (stay), n-1, ..., T+1
                # Wait, this doesn't have fc=2 for all procs.
                # Let me construct properly.
                # The "stay-BAF at T": start at T, stay, go CW to T+n-1, stay, go CCW back to T+1
                # word: T, T, T+1, T+2, ..., T+n-1, T+n-1, T+n-2, ..., T+1 (mod n)
                w = [T % n, T % n]
                for i in range(1, n):
                    w.append((T + i) % n)
                w.append((T + n - 1) % n)
                for i in range(n - 2, 0, -1):
                    w.append((T + i) % n)
                if len(w) == 2 * n:
                    # Verify fc=2
                    fc = Counter(w)
                    if all(fc[p] == 2 for p in range(n)):
                        words.append(tuple(w))

            # Pure-BAF words: parameterized by reversal position
            for R in range(n):
                # CW from R to R+k, reverse, CCW to R-k, reverse, CW back
                # For pure-BAF with 2 reversals:
                # Start at R, go CW to R+k, reverse, go CCW back through R to R-(n-k-1)
                # Actually: for no-stay words, we need CW=CCW=n
                # word: R, R+1, ..., R+k, R+k-1, ..., R-j, R-j+1, ..., R
                # where k + k + j + j = 2n (or something)
                # Let me just compute for k from 1 to n-1
                for k in range(1, n):
                    w = [R % n]
                    for i in range(1, k + 1):
                        w.append((R + i) % n)
                    # Now reverse
                    for i in range(k - 1, -(n - k), -1):
                        w.append((R + i) % n)
                    # Now back up
                    for i in range(-(n - k - 1), 0):
                        w.append((R + i) % n)
                    # Check length and fc
                    if len(w) == 2 * n:
                        fc = Counter(w)
                        if all(fc[p] == 2 for p in range(n)):
                            # Check ZW
                            steps, cw, ccw, stay = classify_word(w, n)
                            if cw == ccw and cw > 0:
                                words.append(tuple(w))

            # Deduplicate
            canonical = set()
            for w in words:
                rots = [tuple(w[i:] + w[:i]) for i in range(len(w))]
                canonical.add(min(rots))
            words = sorted(canonical)

        state_sizes = [2 if p < 3 else 3 for p in range(n)]
        print(f"  Words: {len(words)}")

        all_have_ec = True
        for w in words:
            found = False
            for p in range(n):
                if find_ec_at_proc(w, n, p, state_sizes):
                    found = True
                    break
            if not found:
                all_have_ec = False
                print(f"  NO EC: {w}")

        print(f"  All have EC: {all_have_ec}")

        # For each word, show the BAF arc analysis
        if n <= 7 and len(words) <= 15:
            for w in words:
                steps, cw, ccw, stay = classify_word(w, n)

                # For each binary proc b in {0,1,2}, check if it has a "good"
                # BAF arc: b fires CW then CCW (or reversed), and between the
                # CW-nonmover-step and CCW-mover-step, the fire counts work out.

                # The KEY step pair for binary b:
                # - nonmover_step: the step just AFTER b fires CW (when right(b) fires CW)
                # - mover_step: the step when b fires CCW
                # Between these: b doesn't fire (it fired at CW, fires at CCW).
                # left(b) must fire 0 mod m_{lb} times.
                # right(b) must fire 0 mod m_{rb} times (but it fires at nonmover_step!).

                for b in [0, 1, 2]:
                    b_fires = [i for i in range(len(w)) if w[i] == b]
                    if len(b_fires) != 2:
                        continue

                    # Step directions at b's two firings
                    d0 = steps[b_fires[0]]
                    d1 = steps[b_fires[1]]

                    lb = (b - 1) % n
                    rb = (b + 1) % n

                    # For each firing pair, check the interval
                    for f1, f2 in [(b_fires[0], b_fires[1]), (b_fires[1], b_fires[0])]:
                        # Interval from f1 to f2 (exclusive at both ends for "between")
                        if f2 > f1:
                            interval = range(f1 + 1, f2)
                        else:
                            interval = list(range(f1 + 1, len(w))) + list(range(0, f2))

                        fires = Counter(w[i] for i in interval)

                        # For EC: we compare config at some nonmover step vs mover step f2
                        # The nonmover step must be in the interval where b doesn't fire

                        # The config at f2 (before b fires) vs config at nms (before nms mover fires)
                        # Changes from config(nms) to config(f2): steps nms, nms+1, ..., f2-1

                        # Let's just check: does b have a nonmover step nms where
                        # from nms to f2, b fires 0 times, lb fires 0 mod m, rb fires 0 mod m?

                        # The simplest: nms = f1 + 1 (step right after b fires CW)
                        # At nms, the mover is word[f1+1] which should be right(b) if CW
                        nms = (f1 + 1) % len(w)
                        if w[nms] == b:
                            continue  # b fires again, not useful

                        if f2 > nms:
                            check_interval = range(nms, f2)
                        else:
                            check_interval = list(range(nms, len(w))) + list(range(0, f2))

                        check_fires = Counter(w[i] for i in check_interval)
                        bf = check_fires.get(b, 0)
                        lbf = check_fires.get(lb, 0)
                        rbf = check_fires.get(rb, 0)

                        ec = (bf % state_sizes[b] == 0 and
                              lbf % state_sizes[lb] == 0 and
                              rbf % state_sizes[rb] == 0)

                        if ec:
                            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)
                            print(f"  BAF-EC at b={b}: word={w}  steps={step_str}")
                            print(f"    f1={f1}(dir={steps[f1]}), f2={f2}(dir={steps[f2]})")
                            print(f"    nms={nms}(mover={w[nms]}), check: b={bf}, lb={lbf}, rb={rbf}")
                            break
                    else:
                        continue
                    break

    # THE ANALYTICAL PROOF
    print(f"\n\n{'='*70}")
    print("ANALYTICAL PROOF: THE TWO MECHANISMS")
    print("=" * 70)

    print("""
THEOREM: In a zero-winding good cycle with cwStepCount > 0, fc(p) = 2
for all p, CL = 2n, and >= 3 binary procs with n >= 5: hasEntryConflict.

PROOF OUTLINE:

Given: A ZW mover word w of length 2n on Z_n with fc(p)=2 for all p.
       CW steps = CCW steps > 0.
       At least 3 procs have state size 2 (binary).

The mover word w is a closed walk on Z_n where each vertex appears exactly
twice and each step is +1 (CW), -1 (CCW), or 0 (stay).

STRUCTURE LEMMA: Every such word has exactly 2 "turnaround regions" (where
the walk changes from CW to CCW or vice versa). Between turnarounds, the
walk visits a contiguous arc of procs in one direction.

More precisely, up to cyclic rotation, the word has the form:
  CW phase: p0, p0+1, ..., p0+a  (a CW steps)
  Turnaround 1 (possibly with stay steps)
  CCW phase: q0, q0-1, ..., q0-b  (b CCW steps)
  Turnaround 2 (possibly with stay steps)
  ... back to p0

Since CW = CCW and total = 2n, the two phases cover all n procs.

THE EC ARGUMENT:

Consider 3 consecutive binary procs at positions {j-1, j, j+1} (mod n).
(If binary procs are non-consecutive, a separate argument applies.)

At least one binary proc is "interior" to one of the two directed arcs
(CW or CCW). Call this proc b. Then:
- b fires once during the CW arc (step index i_CW)
- b fires once during the CCW arc (step index i_CCW)
- right(b) = b+1 also fires once during each arc (step indices i_CW+1 and i_CCW-1)
- left(b) = b-1 also fires once during each arc (step indices i_CW-1 and i_CCW+1)

KEY STEP PAIR:
- nonmover_step = i_CW + 1 (the step AFTER b fires CW, when right(b) fires CW)
  At this step, b is a non-mover.
- mover_step = i_CCW (the step when b fires CCW)
  At this step, b is the mover.

FIRE COUNT ANALYSIS (from nonmover_step to mover_step):
The interval [i_CW + 1, i_CCW) in the mover word contains:
- b fires 0 times (b fired at i_CW, will fire again at i_CCW)
  -> val(b) preserved: SELF EQUALITY

- left(b): Let's count. left(b) fires at i_CW - 1 (CW arc) and i_CCW + 1 (CCW arc).
  If i_CW - 1 < i_CW + 1 (always true) and i_CCW + 1 > i_CCW (always true):
  left(b) fires at i_CW - 1 (before our interval) and at i_CCW + 1 (after our interval).
  So left(b) fires 0 times in [i_CW + 1, i_CCW).
  -> val(left(b)) preserved: LEFT EQUALITY

- right(b): right(b) fires at i_CW + 1 (the nonmover_step itself) and at i_CCW - 1 (CCW arc).
  WAIT: i_CW + 1 is the nonmover_step. Is it in the interval?
  The interval [i_CW + 1, i_CCW) starts at i_CW + 1 (inclusive of the step).

  Actually, we need to be precise about what "config at step s" means.
  Config(s) = the configuration BEFORE step s fires.
  From config(s1) to config(s2): steps s1, s1+1, ..., s2-1 fire.

  So from config(nonmover_step) to config(mover_step):
  Steps that fire: nonmover_step, nonmover_step+1, ..., mover_step-1.
  = i_CW+1, i_CW+2, ..., i_CCW-1.

  right(b) fires at: i_CW+1 (= nonmover_step, which IS included!) and i_CCW-1.
  Total: right(b) fires 2 times.
  For binary right(b): 2 mod 2 = 0. VALUE RETURNS!
  -> val(right(b)) preserved: RIGHT EQUALITY

CONCLUSION: At nonmover_step, proc b sees context (L, S, R) as non-mover.
At mover_step, proc b sees the SAME (L, S, R) as mover.
This is an entry conflict. QED.

WAIT — I need to verify the "interior" condition more carefully.
The above argument requires:
1. b fires once in each arc (CW and CCW)
2. left(b) fires once in each arc, BEFORE b in CW and AFTER b in CCW
3. right(b) fires once in each arc, AFTER b in CW and BEFORE b in CCW

This holds when b is "interior" to the arcs: not at a turnaround point.

CONDITION: b is interior to both arcs if and only if b is not a
turnaround proc (the proc where the walk reverses direction).

With >= 3 binary procs and n >= 5: at most 2 turnaround procs,
so at least 1 binary proc is not a turnaround proc.

Actually, I need to be more careful. Let me verify computationally.
""")

    # Verify the analytical argument
    for n in [5, 7]:
        print(f"\n--- Verifying at n = {n} ---")
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        all_have_interior_binary_ec = True

        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

            # Find turnaround procs
            # A turnaround proc is one where the walk visits it with a stay step,
            # OR where the walk reverses direction at it.
            turnaround_procs = set()
            for i in range(len(steps)):
                if steps[i] == 0:  # Stay step
                    turnaround_procs.add(w[i])

            # Also check reversal: if step i is CW and step i+1 is CCW,
            # the turnaround is at proc w[i+1] (= w[i]+1 for CW, then goes back)
            for i in range(len(steps)):
                d1 = steps[i]
                d2 = steps[(i+1) % len(steps)]
                if d1 == 1 and d2 == -1:
                    # CW to CCW reversal at proc w[(i+1) % len(w)]
                    turnaround_procs.add(w[(i+1) % len(w)])
                elif d1 == -1 and d2 == 1:
                    # CCW to CW reversal at proc w[(i+1) % len(w)]
                    turnaround_procs.add(w[(i+1) % len(w)])

            # Find an interior binary proc (not a turnaround)
            binary_interior = [b for b in [0, 1, 2] if b not in turnaround_procs]

            if not binary_interior:
                # All 3 binary procs are turnaround procs
                # This can happen if <=2 turnarounds but binary procs are at them
                print(f"  Word {w}: ALL binary at turnarounds: {turnaround_procs}")

                # Still check EC at all procs
                found_ec = False
                for p in range(n):
                    if find_ec_at_proc(w, n, p, state_sizes):
                        found_ec = True
                        break
                if not found_ec:
                    print(f"    NO EC AT ALL!")
                    all_have_interior_binary_ec = False
                else:
                    print(f"    EC found at other proc")
                continue

            b = binary_interior[0]
            lb = (b - 1) % n
            rb = (b + 1) % n

            # Find b's two firing positions and their directions
            b_fires = [i for i in range(len(w)) if w[i] == b]
            assert len(b_fires) == 2

            d0 = steps[b_fires[0]]
            d1 = steps[b_fires[1]]

            if d0 == 1 and d1 == -1:
                i_CW = b_fires[0]
                i_CCW = b_fires[1]
            elif d0 == -1 and d1 == 1:
                i_CW = b_fires[1]
                i_CCW = b_fires[0]
            elif d0 == 1 and d1 == 1:
                print(f"  Word {w}: b={b} fires CW twice! steps={step_str}")
                continue
            elif d0 == -1 and d1 == -1:
                print(f"  Word {w}: b={b} fires CCW twice! steps={step_str}")
                continue
            else:
                print(f"  Word {w}: b={b} fires with stay! d0={d0}, d1={d1}")
                continue

            # The key step pair
            nonmover_step = (i_CW + 1) % len(w)
            mover_step = i_CCW

            # Verify: at nonmover_step, b is not the mover
            assert w[nonmover_step] != b, f"b fires at nonmover_step! w={w}, b={b}"

            # Count fires from config(nonmover_step) to config(mover_step)
            if mover_step > nonmover_step:
                interval = range(nonmover_step, mover_step)
            else:
                interval = list(range(nonmover_step, len(w))) + list(range(0, mover_step))

            fires = Counter(w[i] for i in interval)
            bf = fires.get(b, 0)
            lbf = fires.get(lb, 0)
            rbf = fires.get(rb, 0)

            # Check parity
            b_ok = (bf % state_sizes[b] == 0)
            lb_ok = (lbf % state_sizes[lb] == 0)
            rb_ok = (rbf % state_sizes[rb] == 0)
            ec = b_ok and lb_ok and rb_ok

            if not ec:
                print(f"  Word {w}: b={b}, i_CW={i_CW}, i_CCW={i_CCW}")
                print(f"    nonmover={nonmover_step}, mover={mover_step}")
                print(f"    b_fires={bf}(ok={b_ok}), lb_fires={lbf}(ok={lb_ok}), "
                      f"rb_fires={rbf}(ok={rb_ok})")
                print(f"    steps={step_str}")
                print(f"    turnarounds={turnaround_procs}")

                # Try the OTHER direction: nonmover at i_CCW-1, mover at i_CW
                nonmover_step2 = (i_CCW - 1) % len(w)
                mover_step2 = i_CW

                if w[nonmover_step2] != b:
                    if mover_step2 > nonmover_step2:
                        interval2 = range(nonmover_step2, mover_step2)
                    else:
                        interval2 = list(range(nonmover_step2, len(w))) + list(range(0, mover_step2))

                    fires2 = Counter(w[i] for i in interval2)
                    bf2 = fires2.get(b, 0)
                    lbf2 = fires2.get(lb, 0)
                    rbf2 = fires2.get(rb, 0)
                    b_ok2 = (bf2 % state_sizes[b] == 0)
                    lb_ok2 = (lbf2 % state_sizes[lb] == 0)
                    rb_ok2 = (rbf2 % state_sizes[rb] == 0)
                    ec2 = b_ok2 and lb_ok2 and rb_ok2

                    print(f"    Alt: nonmover={nonmover_step2}, mover={mover_step2}")
                    print(f"      b_fires={bf2}(ok={b_ok2}), lb_fires={lbf2}(ok={lb_ok2}), "
                          f"rb_fires={rbf2}(ok={rb_ok2})")

                    if not ec2:
                        # Try exhaustive search at this proc
                        result = find_ec_at_proc(w, n, b, state_sizes)
                        if result:
                            ms, nms, bf3, lbf3, rbf3 = result
                            print(f"    Exhaustive: ms={ms}, nms={nms}, b={bf3}, lb={lbf3}, rb={rbf3}")
                        else:
                            print(f"    NO EC AT THIS BINARY PROC!")
                            all_have_interior_binary_ec = False

        print(f"  All interior binary procs have EC: {all_have_interior_binary_ec}")


if __name__ == '__main__':
    main()
