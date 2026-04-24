#!/usr/bin/env python3
"""
Zero-Winding Palindromic EC Proof — Phase 4 (Clean Proof)

KEY INSIGHT FROM PHASES 1-3:
The EC does NOT always come from a single interior binary proc.
The CORRECT approach: use the BAF arc at proc b with a SPECIFIC step pair
where the fire counts of left(b), b, right(b) are all 0 mod their state sizes.

The winning mechanism consistently found by the exhaustive search:
For a binary proc b at the START of the CW arc (i.e., the first binary proc
fired in the CW direction):
  - mover_step = b's CW firing
  - nonmover_step = step where left(b) fires CCW (b is non-mover)
  - Between these: b fires 0 times, left(b) fires 2 times (mod 2 = 0), right(b) fires 0 times

Let me identify the EXACT universal mechanism.
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


def find_all_ec_pairs(word, n, state_sizes):
    """Find ALL EC pairs at ALL processors."""
    CL = len(word)
    ec_list = []
    for b in range(n):
        lb = (b - 1) % n
        rb = (b + 1) % n
        mover_steps = [i for i in range(CL) if word[i] == b]
        for ms in mover_steps:
            for nms in range(CL):
                if word[nms] == b: continue
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
                    ec_list.append({
                        'proc': b,
                        'mover_step': ms,
                        'nonmover_step': nms,
                        'b_fires': bf,
                        'lb_fires': lbf,
                        'rb_fires': rbf,
                    })
    return ec_list


def main():
    print("=" * 70)
    print("IDENTIFYING THE UNIVERSAL EC MECHANISM")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

            ec_list = find_all_ec_pairs(w, n, state_sizes)
            assert ec_list, f"No EC for word {w}!"

            # Classify each EC by the pattern (b_fires, lb_fires, rb_fires)
            # and whether proc is binary/ternary
            patterns = set()
            for ec in ec_list:
                b = ec['proc']
                patterns.add((
                    state_sizes[b],
                    ec['b_fires'], ec['lb_fires'], ec['rb_fires']
                ))

            # Show the simplest EC (fewest total fires)
            ec_list.sort(key=lambda e: e['b_fires'] + e['lb_fires'] + e['rb_fires'])
            best = ec_list[0]

            # Check: is there an EC with (b=0, lb=0, rb=0)?
            zero_ec = [e for e in ec_list if e['b_fires']==0 and e['lb_fires']==0 and e['rb_fires']==0]

            # Check: is there an EC with just b=0?
            bzero_ec = [e for e in ec_list if e['b_fires']==0]

            # What's the relationship between mover_step and nonmover_step?
            ms = best['mover_step']
            nms = best['nonmover_step']
            b = best['proc']
            lb = (b - 1) % n
            rb = (b + 1) % n

            # What fires at the mover step and nonmover step?
            print(f"\nWord: {w}  Steps: {step_str}")
            print(f"  Best EC at proc {b}(m={state_sizes[b]}): ms={ms}(mover={w[ms]},dir={steps[ms]}), "
                  f"nms={nms}(mover={w[nms]},dir={steps[nms]})")
            print(f"    fires: b={best['b_fires']}, lb={best['lb_fires']}, rb={best['rb_fires']}")

            if zero_ec:
                ze = zero_ec[0]
                print(f"  Zero-fire EC at proc {ze['proc']}: ms={ze['mover_step']}, nms={ze['nonmover_step']}")
                # These are the step pairs where NO neighbor fires between them
                # This means the nonmover step is the step JUST BEFORE the mover step
                # or they are very close together
                gap = (ze['mover_step'] - ze['nonmover_step']) % (2*n)
                print(f"    Gap (ms - nms mod CL): {gap}")

    # Now let me understand the structure more precisely
    print(f"\n\n{'='*70}")
    print("PRECISE STRUCTURE: WHICH STEP PAIRS GIVE EC?")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

            ec_list = find_all_ec_pairs(w, n, state_sizes)

            # Focus on EC pairs with b_fires = 0 (self doesn't fire between)
            bzero = [e for e in ec_list if e['b_fires'] == 0]

            # For each, understand the relationship
            print(f"\n  Word: {w}  Steps: {step_str}")
            for ec in bzero:
                b = ec['proc']
                ms = ec['mover_step']
                nms = ec['nonmover_step']

                # What is the mover at nms?
                nms_mover = w[nms]
                # Is nms_mover adjacent to b?
                nms_relation = None
                if nms_mover == (b + 1) % n: nms_relation = "right(b)"
                elif nms_mover == (b - 1) % n: nms_relation = "left(b)"
                else: nms_relation = f"proc {nms_mover}"

                # Step direction at mover step and nonmover step
                ms_dir = steps[ms]
                nms_dir = steps[nms]

                # Are they on opposite arcs? (CW vs CCW)
                opposite = (ms_dir * nms_dir == -1) or (ms_dir == 0 or nms_dir == 0)

                # Gap
                if ms > nms:
                    gap = ms - nms
                else:
                    gap = ms + 2*n - nms

                print(f"    b={b}(m={state_sizes[b]}): ms={ms}(dir={ms_dir}), nms={nms}(dir={nms_dir}), "
                      f"nms_mover={nms_relation}, gap={gap}, "
                      f"lb={ec['lb_fires']}, rb={ec['rb_fires']}")

    # THE KEY: look at which pairs have lb_fires = 0 AND rb_fires = 0
    print(f"\n\n{'='*70}")
    print("ZERO-FIRE EC PAIRS: b=0, lb=0, rb=0")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

            ec_list = find_all_ec_pairs(w, n, state_sizes)
            zero_ec = [e for e in ec_list if e['b_fires']==0 and e['lb_fires']==0 and e['rb_fires']==0]

            if zero_ec:
                print(f"  {step_str}: {len(zero_ec)} zero-fire ECs")
                for e in zero_ec[:3]:
                    b = e['proc']
                    ms = e['mover_step']
                    nms = e['nonmover_step']
                    gap = (ms - nms) % (2*n)
                    print(f"    proc={b}, ms={ms}(dir={steps[ms]}), nms={nms}(dir={steps[nms]}), gap={gap}")

    # OK, now let me take a DIFFERENT approach.
    # Instead of looking for the magic step pair, let me look at the
    # WALK STRUCTURE and prove the EC from the walk's palindromic properties.

    print(f"\n\n{'='*70}")
    print("WALK STRUCTURE ANALYSIS")
    print("=" * 70)

    # Every ZW fc=2 word is parameterized by its turnaround position T.
    # After normalizing by rotation, the word has the form:
    #   Phase 1: go CW from proc a to proc a+T  (T CW steps)
    #   Turnaround 1 (stay at a+T, or reversal at a+T)
    #   Phase 2: go CCW from a+T back to a-T'  (T+T' CCW steps = T CW steps)
    #   Turnaround 2 (stay at a-T', or reversal at a-T')
    #   Phase 3: go CW from a-T' back to a  (T' CW steps)
    #
    # Wait, this is more complex. Let me look at the enumerated words.

    for n in [5]:
        print(f"\n--- n = {n}: all words ---")
        words = enumerate_zw_fc2(n)

        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

            # Track the walk position
            positions = [w[0]]
            for i in range(1, len(w)):
                positions.append(w[i])

            # Find the CW arcs and CCW arcs
            cw_arcs = []
            ccw_arcs = []
            current_arc = [0]
            current_dir = steps[0]

            for i in range(1, len(steps)):
                if steps[i] == current_dir or steps[i] == 0 or current_dir == 0:
                    current_arc.append(i)
                    if current_dir == 0 and steps[i] != 0:
                        current_dir = steps[i]
                else:
                    if current_dir == 1:
                        cw_arcs.append(current_arc)
                    elif current_dir == -1:
                        ccw_arcs.append(current_arc)
                    current_arc = [i]
                    current_dir = steps[i]

            # Don't forget the last arc (wraps to start)
            if current_dir == 1:
                cw_arcs.append(current_arc)
            elif current_dir == -1:
                ccw_arcs.append(current_arc)

            # For each CW arc, find the procs visited
            print(f"\n  Word: {w}  Steps: {step_str}")
            print(f"    CW arcs: {cw_arcs}")
            print(f"    CCW arcs: {ccw_arcs}")

            # The PROOF: for a CW arc visiting procs a, a+1, ..., a+d
            # and a CCW arc visiting procs b, b-1, ..., b-d':
            # if these arcs overlap on some contiguous range,
            # then an interior proc in the overlap sees matching context.

            # Find overlapping ranges
            cw_proc_sets = []
            for arc in cw_arcs:
                procs = [w[i] for i in arc]
                cw_proc_sets.append(procs)

            ccw_proc_sets = []
            for arc in ccw_arcs:
                procs = [w[i] for i in arc]
                ccw_proc_sets.append(procs)

            print(f"    CW procs: {cw_proc_sets}")
            print(f"    CCW procs: {ccw_proc_sets}")

    # THE DEFINITIVE ANALYSIS: the step pair from the CW-CCW overlap
    print(f"\n\n{'='*70}")
    print("DEFINITIVE: CW-CCW OVERLAP YIELDS EC")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        all_ok = True
        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)

            # For each proc b (try binary first):
            # Find the two steps where b fires: b_fires[0] and b_fires[1]
            # One should be CW, one CCW.
            # The KEY pair:
            #   mover_step = b's CW firing
            #   nonmover_step = step where left(b) fires CCW
            #   (or vice versa: mover_step = b's CCW firing,
            #    nonmover_step = step where right(b) fires CW)

            found = False
            for b in range(n):
                if found: break
                lb = (b - 1) % n
                rb = (b + 1) % n

                b_fire_steps = [i for i in range(len(w)) if w[i] == b]
                if len(b_fire_steps) != 2: continue

                # Find lb and rb fire steps
                lb_fire_steps = [i for i in range(len(w)) if w[i] == lb]
                rb_fire_steps = [i for i in range(len(w)) if w[i] == rb]

                # Strategy: look for a pair where b fires as mover,
                # and one of its neighbors fires as mover at a step where
                # b is non-mover, and the interval between has the right parities.

                for ms in b_fire_steps:
                    for nms_mover_proc in [lb, rb]:
                        nms_candidates = [i for i in range(len(w)) if w[i] == nms_mover_proc]
                        for nms in nms_candidates:
                            if w[nms] == b: continue

                            # Count fires from config(nms) to config(ms)
                            if ms > nms:
                                interval = range(nms, ms)
                            else:
                                interval = list(range(nms, len(w))) + list(range(0, ms))

                            fires = Counter(w[i] for i in interval)
                            bf = fires.get(b, 0)
                            lbf = fires.get(lb, 0)
                            rbf = fires.get(rb, 0)

                            if (bf % state_sizes[b] == 0 and
                                lbf % state_sizes[lb] == 0 and
                                rbf % state_sizes[rb] == 0):
                                found = True
                                break
                        if found: break
                    if found: break

            if not found:
                print(f"  NO EC: {w}")
                all_ok = False

        print(f"  All have EC: {all_ok}")

    # Finally: the ACTUAL proof mechanism that works for ALL words
    print(f"\n\n{'='*70}")
    print("PROOF MECHANISM: ADJACENT-PAIR EC")
    print("=" * 70)
    print("""
For each ZW fc=2 word, we look for two ADJACENT procs {b, b+1} that
are both interior (not at turnaround). At these procs:
- b fires CW at some step i, CCW at some step j
- b+1 fires CW at step i+1 (right after b in CW), CCW at step j-1 (right before b in CCW)

The EC at b uses:
  mover_step = j (b fires CCW)
  nonmover_step = i+1 (b+1 fires CW, b is non-mover)

Between config(i+1) and config(j):
  b fires: 0 (b fired at i, fires again at j)
  left(b) = b-1: fires at i-1 and j+1, both outside interval -> 0 fires
  right(b) = b+1: fires at i+1 (included!) and j-1 (included!) -> 2 fires
    For binary b+1: 2 mod 2 = 0

WAIT: the interval from config(nms=i+1) to config(ms=j) includes
steps i+1, i+2, ..., j-1. The mover at step i+1 is b+1.
How many times does b+1 fire in steps i+1, ..., j-1?
b+1 fires at step i+1 (included) and at step j-1 (if j-1 is a b+1 step).

Actually, between steps i+1 and j-1 INCLUSIVE:
- step i+1: b+1 fires CW
- step j-1: b+1 fires CCW
These are b+1's ONLY two firings. So b+1 fires 2 times.

For binary b+1: 2 mod 2 = 0. VALUE RETURNS.
For left(b) = b-1: b-1 fires at i-1 (CW) and j+1 (CCW).
  i-1 < i+1 (before interval) and j+1 > j-1 (after interval).
  So 0 fires. VALUE PRESERVED.

This gives EC at b: same (L, S, R) at mover step j and non-mover step i+1.

THE REQUIREMENT: b and b+1 are both interior to BOTH arcs.
This means: in the CW arc, b fires before b+1 (b is to the left of b+1).
In the CCW arc, b+1 fires before b (b+1 is to the left of b).

This holds when the walk traverses ..., b, b+1, ... in CW direction
and ..., b+1, b, ... in CCW direction.

WHEN DOES THIS FAIL? Only when b or b+1 is at a turnaround point.
With 2 turnaround points and 3 binary procs: at most 2 binary procs
can be at turnarounds. So at least 1 binary proc and its neighbor
are both interior.

Actually, we need TWO adjacent interior binary procs. With 3 consecutive
binary procs at {a, a+1, a+2} and 2 turnarounds: at most 2 of the 3
are at turnarounds. So at least one of {a, a+1} or {a+1, a+2} is an
interior pair.

For the EC, we need b to be binary AND right(b) = b+1 to be binary.
With 3 consecutive binary procs: any interior pair from {a, a+1, a+2}
where both elements are interior works.

EDGE CASE: all 3 binary procs are turnaround or endpoint procs.
With only 2 turnaround points: impossible for 3 to be at turnarounds.
(Could happen if turnarounds are AT 2 of the 3 binary procs.)
Then the 3rd binary proc is interior. But is its NEIGHBOR also interior
AND binary? The neighbor might not be binary.

THIS IS THE CASE that fails and requires a different argument!

For 3 CONSECUTIVE binary: if turnarounds are at positions a and a+2,
then a+1 is interior, and both a and a+2 are turnarounds.
But a+1's neighbors a and a+2 are binary turnarounds.
The BAF argument at a+1 with right(a+1) = a+2 (binary, turnaround):
- a+2 fires CW at step T1 and CCW at step T2 (the turnaround steps)
- Between these steps, a+2 doesn't fire elsewhere (fc=2).
- The turnaround IS one of a+2's firings, not a separate event.

So the argument still works! a+2's two firings are the CW and CCW
traversals. The fact that it's a turnaround means those firings have
stay steps (if stay-BAF) or reversal (if pure-BAF) near them.

Let me verify this case computationally.
""")

    # Verify the adjacent-pair EC mechanism
    for n in [5, 7]:
        print(f"\n--- Verifying adjacent-pair EC at n = {n} ---")
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        all_ok = True
        for w in words:
            steps, cw, ccw, stay = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

            # Try the BAF arc mechanism:
            # For binary b interior to both arcs, with binary right(b):
            # mover_step = b's CCW firing
            # nonmover_step = right(b)'s CW firing (= step after b's CW firing)

            found = False
            for b in [0, 1, 2]:  # Binary procs
                if found: break
                rb = (b + 1) % n
                lb = (b - 1) % n

                if state_sizes[rb] > 2 and state_sizes[lb] > 2:
                    continue  # Need at least one binary neighbor

                b_fires = sorted([i for i in range(len(w)) if w[i] == b])
                assert len(b_fires) == 2

                # Try both orderings of b's fires
                for bfcw, bfccw in [(b_fires[0], b_fires[1]), (b_fires[1], b_fires[0])]:
                    # Check: at bfcw, does right(b) fire at bfcw+1 or nearby?
                    # And at bfccw, does right(b) fire at bfccw-1 or nearby?

                    # The actual check: between nonmover and mover step,
                    # count fires. We use nonmover = bfcw + 1 and mover = bfccw.
                    nms = (bfcw + 1) % len(w)
                    ms = bfccw

                    if w[nms] == b:
                        continue  # b fires at nonmover step, bad

                    # Count fires from config(nms) to config(ms)
                    if ms > nms:
                        interval = range(nms, ms)
                    else:
                        interval = list(range(nms, len(w))) + list(range(0, ms))

                    fires = Counter(w[i] for i in interval)
                    bf = fires.get(b, 0)
                    lbf = fires.get(lb, 0)
                    rbf = fires.get(rb, 0)

                    ec = (bf % state_sizes[b] == 0 and
                          lbf % state_sizes[lb] == 0 and
                          rbf % state_sizes[rb] == 0)

                    if ec:
                        found = True
                        print(f"  {step_str}: EC at b={b}, nms={nms}(w={w[nms]}), ms={ms}(w={w[ms]})")
                        print(f"    b={bf}, lb={lbf}, rb={rbf}")
                        break

                    # Try the other direction: nonmover = bfccw - 1, mover = bfcw
                    nms2 = (bfccw - 1) % len(w)
                    ms2 = bfcw

                    if w[nms2] == b:
                        continue

                    if ms2 > nms2:
                        interval2 = range(nms2, ms2)
                    else:
                        interval2 = list(range(nms2, len(w))) + list(range(0, ms2))

                    fires2 = Counter(w[i] for i in interval2)
                    bf2 = fires2.get(b, 0)
                    lbf2 = fires2.get(lb, 0)
                    rbf2 = fires2.get(rb, 0)

                    ec2 = (bf2 % state_sizes[b] == 0 and
                           lbf2 % state_sizes[lb] == 0 and
                           rbf2 % state_sizes[rb] == 0)

                    if ec2:
                        found = True
                        print(f"  {step_str}: EC(rev) at b={b}, nms={nms2}(w={w[nms2]}), ms={ms2}(w={w[ms2]})")
                        print(f"    b={bf2}, lb={lbf2}, rb={rbf2}")
                        break

            if not found:
                print(f"  FAILED: {w} {step_str}")
                # Try exhaustive at all procs
                ec_list = find_all_ec_pairs(w, n, state_sizes)
                if ec_list:
                    e = ec_list[0]
                    print(f"    But EC exists: proc={e['proc']}, ms={e['mover_step']}, "
                          f"nms={e['nonmover_step']}, fires=({e['b_fires']},{e['lb_fires']},{e['rb_fires']})")
                all_ok = False

        print(f"  Adjacent-pair BAF EC covers all: {all_ok}")

if __name__ == '__main__':
    main()
