#!/usr/bin/env python3
"""
Zero-Winding Palindromic EC Proof — Phase 5 (Complete Proof)

The "full-traverse" word is the ONLY one that escapes binary BAF.
Structure: 0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1
Steps: R, L, L, ..., L, R, R, ..., R  (1 CW, n-1 CCW, turnaround, n-1 CW)

Actually wait -- let me recount. This word has proc 0 firing at steps 0 and 2,
proc 1 at steps 1 and 2n-1 (no, step 2n-1 wraps to step n-1+n = 2n-1).
Let me be precise.

For general n:
w = [0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1]
Length = 1 + 1 + (n-2) + (n-2) + 2 = 2n. Check.

Steps: 0->1 (CW), 1->0 (CCW), 0->n-1 (CCW), n-1->n-2 (CCW), ..., 2->1 (CCW),
       1->2 (CW), 2->3 (CW), ..., n-2->n-1 (CW), n-1->0 (CW, wrapping)

CW steps: [0->1], [1->2, 2->3, ..., n-2->n-1, n-1->0] = 1 + n = n+1? No...

Let me just count carefully.
"""

from collections import Counter

def classify_word(word, n):
    CL = len(word)
    steps = []
    for i in range(CL):
        nxt = word[(i + 1) % CL]
        cur = word[i]
        disp = (nxt - cur) % n
        if disp == 1: steps.append(+1)
        elif disp == n - 1: steps.append(-1)
        elif disp == 0: steps.append(0)
        else: steps.append(None)
    cw = sum(1 for s in steps if s == 1)
    ccw = sum(1 for s in steps if s == -1)
    stay = sum(1 for s in steps if s == 0)
    return steps, cw, ccw, stay


def full_traverse_word(n):
    """The problematic word: 0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1"""
    word = [0, 1, 0]
    for p in range(n-1, 1, -1):  # n-1, n-2, ..., 2
        word.append(p)
    for p in range(1, n):  # 1, 2, ..., n-1
        word.append(p)
    return tuple(word)


def analyze_full_traverse(n, binary_procs=[0,1,2]):
    """Detailed analysis of the full-traverse word."""
    w = full_traverse_word(n)
    CL = len(w)
    assert CL == 2*n

    steps, cw, ccw, stay = classify_word(w, n)
    step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

    print(f"\nn = {n}, CL = {CL}")
    print(f"Word: {list(w)}")
    print(f"Steps: {step_str} (CW={cw}, CCW={ccw}, Stay={stay})")

    # Fire positions for each proc
    fire_pos = {}
    for p in range(n):
        fire_pos[p] = [i for i in range(CL) if w[i] == p]
    print(f"\nFire positions:")
    for p in range(n):
        dirs = [steps[i] for i in fire_pos[p]]
        dir_str = ','.join({1:'CW',-1:'CCW',0:'S'}[d] for d in dirs)
        print(f"  proc {p}: steps {fire_pos[p]}, dirs [{dir_str}]")

    # Identify the structure
    print(f"\nWord structure (step by step):")
    for i in range(CL):
        d = {1:'CW',-1:'CCW',0:'STAY'}[steps[i]]
        nxt = w[(i+1)%CL]
        print(f"  step {i:2d}: mover={w[i]}, dir={d:4s} -> next mover={nxt}")

    # Now find the EC at ternary proc 3
    state_sizes = [2 if p in binary_procs else 3 for p in range(n)]
    print(f"\nState sizes: {state_sizes}")

    # For proc 3 (ternary, m=3):
    if n >= 5:
        b = 3
        lb = 2  # binary
        rb = 4  # ternary (if n > 5)
        b_fires = fire_pos[b]
        print(f"\nEC analysis at proc {b} (m={state_sizes[b]}):")
        print(f"  left = {lb} (m={state_sizes[lb]})")
        print(f"  right = {rb} (m={state_sizes[rb] if rb < n else '?'})")
        print(f"  b fires at: {b_fires}")

        # Check all (mover_step, nonmover_step) pairs at proc b
        for ms in b_fires:
            for nms in range(CL):
                if w[nms] == b: continue
                if ms > nms:
                    interval = range(nms, ms)
                else:
                    interval = list(range(nms, CL)) + list(range(0, ms))
                fires = Counter(w[i] for i in interval)
                bf = fires.get(b, 0)
                lbf = fires.get(lb, 0)
                rbf = fires.get(rb, 0)
                if (bf % state_sizes[b] == 0 and
                    lbf % state_sizes[lb] == 0 and
                    rbf % state_sizes[rb] == 0):
                    print(f"  EC: ms={ms}(dir={steps[ms]}), nms={nms}(mover={w[nms]}, dir={steps[nms]})")
                    print(f"    b_fires={bf}, lb_fires={lbf}, rb_fires={rbf}")
                    print(f"    Interval: steps {list(interval)}")
                    print(f"    Movers in interval: {[w[i] for i in interval]}")

    return w, steps, fire_pos, state_sizes


def main():
    print("=" * 70)
    print("FULL-TRAVERSE WORD: DETAILED EC MECHANISM")
    print("=" * 70)

    for n in [5, 7, 9]:
        analyze_full_traverse(n)

    # Now understand the GENERAL mechanism
    print(f"\n\n{'='*70}")
    print("GENERAL MECHANISM FOR FULL-TRAVERSE WORD")
    print("=" * 70)

    for n in range(5, 16):
        w = full_traverse_word(n)
        steps, cw, ccw, stay = classify_word(w, n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        # The EC at the full-traverse word:
        # Proc 3 fires at two specific steps. The nonmover step is where
        # proc 2 (binary) fires CCW.
        fire_pos = {}
        for p in range(n):
            fire_pos[p] = [i for i in range(len(w)) if w[i] == p]

        # Proc 2's fire positions and directions
        p2_fires = fire_pos[2]
        p2_dirs = [steps[i] for i in p2_fires]

        # Proc 3's fire positions and directions
        p3_fires = fire_pos[3]
        p3_dirs = [steps[i] for i in p3_fires]

        # Find the EC pair
        b = 3
        lb = 2
        rb = 4
        found = False
        for ms in p3_fires:
            for nms in range(len(w)):
                if w[nms] == b: continue
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
                    nms_mover = w[nms]
                    print(f"n={n:2d}: EC at b=3, ms={ms:2d}(dir={steps[ms]:+d}), "
                          f"nms={nms:2d}(mover={nms_mover},dir={steps[nms]:+d}), "
                          f"bf={bf}, lbf={lbf}, rbf={rbf}")
                    found = True
                    break
            if found: break

        if not found:
            print(f"n={n}: NO EC at proc 3!")

    # Now: what about the general case?
    # For the full-traverse word, proc 3 fires:
    # - During the CCW phase (going from n-1 down to 1): at step position n+1-3 = n-2
    #   (counting from step 2: 0->n-1 is step 2, n-1->n-2 is step 3, ..., 4->3 is step n-2)
    #   Wait, let me be precise.

    print(f"\n\nStep-by-step positions for proc 3:")
    for n in [5, 7, 9, 11]:
        w = full_traverse_word(n)
        p3 = [i for i in range(len(w)) if w[i] == 3]
        p2 = [i for i in range(len(w)) if w[i] == 2]
        p4 = [i for i in range(len(w)) if w[i] == 4] if n > 4 else []
        steps, _, _, _ = classify_word(w, n)
        print(f"  n={n}: proc3 fires at {p3}, dirs=[{steps[p3[0]]:+d},{steps[p3[1]]:+d}]")
        print(f"         proc2 fires at {p2}, dirs=[{steps[p2[0]]:+d},{steps[p2[1]]:+d}]")
        if p4:
            print(f"         proc4 fires at {p4}, dirs=[{steps[p4[0]]:+d},{steps[p4[1]]:+d}]")

    # The pattern: for the full-traverse word at general n:
    # Word structure: [0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1]
    # Positions:
    #   step 0: mover 0
    #   step 1: mover 1
    #   step 2: mover 0  (second firing of 0)
    #   step 3: mover n-1
    #   step 4: mover n-2
    #   ...
    #   step 3 + (n-1-k): mover k  for k = n-1, n-2, ..., 2
    #   step 3 + (n-3): mover 2  => step n
    #   step n+1: mover 1  (second firing of 1)

    # Wait: w = [0, 1, 0, n-1, n-2, ..., 2, 1, 2, 3, ..., n-1]
    # Index 0: 0
    # Index 1: 1
    # Index 2: 0
    # Index 3: n-1
    # Index 4: n-2
    # ...
    # Index 3+(n-1-k): k for k=n-1,...,2
    # When k=2: index = 3 + (n-1-2) = n
    # Index n: 2
    # Index n+1: 1
    # Wait, the CCW phase goes: 0, n-1, n-2, ..., 2, 1
    # Starting from index 2: 0
    # Index 3: n-1
    # Index 4: n-2
    # ...
    # Index 2+(n-1-k) = n+1-k: k for k from n-1 down to 1
    # When k=1: index = n+1-1 = n: mover = 1? No, let me recount.

    # w[2] = 0, w[3] = n-1, w[4] = n-2, ..., w[2+j] = n-1-(j-1) = n-j for j=1,...,n-2
    # w[2+(n-2)] = w[n] = n-(n-2) = 2
    # Then: w[n+1] = 1 (continuing CCW from 2)
    # Then CW phase: w[n+2] = 2, w[n+3] = 3, ..., w[n+2+j] = j+2 for j=0,...,n-3
    # w[n+2+(n-3)] = w[2n-1] = n-1

    # So positions:
    # Proc 0: steps 0, 2
    # Proc 1: steps 1, n+1
    # Proc 2: steps n, n+2
    # Proc 3: steps n-1, n+3
    # Proc k (2 <= k <= n-1): steps n+2-k (CCW), n+k (CW)
    # Proc n-1: steps 3, 2n-1

    print(f"\n\nVerifying position formulas:")
    for n in [5, 7, 9, 11]:
        w = full_traverse_word(n)
        print(f"\nn={n}:")
        for p in range(n):
            actual = [i for i in range(len(w)) if w[i] == p]
            if p == 0:
                predicted = [0, 2]
            elif p == 1:
                predicted = [1, n+1]
            elif 2 <= p <= n-1:
                predicted = [n+2-p, n+p]
            else:
                predicted = None

            match = sorted(actual) == sorted(predicted) if predicted else False
            print(f"  proc {p}: actual={actual}, predicted={predicted}, match={match}")

    # So the EC pair for proc 3:
    # Proc 3 fires at steps n-1 (CCW) and n+3 (CW)
    # The EC nonmover step is at step n-1-1 = n-2, where mover is proc 2 (CCW)
    # Wait, we found EC with mover_step = n+3-n+n = ... let me just check directly.

    print(f"\n\nEC pair verification for full-traverse:")
    for n in [5, 7, 9, 11, 13, 15]:
        w = full_traverse_word(n)
        steps_w, _, _, _ = classify_word(w, n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        # Proc 3 fires at n-1 (CCW) and n+3 (CW)
        ccw_step = n - 1  # step n-1: mover = 3, direction CCW
        cw_step = n + 3   # step n+3: mover = 3, direction CW

        # EC pair 1: ms = cw_step (proc 3 fires CW), nms = ?
        # We need: between nms and ms, proc 3 fires 0 mod 3 times,
        # proc 2 fires 0 mod 2, proc 4 fires 0 mod 3.

        # The key pair found computationally:
        # ms = cw_step = n+3, nms = ccw_step - 2 = n-3
        # Let me check: between config(n-3) and config(n+3):
        # Steps n-3, n-2, n-1, n, n+1, n+2
        # Movers: w[n-3], w[n-2], w[n-1], w[n], w[n+1], w[n+2]
        # = proc(n+2-(n-3))=5, proc(n+2-(n-2))=4, proc 3, proc 2, proc 1, proc 2
        # Wait, I should use the formula: w[n+2-k] = k for k=2,...,n-1
        # So w[n-3] = n+2-(n-3) = 5? Only valid for n >= 5.

        # Let me just use the actual word
        if cw_step < len(w) and ccw_step < len(w):
            # Try nms = n-3 (the step where proc 5 fires, for n=9)
            # Actually, the EC pair found was: ms=n+3-n+..., nms=n-3+...
            # Let me just search
            b = 3
            lb = 2
            rb = 4
            found = False
            for ms in [cw_step, ccw_step]:
                for nms in range(len(w)):
                    if w[nms] == b: continue
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
                        print(f"n={n:2d}: ms={ms:2d}(w[ms]={w[ms]},d={steps_w[ms]:+d}), "
                              f"nms={nms:2d}(w[nms]={w[nms]},d={steps_w[nms]:+d}), "
                              f"bf={bf}, lbf={lbf}, rbf={rbf}, "
                              f"nms_formula=n-1+{nms-(n-1)} or n+3+{nms-(n+3)}")
                        found = True
                        break
                if found: break
            if not found:
                print(f"n={n}: NO EC at proc 3!")


if __name__ == '__main__':
    main()
