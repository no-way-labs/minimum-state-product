#!/usr/bin/env python3
"""
Generalized Case B: prove that when Case A fails, proc 3 always has EC.

THE GENERAL ARGUMENT (not word-specific):

Assumption: Case A fails. This means for EVERY pair (b, b+1) of adjacent
binary procs in {0,1,2}, the standard BAF step pair does NOT give EC.

We prove: the walk must have a specific structure near proc 3 that
always gives EC at proc 3.

THE KEY STRUCTURAL FACT:
In any ZW fc=2 word, proc 2 and proc 3 each fire exactly twice.
Since they're adjacent on the ring, and the walk is a closed walk where
each step moves to an adjacent proc or stays:

Proc 3's two firings are ordered in the word. Between them, proc 2 fires
some number of times (0, 1, or 2). Similarly, proc 4 fires some number of
times between proc 3's firings.

For EC at proc 3: we need some nonmover step and mover step at proc 3 where:
  proc 3 fires 0 times between them (ALWAYS: we pick one firing of proc 3
  as the mover step, and a step between proc 3's firings as the nonmover step)
  proc 2 fires 0 mod 2 between them (need: 0 or 2)
  proc 4 fires 0 mod state_size(4) between them

The question: can we ALWAYS find such a pair?

CLAIM: In any ZW fc=2 word where Case A fails, between proc 3's CW firing
and CCW firing (in the "short" direction), proc 2 fires exactly 2 times
and proc 4 fires 0 times.

Let me verify this claim exhaustively.
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
    return steps


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


def is_case_a(word, n, state_sizes):
    """Check if Case A (binary BAF EC) applies."""
    CL = len(word)
    steps = classify_word(word, n)

    for b in [0, 1]:  # Adjacent binary pairs
        rb = b + 1
        lb = (b - 1) % n
        bf = sorted([i for i in range(CL) if word[i] == b])
        if len(bf) != 2: continue

        for i_CW, i_CCW in [(bf[0], bf[1]), (bf[1], bf[0])]:
            if steps[i_CW] != 1 or steps[i_CCW] != -1:
                continue
            nms = (i_CW + 1) % CL
            if word[nms] == b: continue
            ms = i_CCW
            if ms > nms:
                interval = range(nms, ms)
            else:
                interval = list(range(nms, CL)) + list(range(0, ms))
            fires = Counter(word[i] for i in interval)
            if (fires.get(b, 0) % state_sizes[b] == 0 and
                fires.get(lb, 0) % state_sizes[lb] == 0 and
                fires.get(rb, 0) % state_sizes[rb] == 0):
                return True
    return False


def main():
    print("=" * 70)
    print("GENERAL CASE B ANALYSIS")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        for w in words:
            if is_case_a(w, n, state_sizes):
                continue

            CL = len(w)
            steps = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

            # Proc 3 fires at two positions
            p3_fires = sorted([i for i in range(CL) if w[i] == 3])
            # Proc 2 fires at two positions
            p2_fires = sorted([i for i in range(CL) if w[i] == 2])
            # Proc 4 fires at two positions
            p4_fires = sorted([i for i in range(CL) if w[i] == 4]) if n > 4 else []

            # Two intervals between proc 3's firings:
            f1, f2 = p3_fires
            # Interval A: [f1+1, f2-1]
            # Interval B: [f2+1, f1-1] (wrapping)

            intA = list(range(f1+1, f2))
            intB = list(range(f2+1, CL)) + list(range(0, f1))

            moversA = [w[i] for i in intA]
            moversB = [w[i] for i in intB]

            p2_in_A = sum(1 for m in moversA if m == 2)
            p2_in_B = sum(1 for m in moversB if m == 2)
            p4_in_A = sum(1 for m in moversA if m == 4)
            p4_in_B = sum(1 for m in moversB if m == 4)

            print(f"\n  {step_str}")
            print(f"    proc 3 fires at {p3_fires}")
            print(f"    Interval A [{f1+1}..{f2-1}]: movers={moversA}")
            print(f"      proc 2 fires {p2_in_A} times, proc 4 fires {p4_in_A} times")
            print(f"    Interval B [{f2+1}..{f1-1}]: movers={moversB}")
            print(f"      proc 2 fires {p2_in_B} times, proc 4 fires {p4_in_B} times")

            # For EC at proc 3 using interval A:
            # Need p3=0, p2=0 mod 2, p4=0 mod state_sizes[4]
            ec_a = (p2_in_A % 2 == 0 and p4_in_A % state_sizes[4 % n] == 0)
            # For EC at proc 3 using interval B:
            ec_b = (p2_in_B % 2 == 0 and p4_in_B % state_sizes[4 % n] == 0)

            print(f"    EC via interval A: p2%2={p2_in_A%2}, p4%{state_sizes[4%n]}={p4_in_A%state_sizes[4%n]} => {'EC' if ec_a else 'no'}")
            print(f"    EC via interval B: p2%2={p2_in_B%2}, p4%{state_sizes[4%n]}={p4_in_B%state_sizes[4%n]} => {'EC' if ec_b else 'no'}")

            # But WHICH interval? We need the nonmover step to be a step where
            # proc 2 (or someone else) fires, not proc 3.
            # In interval A: proc 3 doesn't fire (it fires at f1 and f2, both outside).
            # So any step in interval A has proc 3 as non-mover.
            # The mover step is f2 (proc 3 fires).
            # Actually: EC needs mover at f2, nonmover at any step in A where
            # proc 3 is NOT the mover. But all steps in A have different movers.
            # The nonmover step can be ANY step in A where proc 3 is non-mover,
            # which is ALL steps in A (since proc 3 doesn't fire in A).

            # WAIT: I need to be more careful. The EC comparison is between
            # config(nms) and config(ms). The config at step ms is the config
            # BEFORE proc 3 fires at step f2. For EC:
            # - nms must be in the interval [f1+1, f2-1] (interval A) if ms = f2
            #   OR nms must be in [f2+1, f1-1] (interval B) if ms = f1
            # - Between config(nms) and config(ms), fire counts must be 0 mod m.

            # For ms = f2, nms in interval A:
            # Steps that fire from config(nms) to config(f2): nms, nms+1, ..., f2-1.
            # That's a SUFFIX of interval A.
            # But we already know proc 3 fires 0 times in A, and proc 2 fires p2_in_A
            # times in the FULL interval A.

            # For the EC to work, we need the SUFFIX from nms to have the right parities.
            # We found computationally that nms = proc 2's CCW firing step works.
            # In the suffix from nms to f2: proc 2 fires at nms (included) and maybe
            # at one more position. If proc 2 fires at nms and one more time before f2:
            # total = 2, which is even.

            # Let me verify: which nms gives EC?
            for ms in [f1, f2]:
                for nms_check in (intA if ms == f2 else intB):
                    if ms > nms_check:
                        check = range(nms_check, ms)
                    else:
                        check = list(range(nms_check, CL)) + list(range(0, ms))
                    fires = Counter(w[i] for i in check)
                    bf = fires.get(3, 0)
                    lbf = fires.get(2, 0)
                    rbf = fires.get(4 % n, 0)
                    if (bf % state_sizes[3] == 0 and
                        lbf % state_sizes[2] == 0 and
                        rbf % state_sizes[4 % n] == 0):
                        print(f"    EC FOUND: ms={ms}(d={steps[ms]:+d}), nms={nms_check}(mover={w[nms_check]},d={steps[nms_check]:+d})")
                        print(f"      fires: p3={bf}, p2={lbf}, p4={rbf}")
                        print(f"      movers in interval: {[w[i] for i in check]}")
                        break
                else:
                    continue
                break

    # THE ANALYTICAL ARGUMENT:
    print(f"\n\n{'='*70}")
    print("ANALYTICAL ARGUMENT: WHY CASE B ALWAYS WORKS")
    print("=" * 70)
    print("""
When Case A fails, the walk must have ALL of procs {0,1,2} near the
turnaround. This means the walk traverses the "long arc" {3, 4, ..., n-1}
in BOTH directions (CW and CCW), with the turnaround happening in the
{0,1,2} region.

STRUCTURAL CONSEQUENCE: Between proc 3's two firings, the walk passes
through the {0,1,2} region. In this passage:
- Proc 2 fires exactly twice (once going toward 0, once coming back)
- Proc 0 fires (at the turnaround)
- Proc 1 fires
- Proc 4 does NOT fire (it's on the other side of the long arc)

This gives the fire counts (0, 2, 0) for (proc3, proc2, proc4) in the
interval between proc 3's firings.

PROOF THAT PROC 2 FIRES EXACTLY TWICE:
Since fc(2) = 2 total and proc 2 fires once in each pass of the long arc,
between proc 3's two firings, proc 2 fires exactly 2 times.

PROOF THAT PROC 4 FIRES 0 TIMES:
Proc 4 is adjacent to proc 3 on the ring (right(3) = 4). In the walk,
proc 4 fires in the SAME arc as proc 3 (the long arc side), not in the
turnaround region. So proc 4's firings are on the OUTER side of proc 3's
firings, not between them.

More precisely: In the CW pass of the long arc, the walk goes
..., 3, 4, 5, ..., n-1 (or reverse). Proc 3 fires BEFORE proc 4 in the
CW pass, and AFTER proc 4 in the CCW pass. So proc 4's two firings are
OUTSIDE the interval between proc 3's firings.

FORMAL STEP INDICES:
Let f3_CCW = proc 3's CCW firing step, f3_CW = proc 3's CW firing step.
Let f2_CCW = proc 2's first firing (in the interval), f2_CW = proc 2's
second firing (in the interval).

The interval from f2_CCW to f3_CW contains steps where proc 2 fires at
f2_CCW and f2_CW, proc 1 fires once, proc 0 fires twice (at turnaround).
But only proc 2 matters for EC at proc 3.

NONMOVER STEP: nms = f2_CCW (proc 2 fires, proc 3 is non-mover)
MOVER STEP: ms = f3_CW (proc 3 fires CW)

Between config(nms = f2_CCW) and config(ms = f3_CW):
  Steps: f2_CCW, f2_CCW+1, ..., f3_CW - 1
  Proc 3 fires: 0 times (both firings are outside)
  Proc 2 fires: 2 times (at f2_CCW and f2_CW, both inside)
  Proc 4 fires: 0 times (both firings are outside)

2 mod 2 = 0 for binary proc 2.
0 mod m_4 = 0 for proc 4 (any state size).

EC AT PROC 3: same (L, S, R) context at mover step and non-mover step.
""")


if __name__ == '__main__':
    main()
