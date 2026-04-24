#!/usr/bin/env python3
"""
Unified understanding of Case B: What characterizes words where Case A fails?

Case A fails when: for every pair (b, b+1) of adjacent binary procs,
the BAF step pair (i_CW+1, i_CCW) does NOT give EC.

This happens when at least one of b, b+1 fires with a stay step (not
a proper CW or CCW), OR when left(b) fires oddly in the interval.

KEY OBSERVATION: Case A fails exactly when BOTH binary procs 0 and 1
fire at turnaround steps, OR when binary procs 1 and 2 do. This means
the binary triple straddles the turnaround.

UNIFIED CASE B ARGUMENT: When Case A fails, the walk must have the
following structure near the binary triple {0,1,2}:

The walk traverses ALL of {3, 4, ..., n-1} in some direction (CW or CCW),
passes through {0,1,2} at the turnaround, and traverses back through
{3, 4, ..., n-1} in the opposite direction.

Because {3, 4, ..., n-1} are all traversed in BOTH directions:
- Proc 3 fires once going CW and once going CCW
- Proc 2 fires once going CW and once going CCW
- Between proc 2's CCW firing and proc 3's CW firing: only proc 2 (again),
  proc 1, and possibly proc 0 fire. Proc 2 fires exactly 2 times total.

THE UNIVERSAL PROPERTY: In any ZW fc=2 word where the binary triple
{0,1,2} is at the turnaround:
- Proc 3 has two firings: one CW, one CCW
- Proc 2 has two firings: one CW, one CCW
- The CW firing of proc 3 comes AFTER the CW firing of proc 2
- The CCW firing of proc 3 comes BEFORE the CCW firing of proc 2
- Between proc 2's first CCW firing and proc 3's CW firing:
  proc 3 fires 0 times, proc 2 fires 2 times, proc 4 fires 0 times
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


# THE REAL QUESTION: What property of the word tells us Case A fails?
# Answer: Case A fails when NO pair of adjacent binary procs BOTH fire
# with CW and CCW steps (at least one fires with stay or same-direction).

# But actually, the code checked: for b in {0,1} (adjacent binary pairs),
# does b fire CW once and CCW once? Let me check more carefully.

print("DETAILED Case A failure analysis:")

for n in [5, 7]:
    print(f"\nn = {n}")
    words = enumerate_zw_fc2(n)
    state_sizes = [2 if p < 3 else 3 for p in range(n)]

    for w in words:
        steps = classify_word(w, n)
        step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)

        # For each binary proc, classify its firing directions
        binary_info = {}
        for b in [0, 1, 2]:
            bf = sorted([i for i in range(len(w)) if w[i] == b])
            dirs = tuple(steps[i] for i in bf)
            binary_info[b] = (bf, dirs)

        # Case A needs: some b in {0,1} where b has (CW, CCW) or (CCW, CW)
        # AND right(b) = b+1 is binary (always true for b in {0,1})
        # AND the fire count in the interval works out.

        # Check if any binary proc fires CW and CCW (not stay)
        has_cw_ccw = {}
        for b in [0, 1, 2]:
            _, dirs = binary_info[b]
            has_cw_ccw[b] = (1 in dirs and -1 in dirs)

        # Case A requires: b and b+1 both have CW+CCW firings,
        # AND the interval fire counts work out.

        # If proc fires with stay (dir = 0), it's at the turnaround.
        has_stay = {b: 0 in binary_info[b][1] for b in [0, 1, 2]}

        # The "problem" words are where some binary proc fires with stay
        case_a_candidates = []
        for b in [0, 1]:  # Adjacent pairs {0,1} and {1,2}
            if has_cw_ccw[b] and has_cw_ccw[b+1]:
                case_a_candidates.append(b)

        if not case_a_candidates:
            print(f"  {step_str}: Case A fails. Binary dirs: "
                  f"p0={binary_info[0][1]}, p1={binary_info[1][1]}, p2={binary_info[2][1]}")
            print(f"    Has stay: p0={has_stay[0]}, p1={has_stay[1]}, p2={has_stay[2]}")
            print(f"    Has CW+CCW: p0={has_cw_ccw[0]}, p1={has_cw_ccw[1]}, p2={has_cw_ccw[2]}")

# KEY FINDING: Case A fails when one of {0,1} has a stay step.
# When p0 has stay: p0 fires at turnaround, (0,0) pair can't form BAF
# When p1 has stay: p1 fires at turnaround, both (0,1) and (1,2) disrupted

# But what about the Type3 word (0,1,...,n-1,0,n-1,...,1) which has NO stays?
# Let me check why Case A fails there.

print("\n\nType 3 (no-stay) failure analysis:")
for n in [5, 7]:
    w = tuple(list(range(n)) + [0] + list(range(n-1, 0, -1)))
    steps = classify_word(w, n)
    step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)
    state_sizes = [2 if p < 3 else 3 for p in range(n)]

    print(f"\nn={n}: {w}  {step_str}")
    for b in [0, 1, 2]:
        bf = sorted([i for i in range(len(w)) if w[i] == b])
        dirs = [steps[i] for i in bf]
        lb = (b - 1) % n
        rb = (b + 1) % n
        print(f"  proc {b}: fires at {bf}, dirs {dirs}")

        # For each ordering, check the interval
        for i_CW, i_CCW in [(bf[0], bf[1]), (bf[1], bf[0])]:
            if steps[i_CW] != 1 or steps[i_CCW] != -1:
                continue

            nms = (i_CW + 1) % len(w)
            ms = i_CCW

            if w[nms] == b:
                print(f"    i_CW={i_CW}, i_CCW={i_CCW}: nms={nms} has b firing (skip)")
                continue

            if ms > nms:
                interval = range(nms, ms)
            else:
                interval = list(range(nms, len(w))) + list(range(0, ms))

            fires = Counter(w[i] for i in interval)
            bf_count = fires.get(b, 0)
            lbf = fires.get(lb, 0)
            rbf = fires.get(rb, 0)

            print(f"    i_CW={i_CW}, i_CCW={i_CCW}: nms={nms}(w={w[nms]}), "
                  f"bf={bf_count}%{state_sizes[b]}={bf_count%state_sizes[b]}, "
                  f"lbf={lbf}%{state_sizes[lb]}={lbf%state_sizes[lb]}, "
                  f"rbf={rbf}%{state_sizes[rb]}={rbf%state_sizes[rb]}")

print("\n\nCONCLUSION:")
print("""
Case A fails for 3 word families, all characterized by the binary triple
{0,1,2} being at or near the turnaround of the walk:

Type 1 (Full-traverse): proc 0 fires CW+CCW, proc 1 fires CCW+CW,
  but left(0) = n-1 is ternary and fires odd times in the interval.

Type 2 (Stay-BAF): proc 0 fires with stay (turnaround), so it doesn't
  have a proper CW+CCW pair.

Type 3 (Full CW + Full CCW): ALL binary procs fire CW+CCW, but left(b)
  fires an odd number of times in every interval (because the walk
  traverses the ENTIRE ring, so left(b) fires once in between).

In ALL three cases, the EC is at proc 3 (ternary) with the SAME mechanism:
  mover_step: proc 3's CW firing
  nonmover_step: proc 2's first CCW firing
  Fire counts: proc3=0, proc2=2, proc4=0

This is the UNIFIED Case B argument.

The proof therefore has exactly TWO cases:
Case A: Some adjacent binary pair {b, b+1} gives BAF EC.
Case B: Binary triple at turnaround; EC at proc 3 via (0, 2, 0) mechanism.
""")

# FINAL VERIFICATION: at every n, do exactly 3 words need Case B?
print("\nWord counts by case:")
for n in [5, 7]:
    words = enumerate_zw_fc2(n)
    state_sizes = [2 if p < 3 else 3 for p in range(n)]

    case_a = 0
    case_b = 0
    for w in words:
        steps = classify_word(w, n)
        found_a = False
        for b in [0, 1]:
            bf = sorted([i for i in range(len(w)) if w[i] == b])
            if len(bf) != 2: continue
            rb = b + 1
            lb = (b - 1) % n
            for i_CW, i_CCW in [(bf[0], bf[1]), (bf[1], bf[0])]:
                if steps[i_CW] != 1 or steps[i_CCW] != -1: continue
                nms = (i_CW + 1) % len(w)
                if w[nms] == b: continue
                ms = i_CCW
                if ms > nms:
                    interval = range(nms, ms)
                else:
                    interval = list(range(nms, len(w))) + list(range(0, ms))
                fires = Counter(w[i] for i in interval)
                if (fires.get(b, 0) % 2 == 0 and
                    fires.get(lb, 0) % state_sizes[lb] == 0 and
                    fires.get(rb, 0) % 2 == 0):
                    found_a = True
                    break
            if found_a: break
        if found_a:
            case_a += 1
        else:
            case_b += 1

    print(f"  n={n}: {case_a} Case A, {case_b} Case B, {len(words)} total")
    print(f"    (Expected: {2*(n-1) - 3} Case A, 3 Case B, {2*(n-1)} total)")
    # At n=5: 10 words, 7 Case A, 3 Case B
    # At n=7: 14 words, 11 Case A, 3 Case B
    # Pattern: 2(n-1) total, 2(n-1)-3 Case A, 3 Case B
