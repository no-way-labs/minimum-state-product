#!/usr/bin/env python3
"""Quick check: which words are Case B (not Case A)?"""

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
    return steps, cw, ccw

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

def verify_case_a(word, n, state_sizes):
    CL = len(word)
    steps, _, _ = classify_word(word, n)
    binary_procs = [p for p in range(n) if state_sizes[p] == 2]

    for b in binary_procs:
        rb = (b + 1) % n
        lb = (b - 1) % n
        if state_sizes[rb] != 2:
            continue

        b_fires = sorted([i for i in range(CL) if word[i] == b])
        if len(b_fires) != 2: continue

        for i_CW, i_CCW in [(b_fires[0], b_fires[1]), (b_fires[1], b_fires[0])]:
            if steps[i_CW] != 1 or steps[i_CCW] != -1:
                continue

            nms = (i_CW + 1) % CL
            ms = i_CCW
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
                return True
    return False

for n in [5, 7]:
    words = enumerate_zw_fc2(n)
    state_sizes = [2 if p < 3 else 3 for p in range(n)]
    print(f"\nn = {n}:")
    for w in words:
        ok_a = verify_case_a(w, n, state_sizes)
        if not ok_a:
            steps, cw, ccw = classify_word(w, n)
            step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)
            # Find which binary procs are at turnaround
            # Check direction of each binary proc's firings
            info = []
            for b in [0, 1, 2]:
                bf = sorted([i for i in range(len(w)) if w[i] == b])
                dirs = [steps[bf[0]], steps[bf[1]]]
                info.append(f"p{b}:{dirs}")

            print(f"  Case B: {w}  {step_str}  {', '.join(info)}")

# Check: are ALL Case B words just rotations/reflections of the full-traverse?
print(f"\n\nFull-traverse word variants:")
for n in [5, 7]:
    w0 = list(range(n)) + list(range(n-1, 0, -1))  # Not a valid fc=2 word
    # The full-traverse: 0,1,0,n-1,...,2,1,2,...,n-1
    ft = [0, 1, 0]
    for p in range(n-1, 1, -1): ft.append(p)
    for p in range(1, n): ft.append(p)
    ft = tuple(ft)

    # All rotations
    rots = set()
    for i in range(len(ft)):
        rots.add(tuple(ft[i:] + ft[:i]))
    # All reflections
    ft_rev = tuple(reversed(ft))
    for i in range(len(ft_rev)):
        rots.add(tuple(ft_rev[i:] + ft_rev[:i]))

    # Canonical forms
    canonicals = set()
    for r in rots:
        all_rots = [tuple(r[i:] + r[:i]) for i in range(len(r))]
        canonicals.add(min(all_rots))

    print(f"\nn={n}: Full-traverse canonical forms: {len(canonicals)}")
    for c in sorted(canonicals):
        steps, cw, ccw = classify_word(c, n)
        step_str = ''.join({1:'R',-1:'L',0:'S',None:'?'}[s] for s in steps)
        print(f"  {c}  {step_str}")
