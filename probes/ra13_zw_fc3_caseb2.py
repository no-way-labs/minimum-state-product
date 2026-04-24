#!/usr/bin/env python3
"""
RA13: Deep dive into the single constant-fc case found at n=9.
Also: search harder for constant-fc cases at all sizes.
"""

from itertools import product as iterproduct
from collections import defaultdict
import random

random.seed(42)


def find_uniform_fc_cycles(ms, num=2000000, maxs=100):
    """Specifically search for constant-fc ZW cycles."""
    n = len(ms)
    all_c = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_c:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c); c2[p] = v
                    adj[c].append((tuple(c2), p))

    results = []
    unique = set()

    for _ in range(num):
        c = random.choice(all_c)
        vis = {c: 0}; path = [c]; mov = []
        for step in range(1, maxs):
            nb = adj[c]
            if not nb: break
            c, p = random.choice(nb)
            mov.append(p)
            if c in vis:
                s = vis[c]; cc = path[s:]; cm = mov[s:]; L = len(cm)
                if L < 2*n: break
                fc = defaultdict(int)
                for m in cm: fc[m] += 1
                if len(fc) < n or min(fc.values()) < 2: break
                cw = ccw = 0
                for i in range(L):
                    d = (cm[i] - cm[i-1]) % n
                    if d == 1: cw += 1
                    elif d == n-1: ccw += 1
                if cw != ccw or cw == 0: break
                if max(fc.values()) < 3: break

                fc_vals = [fc[q] for q in range(n)]
                if min(fc_vals) != max(fc_vals): break  # Only constant fc

                key = (cc[0], tuple(cm))
                if key in unique: break
                unique.add(key)
                results.append({'configs': cc, 'movers': cm, 'fc': dict(fc),
                               'length': L, 'cw': cw})
                break
            vis[c] = step; path.append(c)

    return results


def main():
    print("RA13: Constant fc deep search")
    print("=" * 60)

    for ms in [
        (2,2,2,2,2,2,2,2,2),  # n=9 all binary
        (2,2,2,2,2),           # n=5 all binary
        (2,2,2,2,2,2,2),      # n=7 all binary
    ]:
        n = len(ms)
        P = 2**n
        print(f"\nms={ms}, n={n}, P={P}")

        cycles = find_uniform_fc_cycles(ms, num=3000000, maxs=min(100, P))
        print(f"  Constant-fc ZW cycles found: {len(cycles)}")

        for cyc in cycles[:10]:
            fc = cyc['fc']
            movers = cyc['movers']
            L = len(movers)
            k = fc[0]
            print(f"\n  fc={k}, CL={L}, cw={cyc['cw']}")

            # Show phases at every proc
            disp_found = False
            disp_mechanism = None
            for q in range(n):
                fp = [i for i, m in enumerate(movers) if m == q]
                lq = (q-1)%n; rq = (q+1)%n
                phases = []
                for pi in range(len(fp)):
                    s2 = fp[pi]; e2 = fp[(pi+1)%len(fp)]
                    J = K = 0; pos = (s2+1)%L
                    while pos != e2:
                        if movers[pos] == lq: J += 1
                        if movers[pos] == rq: K += 1
                        pos = (pos+1)%L
                    phases.append((J, K))

                has_zero_j = any(J == 0 for J, K in phases)
                has_zero_k = any(K == 0 for J, K in phases)
                has_even_even = any(J%2==0 and K%2==0 and J+K>0 for J, K in phases)
                has_both_zero = any(J==0 and K==0 for J, K in phases)

                markers = []
                if has_both_zero: markers.append("both-zero")
                elif has_zero_j: markers.append("J=0")
                elif has_zero_k: markers.append("K=0")
                if has_even_even: markers.append("even-even")

                if markers and not disp_found:
                    disp_found = True
                    disp_mechanism = markers[0]

                print(f"    q={q}: {phases}  {' '.join(markers)}")

            print(f"    Mechanism: {disp_mechanism}")

            # Show mover walk
            print(f"    Movers: {list(movers)}")

    # Key question: for the uniform-fc cycle at n=9, WHY does it have zero-sided phase?
    # The walk structure forces it.
    print("\n" + "=" * 60)
    print("THEORETICAL ARGUMENT FOR CONSTANT fc CASE")
    print("=" * 60)
    print("""
When fc is constant = k (even ≥ 4):

Consider the mover walk as a sequence on Z_n.
CW + CCW = total ±1 steps. Stay/jump steps also exist.
ZW: CW = CCW > 0.

In a ±1 walk (no stay/jump): every step is either +1 or -1.
The walk visits each proc k times.

KEY OBSERVATION: In a ±1 walk on Z_n with ZW,
the walk has "turnaround points" where it switches from CW to CCW or vice versa.
At a turnaround: the mover stays at the same position or reverses.

Between turnarounds: the walk sweeps CW or CCW, visiting consecutive procs.
In a CW sweep from proc a to proc b: procs a, a+1, ..., b fire in order.
In a CCW sweep from b to a: procs b, b-1, ..., a fire in order.

If the walk bounces between turnaround points: the "boundary" procs
at turnaround points fire more (they fire at each turnaround).
Non-boundary procs fire fewer times.

For constant fc: ALL procs must fire equally. This requires the bouncing
to be very uniform. But with CW=CCW, the total CW displacement = total CCW
displacement. If the walk bounces between positions p and q:
each CW sweep covers |q-p| edges, each CCW sweep covers |q-p| edges.
Number of sweeps = CW / |q-p| = CCW / |q-p|.
But procs at p and q fire at every turnaround (twice per bounce),
while interior procs fire once per bounce. NOT uniform.

SO: constant fc REQUIRES the walk to NOT be a simple bounce.
It needs a more complex pattern.

But: the ±1 walk on Z_n with equal CW and CCW steps MUST have turnarounds.
At turnaround points, the walk direction reverses.
The proc at the turnaround fires TWICE in succession (or nearly).
This creates short phases (0 or 1 steps between fires) at those procs.
Short phases are more likely to have J=0 or K=0.

Specifically: if proc q fires at step t and again at step t+2
(one intermediate step by some other proc p), then the phase
between these two firings has length 1. Only one other proc fires.
If that proc is q-1: J=1, K=0 → dispatchable!
If that proc is q+1: J=0, K=1 → dispatchable!
If that proc is neither: J=0, K=0 → dispatchable!

So: ANY "short phase" (length 1-2) at any proc gives dispatchable.

For constant fc with k ≥ 4: CL = nk.
Average phase length = n-1 (plus the firing step).
Some phases are shorter, some longer.
With ZW turnarounds: the turnaround proc has a very short phase.

ACTUALLY: let's just check if every constant-fc cycle has a short phase.
""")


if __name__ == '__main__':
    main()
