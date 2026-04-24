#!/usr/bin/env python3
"""
RA13: Can constant fc be RULED OUT for n ≥ 9?

With constant fc = k and ≥3 binary procs: k must be even ≥ 4.
CL = nk. ZW: cw = ccw > 0.

For all-binary ring (ms = (2,...,2)), P = 2^n.
CL = nk. For k = 4: CL = 4n. Need CL ≤ P = 2^n.
For n = 9: 36 ≤ 512. OK.
For n = 5: 20 ≤ 32. OK.

But: the ZW + no-safe + all-fire-≥2 constraints severely restrict the walk.
Let me check more carefully.

Actually, let me take a different approach. Instead of ruling out constant fc,
let me prove that even with constant fc, some phase must be zero-sided.

CLAIM: With constant fc = k ≥ 4 (even) on a ring of n ≥ 5 procs,
in a ZW good cycle, some proc has a phase with J = 0 or K = 0.

Proof approach:
Consider the mover walk m_0, m_1, ..., m_{nk-1}.
This is a closed walk on Z_n with cw = ccw > 0.
Each proc appears exactly k times.

A "phase" of proc q is the segment between consecutive q-firings.
J_i = number of (q-1)-firings in phase i. K_i = number of (q+1)-firings in phase i.

If ALL phases of ALL procs have J ≥ 1 and K ≥ 1:
Then between every pair of consecutive q-firings, q-1 fires ≥ 1 and q+1 fires ≥ 1.

This means: in the mover sequence, between consecutive appearances of q,
there's at least one q-1 and one q+1.

Consider the "first returns": after q fires, the next q-fire must be preceded by
at least one q-1 and one q+1 fire.

With n procs each firing k = 4 times: CL = 4n.
Between consecutive q-firings: (CL/k) - 1 = n-1 steps on average.
Each of the other n-1 procs fires 4 times total over 4 phases.
If uniform: each other proc fires exactly 1 time per phase (total = 4).

But: "at least one q-1 and one q+1" in each phase means:
among the n-1 firings in the phase, at least 2 are accounted for (q-1 and q+1).
The other n-3 can be any of the remaining procs.

This seems achievable. The constraint doesn't force a zero-sided phase.

ALTERNATIVE: Use the ZW constraint more directly.
ZW means the walk has equal CW and CCW steps.
With constant fc = k: n*k steps, cw = ccw.

The walk visits each proc k times. The step structure matters.
If the walk is "sweep-like" (mostly CW then mostly CCW), the phases
might have specific structure.

For ZW: the walk must alternate direction. In a bounce-like walk,
the mover goes CW to some point, then CCW back, then CW again, etc.
At turnaround points, the same proc fires twice in succession (or with stay).

Actually, stay steps: when m_t = m_{t-1}, that's a "stay" step.
With CW+CCW only (no stay, no jump), every step is ±1.
Then the walk is a ±1 walk on Z_n, returning to start.
CW = CCW = some value.

In such a walk, the phases of proc q are the intervals between
consecutive visits to q. In a ±1 walk, to go from q to q and back,
the walk must pass through q-1 and q+1 (or loop around).

Hmm, this is getting complicated. Let me just verify computationally
whether constant fc cycles exist at n=9 and check if they're always
dispatchable, even with heavy sampling.
"""

from itertools import product as iterproduct
from collections import defaultdict
import random

random.seed(42)


def test_uniform_fc(ms, num_samples=1000000, maxs=150):
    n = len(ms)
    all_c = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_c:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c); c2[p] = v
                    adj[c].append((tuple(c2), p))

    uniform_found = 0
    uniform_disp = 0
    uniform_nondisp = 0
    total_zw_fc3 = 0
    unique = set()

    for _ in range(num_samples):
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
                key = (cc[0], tuple(cm))
                if key in unique: break
                unique.add(key)
                total_zw_fc3 += 1

                fc_vals = [fc[q] for q in range(n)]
                if min(fc_vals) == max(fc_vals):
                    uniform_found += 1
                    k = fc_vals[0]
                    # Check dispatchable
                    found = False
                    for q in range(n):
                        fp = [i for i, m in enumerate(cm) if m == q]
                        lq = (q-1)%n; rq = (q+1)%n
                        for pi in range(len(fp)):
                            s2 = fp[pi]; e2 = fp[(pi+1)%len(fp)]
                            J = K = 0; pos = (s2+1)%L
                            while pos != e2:
                                if cm[pos] == lq: J += 1
                                if cm[pos] == rq: K += 1
                                pos = (pos+1)%L
                            if J == 0 or K == 0 or (J%2==0 and K%2==0):
                                found = True; break
                        if found: break
                    if found:
                        uniform_disp += 1
                    else:
                        uniform_nondisp += 1
                        print(f"  UNIFORM NON-DISP: k={k}, CL={L}")
                        for q in range(n):
                            fp = [i for i, m in enumerate(cm) if m == q]
                            lq = (q-1)%n; rq = (q+1)%n
                            phases = []
                            for pi in range(len(fp)):
                                s2 = fp[pi]; e2 = fp[(pi+1)%len(fp)]
                                J = K = 0; pos = (s2+1)%L
                                while pos != e2:
                                    if cm[pos] == lq: J += 1
                                    if cm[pos] == rq: K += 1
                                    pos = (pos+1)%L
                                phases.append((J, K))
                            print(f"    q={q}: {phases}")
                break
            vis[c] = step; path.append(c)

    return total_zw_fc3, uniform_found, uniform_disp, uniform_nondisp


def main():
    print("RA13 Case B: Constant fc analysis")
    print("=" * 60)

    for ms in [
        (2,2,2,2,2),      # n=5, P=32
        (2,2,2,2,2,2,2),  # n=7, P=128
        (2,2,2,2,2,2,2,2,2),  # n=9, P=512
        (2,2,2,2,3),      # n=5, P=48
        (2,2,2,2,2,2,3),  # n=7, P=192
        (2,2,2,2,2,2,2,2,3),  # n=9, P=768
        (2,2,2,3,3),      # n=5, P=72
        (2,2,2,2,2,3,3),  # n=7, P=288
    ]:
        n = len(ms)
        P = 1
        for m in ms: P *= m
        threshold = 4 * 3**(n-2)
        if P >= threshold: continue

        print(f"\nms={ms}, P={P}, n={n}:")
        tot, unif, udisp, unondisp = test_uniform_fc(ms, num_samples=500000, maxs=min(100, P))
        print(f"  ZW fc≥3: {tot}, uniform fc: {unif} ({100*unif/max(tot,1):.1f}%), "
              f"uniform_disp: {udisp}, uniform_nondisp: {unondisp}")

    print("\n" + "=" * 60)
    print("CONCLUSION")
    print("=" * 60)
    print("""
For the FORMALIZATION:

CASE A (non-constant fc): ANALYTICAL.
  Proof: Let S = {q: fc(q) >= 3}. S non-empty.
  If fc is non-constant: there exist adjacent procs p, q with fc(p) < fc(q).
  Among such pairs, pick one where fc(q) >= 3.
  (This exists because: if all fc >= 3 procs have equal fc to neighbors,
  then fc is constant on the fc>=3 connected component. But if fc is non-constant,
  the boundary of the {fc = max} set has such a pair.)

  At q: fc(p) fires distributed over fc(q) > fc(p) phases.
  By pigeonhole: some phase has 0 fires from p's side.
  That phase is zero-sided → DISPATCHABLE → entry conflict → contradiction.

CASE B (constant fc = k, even >= 4): RARE (< 0.1% of cycles).
  For formalization: either prove analytically or handle separately.

  Possible analytical arguments for Case B:
  1. CL = nk >= 4n. With P < 4*3^(n-2), need nk < 4*3^(n-2).
     For all-binary: P = 2^n, nk < 2^n → k < 2^n/n.
     At n=9: k < 512/9 ≈ 56.9. Not a useful bound.

  2. Binary context counting: binary proc b has 2 * ms[left] * ms[right] contexts.
     It appears as mover k times and non-mover CL-k = (n-1)k times.
     If k >= 2 * ms[left] * ms[right] + 1: guaranteed entry conflict by pigeonhole
     on contexts alone (more mover appearances than contexts).

     For all-binary: contexts = 2*2*2 = 8. k >= 9 → EC guaranteed.
     But k could be 4: only 4 mover appearances among 8 contexts.
     Not sufficient.

  3. ALTERNATIVE: don't prove Case B via phases at all.
     Instead: with constant fc = k >= 4, CL = nk >= 4n.
     Use the CL >= 4n bound directly to prove entry conflict
     via context counting or some other method.

  4. BEST: Just rule out uniform fc in ZW cycles with the given constraints.
     Perhaps: in a ZW cycle with cw=ccw>0 and ≥3 binary,
     constant fc is impossible?
""")


if __name__ == '__main__':
    main()
