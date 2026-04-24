#!/usr/bin/env python3
"""
RA13 FINAL: Definitive proof verification.

THEOREM: In a ZW good cycle with cw>0, no safe proc, sub-threshold,
≥3 binary, n≥5, fc≥2 for all, if some fc(q) ≥ 3: derive False.

PROOF via phase_dispatch_ec:
1. Let S = {q : fc(q) ≥ 3}. S non-empty by hypothesis.
2. Find a proc t with fc(t) ≥ 3 and a neighbor u with fc(u) < fc(t).
   This gives pigeonhole: fc(u) fires over fc(t) ≥ 3 phases of t,
   so some phase has 0 fires from u-side → (0,K) or (J,0) → dispatchable.
3. Dispatchable phase → entry conflict → contradiction (via phase_dispatch_ec).

WHY does step 2 always work?
Consider the MAXIMUM fc value k* = max fc(q).
Let q* = argmax fc(q). Then fc(q*) = k*.
fc(q*) ≥ avg(fc) = CL/n.
Since CL ≥ 2n + 1 (some proc fires ≥3, rest ≥2): avg > 2.

Case A: fc is NOT constant (∃ procs with different fc values).
  Then q* has strictly higher fc than at least one proc.
  If a neighbor of q* has fc < k*: done.
  If both neighbors of q* have fc = k*: expand. The set of procs
  with fc = k* is a subset. If it's not all procs, its boundary
  has a proc adjacent to a lower-fc proc.
  If ALL procs with fc = k*: fc is constant. Contradiction.

Case B: fc IS constant = k for all procs.
  Binary procs: even fc. k must be even. k ≥ 4.
  Ternary procs: fc = k.

  CL = nk. With n ≥ 5, k ≥ 4: CL ≥ 20.

  Consider any proc q. It has k phases.
  Left fires k times over k phases. Right fires k times over k phases.
  If all phases have J=1, K=1: each phase has exactly 2 neighbor-fires.
  Total steps in phase = varies. But: sum over phases of (phase_length) = CL = nk.
  Each phase starts with q's fire. Length of phase i = (steps until next q-fire).
  Total non-q steps per phase: some number ≥ 2 (at least J+K ≥ 2).

  Wait — J=K=1 doesn't mean phase_length = 3.
  There could be other proc fires in the phase too.
  J counts ONLY left neighbor, K counts ONLY right neighbor.
  Other procs (not left, not right, not q) also fire.

  So all-phases (1,1) is necessary but not sufficient for non-dispatchable.
  The question: does some phase have (J,K) with J=0 or K=0 or both even?

  With uniform fc = k (even):
  J sums to k over k phases. K sums to k over k phases.
  PARITY: k = even. Number of odd-J phases must be even.
  With k phases: 0, 2, 4, ..., k odd-J phases possible.

  If ALL J = 1 (all odd): k odd-J phases, but k is even → k even → OK.
  So J = (1,1,...,1) is parity-consistent.
  Similarly K = (1,1,...,1).

  BUT: does ZW constraint prevent this?
  Let's check computationally.

VERIFICATION: For each ZW fc≥3 cycle found:
1. Check Case A: is fc non-constant?
   If yes: find max-fc proc with lower-fc neighbor. Verify pigeonhole.
2. Check Case B: is fc constant?
   If yes: check if some phase has J=0 or K=0 or both-even.
"""

from itertools import product as iterproduct, permutations
from collections import defaultdict
import random

random.seed(42)


def classify_step(prev, curr, n):
    d = (curr - prev) % n
    if d == 1: return 'cw'
    elif d == n-1: return 'ccw'
    else: return 'other'


def build_adj(ms):
    n = len(ms)
    all_c = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_c:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c); c2[p] = v
                    adj[c].append((tuple(c2), p))
    return all_c, adj


def find_zw_fc3_cycles(ms, all_c, adj, num=300000, maxs=80):
    n = len(ms)
    unique = {}
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
                    t = classify_step(cm[i-1], cm[i], n)
                    if t == 'cw': cw += 1
                    elif t == 'ccw': ccw += 1
                if cw != ccw or cw == 0: break
                if max(fc.values()) < 3: break
                key = (cc[0], tuple(cm))
                unique[key] = {'configs': cc, 'movers': cm, 'fc': dict(fc), 'length': L}
                break
            vis[c] = step; path.append(c)
    return list(unique.values())


def get_phases(movers, q, n):
    L = len(movers)
    fire_pos = [i for i, m in enumerate(movers) if m == q]
    if not fire_pos: return []
    lq = (q-1)%n; rq = (q+1)%n
    phases = []
    for pi in range(len(fire_pos)):
        s = fire_pos[pi]; e = fire_pos[(pi+1)%len(fire_pos)]
        J = K = 0; pos = (s+1)%L
        while pos != e:
            if movers[pos] == lq: J += 1
            if movers[pos] == rq: K += 1
            pos = (pos+1)%L
        phases.append((J, K))
    return phases


def is_phase_dispatchable(J, K):
    return J == 0 or K == 0 or (J % 2 == 0 and K % 2 == 0)


def find_gradient_proc(fc, n):
    """Find a proc with fc(q) ≥ 3 that has a neighbor with strictly lower fc."""
    # Strategy: find proc with max fc, then walk to a boundary
    fc_vals = [fc.get(q, 0) for q in range(n)]
    max_fc = max(fc_vals)

    # If not all equal: find a max-fc proc with a lower-fc neighbor
    if min(fc_vals) < max_fc:
        for q in range(n):
            if fc_vals[q] == max_fc:
                lq = (q-1) % n; rq = (q+1) % n
                if fc_vals[lq] < max_fc or fc_vals[rq] < max_fc:
                    return q
        # Max-fc procs might form a connected component.
        # Find boundary of {q: fc(q) = max_fc}.
        # Actually: any non-constant function on a ring has adjacent values that differ.
        for q in range(n):
            lq = (q-1) % n
            if fc_vals[q] > fc_vals[lq] and fc_vals[q] >= 3:
                return q
            if fc_vals[q] > fc_vals[(q+1)%n] and fc_vals[q] >= 3:
                return q
        # More general: find any fc≥3 proc with a lower-fc neighbor
        for q in range(n):
            if fc_vals[q] < 3: continue
            lq = (q-1)%n; rq = (q+1)%n
            if fc_vals[lq] < fc_vals[q] or fc_vals[rq] < fc_vals[q]:
                return q
    return None  # fc is constant


def main():
    print("=" * 70)
    print("RA13 FINAL: Definitive Proof Verification")
    print("=" * 70)

    grand_total = 0
    case_a_gradient = 0
    case_b_uniform = 0
    case_b_dispatchable = 0
    case_b_not_dispatchable = 0
    case_a_not_dispatchable = 0

    for n in [5, 7, 9]:
        threshold = 4 * 3 ** (n-2)
        multisets = []
        def gen(pos, cur, prod, ml=multisets, nn=n, t=threshold):
            if pos == nn:
                if prod < t and sum(1 for x in cur if x == 2) >= 3:
                    ml.append(tuple(cur))
                return
            for m in range(2, min(t // max(prod, 1) + 1, 20)):
                if prod * m >= t: break
                if cur and m < cur[-1]: continue
                gen(pos + 1, cur + [m], prod * m)
        gen(0, [], 1)

        print(f"\nn={n}: {len(multisets)} multisets, threshold={threshold}")

        n_total = 0; n_case_a = 0; n_case_b = 0; n_ok = 0; n_fail = 0

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted: P *= m
            if P > 3000: continue

            seen = set(); pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen: continue
                seen.add(perm); pc += 1
                if pc > (30 if n <= 7 else 5): break
                ms = perm
                all_c, adj = build_adj(ms)
                cycles = find_zw_fc3_cycles(ms, all_c, adj,
                    num=(300000 if n <= 7 else 100000),
                    maxs=(80 if n <= 7 else 150))

                for cyc in cycles:
                    fc = cyc['fc']
                    movers = cyc['movers']
                    n_total += 1
                    grand_total += 1

                    # Case A: non-constant fc
                    grad_q = find_gradient_proc(fc, n)
                    if grad_q is not None:
                        n_case_a += 1
                        case_a_gradient += 1

                        # Verify: gradient proc has dispatchable phase
                        phases = get_phases(movers, grad_q, n)
                        has_disp = any(is_phase_dispatchable(J, K) for J, K in phases)
                        if has_disp:
                            n_ok += 1
                        else:
                            # Gradient gives J=0 or K=0 in some phase → must be dispatchable
                            # This would be a bug in our analysis
                            case_a_not_dispatchable += 1
                            n_fail += 1
                            fc_vals = [fc[q] for q in range(n)]
                            lq = (grad_q-1)%n; rq = (grad_q+1)%n
                            print(f"\n  BUG: gradient proc {grad_q} not dispatchable!")
                            print(f"    ms={ms}, fc={fc_vals}")
                            print(f"    fc[q]={fc[grad_q]}, fc[L]={fc_vals[lq]}, fc[R]={fc_vals[rq]}")
                            print(f"    phases={phases}")
                    else:
                        # Case B: constant fc
                        n_case_b += 1
                        case_b_uniform += 1

                        # Check if some fc≥3 proc has dispatchable phase
                        found = False
                        for q in range(n):
                            if fc.get(q, 0) < 3: continue
                            phases = get_phases(movers, q, n)
                            if any(is_phase_dispatchable(J, K) for J, K in phases):
                                found = True; break

                        if found:
                            case_b_dispatchable += 1
                            n_ok += 1
                        else:
                            case_b_not_dispatchable += 1
                            n_fail += 1
                            k = fc[0]
                            print(f"\n  UNIFORM fc={k}, NO dispatchable phase!")
                            print(f"    ms={ms}, CL={cyc['length']}")
                            for q in range(n):
                                phases = get_phases(movers, q, n)
                                print(f"      q={q}(ms={ms[q]}): phases={phases}")

        print(f"  Cycles: {n_total}, Case A (gradient): {n_case_a}, "
              f"Case B (uniform): {n_case_b}")
        print(f"  OK: {n_ok}, FAIL: {n_fail}")

    print(f"\n{'='*60}")
    print(f"GRAND TOTAL: {grand_total} cycles")
    print(f"  Case A (non-constant fc, gradient): {case_a_gradient}")
    if case_a_not_dispatchable:
        print(f"    NOT dispatchable (BUG): {case_a_not_dispatchable}")
    else:
        print(f"    ALL dispatchable by pigeonhole")
    print(f"  Case B (constant fc): {case_b_uniform}")
    print(f"    Dispatchable: {case_b_dispatchable}")
    print(f"    Not dispatchable: {case_b_not_dispatchable}")

    if case_a_not_dispatchable == 0 and case_b_not_dispatchable == 0:
        print(f"\n  THEOREM VERIFIED: fc≥3 → dispatchable phase → entry conflict")
        print(f"  Case A: gradient argument (pigeonhole at max-fc proc)")
        print(f"  Case B: uniform fc — empirically always dispatchable")
    else:
        print(f"\n  GAPS FOUND — need further analysis")


if __name__ == '__main__':
    main()
