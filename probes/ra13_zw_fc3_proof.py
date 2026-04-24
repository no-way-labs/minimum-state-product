#!/usr/bin/env python3
"""
RA13: Clean proof verification for fc≥3 → contradiction in ZW cycles.

THEOREM: In a zero-winding good cycle with cwStepCount > 0, no safe processor,
sub-threshold product (< 4·3^(n-2)), ≥3 binary, n ≥ 9, and convergent,
no processor q can have fc(q) ≥ 3.

PROOF STRUCTURE:
1. All procs fire ≥ 2 times (already proved).
2. Binary procs have even fc (they cycle through {0,1}, must return to start).
   So binary fc ∈ {2, 4, 6, ...}.
3. If some q has fc(q) ≥ 3:
   a. Consider the set S = {p : fc(p) ≥ 3} (non-empty).
   b. Consider the set B = {p : ms[p] = 2} (|B| ≥ 3, binary procs).
   c. Since fc is even for binary: binary procs in S have fc ≥ 4.
   d. Binary procs NOT in S have fc = 2 (only even value in {2,3,...} that's < 3).

   KEY STEP: Find a proc t ∈ S with a neighbor u ∉ S (i.e., fc(u) = 2).

   CLAIM: Such a pair (t, u) always exists when S ≠ {0,...,n-1}.
   Proof: S is a proper subset of {0,...,n-1} (since |B| ≥ 3 and binary procs
   have fc ≥ 2, if all binary have fc ≥ 4, that's at least 3*4=12 extra firings,
   but let's not assume). Actually:
   - If S = {0,...,n-1}: every proc fires ≥ 3 times. CL ≥ 3n.
     But we only need S ≠ all procs. Can S = all procs?
     Only if every proc fires ≥ 3, including binary (fc ≥ 4).
     CL ≥ 4*|B| + 3*(n-|B|) = 3n + |B| ≥ 3n + 3.
     This is possible (CL can be up to P).

   - If S is a proper subset: S has a boundary. Some t ∈ S has neighbor u ∉ S.
     fc(t) ≥ 3, fc(u) = 2 (or fc(u) < 3, so fc(u) = 2 since fc ≥ 2).
     Pigeonhole applies: fc(u) = 2 fires distributed over fc(t) ≥ 3 phases of t.
     Some phase has 0 fires from u-side → phase is (0, K) or (J, 0) → dispatchable.

   - If S = {0,...,n-1}: EVERY proc fires ≥ 3. All binary fire ≥ 4.
     CL ≥ 4*3 + 3*(n-3) = 3n + 3.

     But wait: even if S = all procs, we can still use pigeonhole!
     Find a proc t with fc(t) < fc(neighbor). Or more precisely:
     fc values vary. The MINIMUM fc in S determines things.

     Actually, the smarter argument:
     Binary procs have fc ≥ 4 (even, ≥ 3 → ≥ 4).
     Non-binary procs have fc ≥ 3.
     Consider a non-binary proc t adjacent to a binary proc b.
     Such t exists because ≥3 binary procs means ≥2 binary-nonbinary boundaries
     (unless ALL procs are binary, but n ≥ 9 with product < 4·3^7 = 8748,
     and all-binary product = 2^9 = 512 < 8748, so this is possible).

     If ALL procs are binary: n ≥ 9, all ms[p] = 2, product = 2^n.
     fc even for all. fc ≥ 3 → fc ≥ 4 for all.
     CL ≥ 4n ≥ 36.

     Wait, but we assumed ≥3 binary, not all binary. If all binary, that's ≥3 binary. OK.

     Case: not all binary (some ternary+).
     There exists a non-binary proc t adjacent to binary proc b.
     If fc(t) ≥ 3: fc(t) ≥ 3, fc(b) ≥ 4 (even). Not necessarily fc(b) < fc(t).
     If fc(t) = 3 and fc(b) = 4: fc(b) > fc(t), pigeonhole DOES NOT apply at t.
     Hmm.

     But: at t, J = fc(left(t)), K = fc(right(t)), over fc(t) = 3 phases.
     If b = left(t): J = fc(b) ≥ 4, over 3 phases.
     ALL phases have J ≥ 1 (in fact, one phase has J ≥ 2).
     K = fc(right(t)), over 3 phases.
     If right(t) is binary: K even ≥ 4. All phases have K ≥ 1, one has K ≥ 2.
     Parity: sum J = fc(b) = 4 = even. Over 3 phases, even number of odd-J phases.
     Could be (2,1,1) or (2,2,0) or (4,0,0) or (1,1,2) etc.
     (2,2,0): phase with K=? and J=0 → dispatchable!
     (2,1,1): J=(2,1,1). The J=2 phase: if K=even → even-even → dispatchable.
     (1,1,2): similar.

     Actually J's sum to 4 over 3 phases. Can we avoid J=0 entirely?
     Yes: (1,1,2) or (1,2,1) or (2,1,1) all work.
     But parity: sum = 4 (even), 3 phases. Even number of odd-J phases = 0 or 2.
     If 0 odd-J: all even. (2,2,0) — contains 0! Or (4,0,0) — contains 0!
     Or (2,0,2) — contains 0!
     If 2 odd-J: (1,1,2) — no zero. Or (1,3,0) — contains 0.

     So: with sum = 4 (even) and 3 phases, either some J=0 (dispatchable)
     or all J ≥ 1 with exactly 2 odd values.

     When all J ≥ 1: (1,1,2) type. The even-J phase has J = 2 (or 4, etc).
     At that phase: J even, K = ?. If K also even → even-even → dispatchable!
     K's over 3 phases sum to fc(right). If fc(right) is even:
     even number of odd-K phases. If the even-J phase also has even K:
     DISPATCHABLE.

     Can we force the even-J phase to have odd K?
     Sum K = even. Even number of odd-K phases (0 or 2).
     If 0 odd-K: all K even. Every phase has K even.
       The phase with J even: both even → even-even → DISPATCHABLE.
     If 2 odd-K: 2 phases have odd K, 1 has even K.
       The even-J phases: there's 1 even-J phase. The even-K phases: 1.
       Could be the same phase → DISPATCHABLE.
       Could be different phases → the even-J phase has odd K, and
       the even-K phase has odd J. Then no even-even phase.
       But: the even-J phase has J even. Not J=0 (since all J≥1).
       The odd-K: K odd ≥ 1.
       So this phase has (J_even≥2, K_odd≥1). Not zero-sided, not even-even.

       The even-K phase has odd J. (J_odd≥1, K_even≥2). Also not dispatchable.
       The third phase has odd J, odd K. Not dispatchable.

       THIS IS A GAP. If right neighbor also has even fc, we can have
       a non-dispatchable cycle!

     Wait, but what is fc(right(t))? If right(t) is also binary: fc even.
     So we're in the case: t is non-binary with BOTH neighbors binary.
     This requires t to be surrounded by binary procs.

     HOWEVER: for this "no even-even" scenario:
     J phases = (1, 1, 2), K phases = (1, 2, 1) [or permutation].
     Phase 0: (1, 1) — odd-odd
     Phase 1: (1, 2) — odd-even
     Phase 2: (2, 1) — even-odd
     No phase is both-even!

     But: can this actually occur? Let me check computationally.

     Actually, this exactly matches the non-dispatchable example from Part 1:
     ms=(2, 2, 3, 2, 2), q=2, fc(q)=3, phases=[(1, 1), (2, 1), (1, 2)]
     J sum = 4 = fc(left=1) = binary fc 4. K sum = 4 = fc(right=3) = binary fc 4.
     ALL 3 phases have J≥1 AND K≥1. No phase with J=0 or K=0.
     Phase (1,1): both odd → not even-even.
     Phase (2,1): J=2 even, K=1 odd → not even-even.
     Phase (1,2): J=1 odd, K=2 even → not even-even.
     NOT DISPATCHABLE at this proc!

     So the claim "fc≥3 → dispatchable phase at that proc" is FALSE.
     But the cycle DOES have an entry conflict (verified 100%).

     The dispatchable phase must be found at a DIFFERENT proc.
     From Part 4: 100% of cycles have a dispatchable phase at SOME fc≥3 proc.

REVISED STRATEGY: We don't need every fc≥3 proc to be dispatchable.
We need: if fc(q) ≥ 3 for SOME q, then SOME proc has a dispatchable phase.

Actually, re-reading the task: we need fc(q) ≥ 3 for SOME q → False.
The entry conflict can be at ANY proc, not just q.

Let me verify: in the non-dispatchable case ms=(2,2,3,2,2), q=2, fc(2)=3,
what are the fc values of ALL procs? And where is the dispatchable phase?
"""

from itertools import product as iterproduct, permutations
from collections import defaultdict
import random

random.seed(42)


def classify_step(prev, curr, n):
    d = (curr - prev) % n
    if d == 1: return 'cw'
    elif d == n-1: return 'ccw'
    elif d == 0: return 'stay'
    else: return 'jump'


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


def find_cycles(ms, all_c, adj, num=500000, maxs=80):
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
                if key not in unique:
                    unique[key] = {'configs': cc, 'movers': cm, 'fc': dict(fc), 'length': L}
                break
            vis[c] = step; path.append(c)
    return list(unique.values())


def get_phases(movers, q, n):
    L = len(movers)
    fire_pos = [i for i, m in enumerate(movers) if m == q]
    if not fire_pos: return []
    left = (q-1) % n; right = (q+1) % n
    phases = []
    for pi in range(len(fire_pos)):
        s = fire_pos[pi]; e = fire_pos[(pi+1)%len(fire_pos)]
        J = K = 0
        pos = (s+1) % L
        while pos != e:
            if movers[pos] == left: J += 1
            if movers[pos] == right: K += 1
            pos = (pos+1) % L
        phases.append((J, K))
    return phases


def is_dispatchable_phase(J, K):
    if J == 0 or K == 0: return True
    if J % 2 == 0 and K % 2 == 0: return True
    return False


def main():
    print("=" * 70)
    print("RA13: Proof Verification — WHERE is the dispatchable phase?")
    print("=" * 70)

    # Focus on the hard case: ms with ternary proc between 2 binary procs
    # and fc=3 at that ternary proc

    ms_cases = [
        (2, 2, 3, 2, 2),  # The known non-dispatchable case at q=2
    ]

    for ms in ms_cases:
        n = len(ms)
        print(f"\nms = {ms}")
        all_c, adj = build_adj(ms)
        cycles = find_cycles(ms, all_c, adj, num=500000)
        print(f"ZW fc≥3 cycles found: {len(cycles)}")

        for cyc in cycles[:20]:
            fc = cyc['fc']
            # Only look at cases where q=2 has fc≥3
            if fc.get(2, 0) < 3:
                continue

            print(f"\n  CL={cyc['length']}, fc={fc}")

            # Check phases at every proc
            for q in range(n):
                if fc.get(q, 0) < 2:
                    continue
                phases = get_phases(cyc['movers'], q, n)
                has_disp = any(is_dispatchable_phase(J, K) for J, K in phases)
                marker = " <-- DISPATCHABLE" if has_disp else ""
                fc_q = fc[q]
                left = (q-1) % n; right = (q+1) % n
                print(f"    q={q} (ms={ms[q]}): fc={fc_q}, "
                      f"L_fc={fc.get(left,0)}, R_fc={fc.get(right,0)}, "
                      f"phases={phases}{marker}")

    # Now: broader analysis. For ALL ZW fc≥3 cycles, find WHERE the
    # dispatchable phase is.
    print("\n" + "=" * 60)
    print("BROAD ANALYSIS: Where is the dispatchable phase?")
    print("=" * 60)

    for n in [5]:
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

        total = 0
        disp_at_fc3 = 0  # Dispatchable at some fc≥3 proc
        disp_at_fc2_only = 0  # Dispatchable only at fc=2 procs (not at any fc≥3)
        no_disp_anywhere = 0

        # Where exactly?
        disp_at_binary_fc_ge4 = 0
        disp_at_ternary_binary_adj = 0
        disp_at_ternary_ternary_adj = 0

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted: P *= m
            if P > 1500: continue

            seen = set(); pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen: continue
                seen.add(perm); pc += 1
                if pc > 30: break
                ms = perm
                all_c, adj = build_adj(ms)
                cycles = find_cycles(ms, all_c, adj, num=300000)

                for cyc in cycles:
                    fc = cyc['fc']
                    fc3_procs = {q for q in range(n) if fc.get(q,0) >= 3}
                    total += 1

                    # Check each fc≥3 proc for dispatchable
                    found_at_fc3 = False
                    for q in fc3_procs:
                        phases = get_phases(cyc['movers'], q, n)
                        if any(is_dispatchable_phase(J, K) for J, K in phases):
                            found_at_fc3 = True
                            break

                    if found_at_fc3:
                        disp_at_fc3 += 1
                    else:
                        # Check: is ANY fc≥3 proc adjacent to a proc with fc < fc_q?
                        # The dispatchable phase might be at a non-fc≥3 proc...
                        # Actually, we need the dispatchable phase at an fc≥3 proc
                        # for the phase_dispatch_ec to apply.
                        # Let's check if there's a DIFFERENT fc≥3 proc with dispatchable.
                        disp_at_fc2_only += 1

                    # Also check: entry conflict at any proc
                    # (already verified 100% in Part 4)

        print(f"\nn={n}: {total} ZW fc≥3 cycles")
        print(f"  Dispatchable at some fc≥3 proc: {disp_at_fc3}")
        print(f"  No dispatchable at any fc≥3 proc: {disp_at_fc2_only}")

    # KEY THEORETICAL INSIGHT
    print("\n" + "=" * 60)
    print("KEY INSIGHT: GRADIENT ARGUMENT")
    print("=" * 60)
    print("""
The fc≥3 set S has a BOUNDARY in the ring.
At the boundary: some t ∈ S has neighbor u ∉ S with fc(u) = 2.
fc(u) = 2 < 3 ≤ fc(t) → pigeonhole at t.
2 fires of u distributed over ≥3 phases of t → some phase has 0 from u.
That phase: (0, K) or (J, 0) → dispatchable.

BUT: What if S = {0,...,n-1}? Then every proc has fc ≥ 3.
Binary procs have fc ≥ 4 (even ≥ 3 → ≥ 4).

With all binary procs having fc ≥ 4:
CL ≥ 4*|B| + 3*(n-|B|) = 3n + |B| ≥ 3n + 3.

Now: consider a binary proc b with fc(b) = 4.
Phases: 4 phases. J = fc(left(b)), K = fc(right(b)).
Both ≥ 3.

J sum ≥ 3 over 4 phases. Can avoid J=0: (1,1,1,0) — no! has 0.
(1,1,1,0) has J=0. To avoid: all J≥1 needs J sum ≥ 4.
If J sum = 3 < 4 = fc(b): pigeonhole → some J=0 → DISPATCHABLE.

If J sum = fc(left(b)) ≥ 4: pigeonhole doesn't apply.
But fc(left(b)) ≥ 4 means left(b) fires ≥ 4 times.

KEY: binary proc b has fc = 4. If its binary neighbor b' has fc = 4:
fc(b') = 4 distributed over 4 phases of b.
Can all phases have J ≥ 1? Yes: (1,1,1,1).
K = fc(right(b)) distributed over 4 phases. Same issue.

Parity: fc(b') = 4 = even. Over 4 phases. Even number of odd-J phases.
Could be (1,1,1,1) — all odd, 4 odd = even. OK.
K similar. All phases (1,1) — ALL odd-odd.

So: the non-dispatchable case extends to S = all procs!

HOWEVER: CL = sum fc. With all fc ≥ 3, binary fc ≥ 4:
CL ≥ 4·|B| + 3·(n-|B|) = 3n + |B|.
With all procs having fc = 3 (ternary) or 4 (binary):
CL = 4·|B| + 3·(n-|B|) = 3n + |B|.
With all procs fc = 4 (if all binary): CL = 4n.

Number of distinct configs = CL ≤ P = product of ms.
For all binary n=9: CL ≥ 4·9 = 36, P = 512. Fine.

So the phases-only argument HAS A GAP when S = all procs.

Need a different approach for S = all procs.
""")


if __name__ == '__main__':
    main()
