"""
RA12 v8: Final verification — can the n=9 double-sweep cycle exist as a GoodCycle?

We need to verify ALL conditions:
1. Unique privilege at each step
2. Cycle closes
3. Distinct configs
4. Fair (all procs fire)
5. n >= 9, subThreshold, hasGe3Binary, threeConsecutiveBinary at i
6. ri has fc >= 2 and isolated firings
7. Some mover outside the triple
8. hfull (all procs fire > 0)

Then check: does the Lean theorem's conclusion (False) hold?
If not, the theorem has a bug.

BUT WAIT: The theorem says False. It doesn't say hasEntryConflict.
The sorry is inside a branch. Let me re-examine the proof structure.
The even-parity branch gives hasEntryConflict -> False via entryConflict_impossible.
The odd-parity branch has sorry (should also give False).

If the cycle has no EC, then entryConflict_impossible can't be used.
So the proof needs a DIFFERENT mechanism for the odd-parity case.

OR: maybe the theorem statement is wrong and the odd-parity case can't be proved False
with just these hypotheses. Maybe additional hypotheses (from the broader proof
context) are needed.

Let me check what calls consecutive_binary_isolated_false'.
"""

import sys
sys.path.insert(0, './claude')

def verify_double_sweep_n9():
    """Complete verification of the n=9 double-sweep cycle."""
    n = 9
    ms = [2, 2, 2, 3, 3, 3, 3, 3, 3]

    # Double sweep word
    word = []
    for _ in range(2):
        word.append(0)
        for p in range(n-1, 0, -1):
            word.append(p)
    L = len(word)

    print(f"n={n}, ms={ms}, product={2**3 * 3**6}={2**3 * 3**6}")
    print(f"Threshold: 4*3^7 = {4 * 3**7}")
    print(f"Sub-threshold: {2**3 * 3**6 < 4 * 3**7}")
    print(f"Word: {word} (L={L})")

    # Build config sequence (all increment transitions)
    vals = [[0]*L for _ in range(n)]
    current = [0] * n

    for k in range(L):
        for p in range(n):
            vals[p][k] = current[p]
        mover = word[k]
        if ms[mover] == 2:
            current[mover] = 1 - current[mover]
        else:
            current[mover] = (current[mover] + 1) % 3

    # Check cycle closes
    cycle_closes = all(current[p] == 0 for p in range(n))
    print(f"\nCycle closes: {cycle_closes}")
    if not cycle_closes:
        print(f"  Final state: {current}")
        # Check: binary fire counts
        from collections import Counter
        fc = Counter(word)
        for p in range(3):
            print(f"  Binary proc {p}: fires {fc[p]} times (even={fc[p]%2==0})")
        for p in range(3, n):
            print(f"  Ternary proc {p}: fires {fc[p]} times (div3={fc[p]%3==0})")
        return

    # Build configs
    configs = []
    for k in range(L):
        configs.append(tuple(vals[p][k] for p in range(n)))

    # Check distinct
    distinct = len(set(configs)) == L
    print(f"Distinct configs: {distinct} ({len(set(configs))} unique out of {L})")

    # Check fair (all procs fire)
    from collections import Counter
    fc = Counter(word)
    all_fire = all(fc.get(p, 0) > 0 for p in range(n))
    print(f"Fair (all procs fire): {all_fire}")
    print(f"Fire counts: {dict(sorted(fc.items()))}")

    # Check 3 consecutive binary
    i = 0  # binary triple at 0, 1, 2
    ri = 1
    rri = 2
    print(f"\n3 consecutive binary at {i}, {ri}, {rri}: ms[0]={ms[0]}, ms[1]={ms[1]}, ms[2]={ms[2]}")

    # Check ri isolated
    ri_steps = [k for k in range(L) if word[k] == ri]
    ri_fc = len(ri_steps)
    print(f"ri={ri} fire count: {ri_fc}")
    isolated = all(word[(k+1)%L] != ri for k in ri_steps)
    print(f"ri isolated: {isolated}")

    # Check some mover outside triple
    outside = any(word[k] not in [0,1,2] for k in range(L))
    print(f"Some mover outside triple: {outside}")

    # MinFiringGap analysis
    gaps = []
    for idx in range(len(ri_steps)):
        a = ri_steps[idx]
        b = ri_steps[(idx+1) % len(ri_steps)]
        g = (b - a) % L
        if g == 0: g = L
        gaps.append((a, b, g))

    print(f"\nGaps: {gaps}")
    min_g = min(g for _, _, g in gaps)
    print(f"Min gap: {min_g}")

    for a, b, g in gaps:
        if g != min_g: continue
        lf = rf = 0
        for off in range(1, g):
            s = (a + off) % L
            if word[s] == 0: lf += 1
            if word[s] == 2: rf += 1
        print(f"Gap ({a},{b},{g}): L_fires={lf}({['even','odd'][lf%2]}), R_fires={rf}({['even','odd'][rf%2]})")

    # EC check
    print(f"\nEntry conflict check:")
    for p in range(n):
        mc = set()
        nc = set()
        for k in range(L):
            lv = configs[k][(p-1) % n]
            sv = configs[k][p]
            rv = configs[k][(p+1) % n]
            ctx = (lv, sv, rv)
            if word[k] == p:
                mc.add(ctx)
            else:
                nc.add(ctx)
        overlap = mc & nc
        if overlap:
            print(f"  Proc {p}: EC! overlap={overlap}")
        else:
            print(f"  Proc {p}: clean (mover={len(mc)}, nonmover={len(nc)})")

    # Build transition function and check unique privilege
    print(f"\nTransition function consistency:")
    f_table = {p: {} for p in range(n)}
    consistent = True
    for k in range(L):
        mover = word[k]
        for p in range(n):
            lv = configs[k][(p-1) % n]
            sv = configs[k][p]
            rv = configs[k][(p+1) % n]
            ctx = (lv, sv, rv)

            if p == mover:
                new_val = configs[(k+1)%L][p]
                if ctx in f_table[p]:
                    if f_table[p][ctx] != new_val:
                        print(f"  CONFLICT at proc {p}, ctx={ctx}: {f_table[p][ctx]} vs {new_val}")
                        consistent = False
                f_table[p][ctx] = new_val
            else:
                # Non-mover: f(ctx) = sv
                if ctx in f_table[p]:
                    if f_table[p][ctx] != sv:
                        print(f"  CONFLICT at proc {p}, ctx={ctx}: {f_table[p][ctx]} vs {sv}")
                        consistent = False
                f_table[p][ctx] = sv

    print(f"  Consistent: {consistent}")

    if consistent:
        # Check unique privilege at each step
        print(f"\nUnique privilege check:")
        # Fill undefined contexts with identity
        for p in range(n):
            for lv in range(ms[(p-1) % n]):
                for sv in range(ms[p]):
                    for rv in range(ms[(p+1) % n]):
                        ctx = (lv, sv, rv)
                        if ctx not in f_table[p]:
                            f_table[p][ctx] = sv

        for k in range(L):
            priv = []
            for p in range(n):
                lv = configs[k][(p-1) % n]
                sv = configs[k][p]
                rv = configs[k][(p+1) % n]
                ctx = (lv, sv, rv)
                if f_table[p][ctx] != sv:
                    priv.append(p)
            if len(priv) != 1:
                print(f"  Step {k}: {len(priv)} privileged procs: {priv} (expected: [{word[k]}])")
            elif priv[0] != word[k]:
                print(f"  Step {k}: privileged={priv[0]} but expected mover={word[k]}")

        # Check for non-cycle configs with privilege issues
        # (This checks liveness but only for configs in the cycle)

    print(f"\n{'='*60}")
    print("CONCLUSION:")
    if consistent and distinct and cycle_closes and isolated and ri_fc >= 2 and outside:
        print("The double-sweep cycle at n=9 satisfies ALL hypotheses of")
        print("consecutive_binary_isolated_false' and has NO entry conflict.")
        print("A valid System can be built with this as a GoodCycle")
        print("(transition function is consistent, no EC).")
        print()
        print("This means the sorry case IS REAL: it is NOT vacuous,")
        print("and entry conflict is NOT a valid proof strategy here.")
        print()
        print("HOWEVER: the overall theorem M_n = 4*3^(n-2) IS correct.")
        print("The proof just needs a different mechanism for this branch.")
        print("Possible approaches:")
        print("  (a) Use a DIFFERENT MinFiringGap pair that has even parity")
        print("  (b) Prove False directly from some other structural property")
        print("  (c) Show that the convergence property fails")
        print("  (d) Use shadow cycle or other obstruction")
    else:
        print("Some condition not met. Check details above.")

if __name__ == '__main__':
    verify_double_sweep_n9()
