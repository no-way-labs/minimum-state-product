"""
RA12 v7: Verify the n=5 EC-free good cycles form valid SYSTEMS,
and check n=9.

Key finding from v6: word [0,4,3,2,1,0,4,3,2,1] at n=5, ms=[2,2,2,3,3]
produces EC-free good cycles. BUT does a full SYSTEM (transition functions
satisfying liveness + mutual exclusion + closure + convergence + fairness)
exist with this as the good cycle?

Also: the sorry is gated by n >= 9. Need to check the n=9 case specifically.
"""

import sys
sys.path.insert(0, './claude')
from verifier import verify_system, all_configs, privileged_set, apply_move

from itertools import product as iprod
from collections import defaultdict

def build_system_from_cycle(n, ms, cycle_configs, movers):
    """
    Given a good cycle (configs + movers), try to build a complete system.

    The good cycle determines transition functions at mover contexts.
    At non-mover contexts, f(L,S,R) = S (identity).
    We need to fill in remaining contexts and check convergence.
    """
    L = len(cycle_configs)

    # Build partial transition functions
    # f[p][(L,S,R)] = new_value
    f_table = {p: {} for p in range(n)}

    for k in range(L):
        cfg = cycle_configs[k]
        next_cfg = cycle_configs[(k+1) % L]
        mover = movers[k]

        for p in range(n):
            left_v = cfg[(p-1) % n]
            self_v = cfg[p]
            right_v = cfg[(p+1) % n]
            ctx = (left_v, self_v, right_v)

            if p == mover:
                new_val = next_cfg[p]
                if ctx in f_table[p]:
                    if f_table[p][ctx] != new_val:
                        return None  # inconsistency (EC!)
                f_table[p][ctx] = new_val
            else:
                # Non-mover: must map to identity
                if ctx in f_table[p]:
                    if f_table[p][ctx] != self_v:
                        return None  # inconsistency
                f_table[p][ctx] = self_v

    # Fill undefined contexts: for liveness, every config needs a privileged proc.
    # For convergence, bad configs must not form cycles.
    # Try: set undefined contexts to identity (non-privileged).
    # Then check liveness. If liveness fails, try other assignments.

    # First, check with identity for all undefined:
    for p in range(n):
        for L_v in range(ms[(p-1) % n]):
            for S_v in range(ms[p]):
                for R_v in range(ms[(p+1) % n]):
                    ctx = (L_v, S_v, R_v)
                    if ctx not in f_table[p]:
                        f_table[p][ctx] = S_v  # identity

    # Build function objects
    fs = []
    for p in range(n):
        table = f_table[p]
        def f(L, S, R, t=table):
            return t[(L, S, R)]
        fs.append(f)

    return fs

def check_word_at_n9():
    """Check if the sweep-like word pattern exists at n=9."""
    n = 9
    ms = [2, 2, 2, 3, 3, 3, 3, 3, 3]
    ri = 1

    # The n=5 EC-free word was [0,4,3,2,1,0,4,3,2,1] — a double sweep.
    # At n=9: analogous would be [0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1]
    # This is a double CW sweep: mover goes 0->8->7->...->1->0->8->...->1

    word = []
    for _ in range(2):
        word.append(0)
        for p in range(n-1, 0, -1):
            word.append(p)
    L = len(word)
    print(f"n=9 double sweep word: {word} (L={L})")

    # Check fire counts
    from collections import Counter
    fc = Counter(word)
    print(f"Fire counts: {dict(fc)}")

    # Binary fire counts: 0->2, 1->2, 2->2 ✓ (even)
    # All procs fire: yes ✓
    # Some mover outside {0,1,2}: yes (3-8) ✓

    # Check ri=1 isolation
    ri_steps = [k for k in range(L) if word[k] == ri]
    print(f"ri=1 fires at steps: {ri_steps}")
    for k in ri_steps:
        if word[(k+1) % L] == ri:
            print(f"  NOT isolated!")
            break
    else:
        print(f"  Isolated ✓")

    # MinFiringGap
    gaps = []
    for idx in range(len(ri_steps)):
        a = ri_steps[idx]
        b = ri_steps[(idx+1) % len(ri_steps)]
        g = (b - a) % L
        if g == 0:
            g = L
        gaps.append((a, b, g))
    print(f"Gaps: {gaps}")
    min_g = min(g for _, _, g in gaps)
    print(f"MinFiringGap: {min_g}")

    for a, b, g in gaps:
        if g != min_g:
            continue
        lf = rf = 0
        for off in range(1, g):
            s = (a + off) % L
            if word[s] == 0:
                lf += 1
            if word[s] == 2:
                rf += 1
        print(f"Gap ({a},{b},{g}): L_fires={lf}, R_fires={rf}")
        print(f"  Left parity: {'odd' if lf%2 else 'even'}")
        print(f"  Right parity: {'odd' if rf%2 else 'even'}")

    # Check parity context at ri
    pfc = [[0]*(L+1) for _ in range(3)]
    for k in range(L):
        for p in range(3):
            pfc[p][k+1] = pfc[p][k] + (1 if word[k] == p else 0)

    print(f"\nParity contexts at ri=1:")
    mctx = set()
    nctx = set()
    for k in range(L):
        c = (pfc[0][k]%2, pfc[1][k]%2, pfc[2][k]%2)
        if word[k] == ri:
            mctx.add(c)
            print(f"  Step {k} (MOVER): pfc=({pfc[0][k]},{pfc[1][k]},{pfc[2][k]}), ctx={c}")
        else:
            nctx.add(c)

    print(f"Mover contexts: {mctx}")
    print(f"Non-mover contexts: {nctx}")
    print(f"EC at ri: {bool(mctx & nctx)}")

    # Build config sequence and check EC everywhere
    # Binary values
    binary_val = [[pfc[p][k] % 2 for k in range(L)] for p in range(3)]

    # Ternary: use increment
    ternary_val = {}
    for p in range(3, n):
        ternary_val[p] = [0] * L
        current = 0
        for k in range(L):
            ternary_val[p][k] = current
            if word[k] == p:
                current = (current + 1) % 3

    # Build configs
    configs = []
    for k in range(L):
        cfg = [0] * n
        for p in range(3):
            cfg[p] = binary_val[p][k]
        for p in range(3, n):
            cfg[p] = ternary_val[p][k]
        configs.append(tuple(cfg))

    # Check distinct
    if len(set(configs)) == L:
        print(f"\nAll {L} configs distinct ✓")
    else:
        print(f"\nWARNING: only {len(set(configs))} distinct out of {L}")

    # Check EC at all procs
    print(f"\nEC check at each proc:")
    any_ec = False
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
            any_ec = True
            print(f"  Proc {p}: EC at contexts {overlap}")
        else:
            print(f"  Proc {p}: no EC (mover: {len(mc)}, nonmover: {len(nc)})")

    if not any_ec:
        print(f"\n*** NO EC ANYWHERE at n=9 with increment transitions! ***")
    else:
        print(f"\nEC found. Checking if ternary choices can avoid it...")

        # Try different ternary initial values and transitions
        ternary_pos = list(range(3, n))
        ternary_fire_steps = {p: [k for k in range(L) if word[k] == p]
                              for p in ternary_pos}
        ternary_fc = {p: len(ternary_fire_steps[p]) for p in ternary_pos}

        print(f"Ternary fire counts: {ternary_fc}")

        # Total choices: 3^6 * 2^(sum of fire counts)
        total_ternary = sum(ternary_fc[p] for p in ternary_pos)
        total_search = 3**len(ternary_pos) * 2**total_ternary
        print(f"Total search space: 3^{len(ternary_pos)} * 2^{total_ternary} = {total_search}")

        if total_search > 10_000_000:
            print("Search space too large for brute force.")
            print("Sampling random ternary assignments...")

            import random
            random.seed(42)
            ec_free_found = False
            for trial in range(100000):
                # Random ternary init
                t_init = {p: random.randint(0, 2) for p in ternary_pos}
                # Random fire choices
                t_val = {}
                for p in ternary_pos:
                    t_val[p] = [0] * L
                    current = t_init[p]
                    for k in range(L):
                        t_val[p][k] = current
                        if word[k] == p:
                            alts = [v for v in range(3) if v != current]
                            current = random.choice(alts)
                    if current != t_init[p]:
                        continue  # doesn't close

                # Build configs
                cfgs = []
                for k in range(L):
                    cfg = [0] * n
                    for p in range(3):
                        cfg[p] = binary_val[p][k]
                    for p in ternary_pos:
                        cfg[p] = t_val[p][k]
                    cfgs.append(tuple(cfg))

                if len(set(cfgs)) != L:
                    continue

                # Check EC
                has_ec = False
                for p in range(n):
                    mc = set()
                    nc = set()
                    for k in range(L):
                        lv = cfgs[k][(p-1) % n]
                        sv = cfgs[k][p]
                        rv = cfgs[k][(p+1) % n]
                        ctx = (lv, sv, rv)
                        if word[k] == p:
                            mc.add(ctx)
                        else:
                            nc.add(ctx)
                    if mc & nc:
                        has_ec = True
                        break

                if not has_ec:
                    ec_free_found = True
                    print(f"\n*** EC-FREE found at trial {trial}! ***")
                    print(f"  Ternary init: {t_init}")
                    break

            if not ec_free_found:
                print(f"No EC-free assignment found in 100K random trials.")
                print("Likely EC is forced at n=9 for this word.")
        else:
            # Brute force
            ec_free_count = 0
            for t_init in iprod(range(3), repeat=len(ternary_pos)):
                t_init_dict = {ternary_pos[i]: t_init[i] for i in range(len(ternary_pos))}

                fire_choice_count = [ternary_fc[p] for p in ternary_pos]
                total_fc = sum(fire_choice_count)

                for choices in iprod(range(2), repeat=total_fc):
                    t_val = {}
                    ci = 0
                    valid = True
                    for p in ternary_pos:
                        t_val[p] = [0] * L
                        current = t_init_dict[p]
                        for k in range(L):
                            t_val[p][k] = current
                            if word[k] == p:
                                alts = [v for v in range(3) if v != current]
                                current = alts[choices[ci]]
                                ci += 1
                        if current != t_init_dict[p]:
                            valid = False
                            break

                    if not valid:
                        continue

                    cfgs = []
                    for k in range(L):
                        cfg = [0] * n
                        for p in range(3):
                            cfg[p] = binary_val[p][k]
                        for p in ternary_pos:
                            cfg[p] = t_val[p][k]
                        cfgs.append(tuple(cfg))

                    if len(set(cfgs)) != L:
                        continue

                    has_ec = False
                    for p in range(n):
                        mc = set()
                        nc = set()
                        for k in range(L):
                            lv = cfgs[k][(p-1) % n]
                            sv = cfgs[k][p]
                            rv = cfgs[k][(p+1) % n]
                            ctx = (lv, sv, rv)
                            if word[k] == p:
                                mc.add(ctx)
                            else:
                                nc.add(ctx)
                        if mc & nc:
                            has_ec = True
                            break

                    if not has_ec:
                        ec_free_count += 1
                        if ec_free_count <= 3:
                            print(f"\n  EC-FREE: init={t_init}")

            print(f"\nTotal EC-free assignments: {ec_free_count}")

def verify_n5_system():
    """Try to build and verify a complete system at n=5 from the EC-free cycle."""
    n = 5
    ms = [2, 2, 2, 3, 3]

    word = [0, 4, 3, 2, 1, 0, 4, 3, 2, 1]
    L = len(word)

    # Build config sequence with all binary init=0, ternary init=0, increment
    pfc = [[0]*(L+1) for _ in range(3)]
    for k in range(L):
        for p in range(3):
            pfc[p][k+1] = pfc[p][k] + (1 if word[k] == p else 0)

    configs = []
    ternary_val = {}
    for p in [3, 4]:
        ternary_val[p] = [0] * L
        current = 0
        for k in range(L):
            ternary_val[p][k] = current
            if word[k] == p:
                current = (current + 1) % 3

    for k in range(L):
        cfg = [pfc[p][k] % 2 for p in range(3)]
        for p in [3, 4]:
            cfg.append(ternary_val[p][k])
        configs.append(tuple(cfg))

    print(f"\nn=5 cycle configs: {configs}")
    print(f"Word: {word}")

    # Build transition functions from the cycle
    fs_result = build_system_from_cycle(n, ms, configs, word)
    if fs_result is None:
        print("Could not build consistent transition functions!")
        return

    # Verify
    result = verify_system(ms, fs_result, verbose=True)
    print(f"\nVerification result: valid={result['valid']}")
    for prop, (ok, info) in result.get('properties', {}).items():
        print(f"  {prop}: {ok} — {info}")

    if result['valid']:
        print("\n*** VALID SYSTEM AT n=5, ms=[2,2,2,3,3]! ***")
        print("This means M_5 <= 72, contradicting M_5 = 96.")
        print("SOMETHING IS WRONG WITH OUR ANALYSIS.")
    else:
        print("\nSystem is NOT valid (as expected — M_5 = 96 > 72)")
        print("The good cycle exists but convergence/liveness fails.")

def main():
    print("=" * 60)
    print("SORRY 5 v7: Full system validity check")
    print("=" * 60)

    print("\n--- Part 1: Verify n=5 system ---")
    verify_n5_system()

    print("\n\n--- Part 2: Check n=9 double-sweep word ---")
    check_word_at_n9()

if __name__ == '__main__':
    main()
