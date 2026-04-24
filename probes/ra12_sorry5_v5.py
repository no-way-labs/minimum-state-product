"""
RA12 v5: Check whether odd-parity mover words ALWAYS have EC somewhere.

From v4 results: odd-parity is non-vacuous, and EC at ri is NOT always forced.
Now check: is EC forced at some other proc? Or can the adversary (choosing ternary
transitions) avoid EC everywhere?

KEY INSIGHT: For a mover word, EC is a property of the CONFIG sequence, not just
the mover word. The config sequence depends on:
- Initial config
- Transition functions (determines new state at each move)

For BINARY procs: transition is forced (flip). So binary values are determined
by the mover word + initial binary values.

For TERNARY procs: when a ternary proc fires, its new value can be anything != old.
The adversary chooses.

EC at proc p means: exists two steps k1 (mover=p) and k2 (mover!=p) with same
context (L,S,R) at both steps.

For procs with ALL binary neighbors (only ri=1 at n=5): EC is determined by mover word.
For procs with ternary neighbors: adversary controls ternary values, so EC depends
on adversary's choices.

So the question is: for a given mover word, can the adversary choose ternary values
such that NO proc has EC?

This is a constraint satisfaction problem. Let me check it for the concrete examples.
"""

import sys
from collections import defaultdict
from itertools import product as iprod

sys.setrecursionlimit(100000)

def check_ec_avoidability(n, ms, word):
    """
    Given a mover word, check if an adversary can choose ternary proc values
    to avoid entry conflict at ALL processors.

    Binary values at each step are determined by the mover word (plus initial,
    which we can set to 0 WLOG for binary by symmetry).

    Ternary values: at each step where ternary proc p fires, adversary picks
    new value != current. This determines the ternary config sequence.

    We need to check: does there exist a choice of ternary transitions such that
    for every proc p, the mover-context set and non-mover-context set are disjoint?
    """
    L = len(word)
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    # Binary values: determined by mover word
    # val[p][k] = pfc(p, k) % 2 (with initial = 0)
    pfc = {}
    for p in binary_pos:
        pfc[p] = [0] * (L + 1)
        for k in range(L):
            pfc[p][k+1] = pfc[p][k] + (1 if word[k] == p else 0)

    binary_val = {}
    for p in binary_pos:
        binary_val[p] = [pfc[p][k] % 2 for k in range(L)]

    # Check if cycle condition holds for binary: val[p][L] must equal val[p][0]
    for p in binary_pos:
        if pfc[p][L] % 2 != 0:
            return None  # not a valid cycle (binary doesn't return)

    # For ternary procs: we need to search over possible value sequences
    # Ternary proc p fires at steps where word[k] == p
    # At each firing step, new value in {0,1,2} \ {current value}

    # For small n=5 with 2 ternary procs: try all possible ternary sequences
    # Each ternary proc has initial value (0,1, or 2) and at each fire step,
    # 2 choices for new value.

    # Number of ternary fire steps
    ternary_fires = {}
    for p in ternary_pos:
        ternary_fires[p] = sum(1 for k in range(L) if word[k] == p)

    # Total search space: 3^|ternary| * 2^(sum of ternary fires)
    # For n=5, L=8: maybe 2 ternary procs, each fires ~1-2 times
    # 3^2 * 2^(~3) = 72. Very feasible.

    total_choices = 3 ** len(ternary_pos)
    for p in ternary_pos:
        total_choices *= 2 ** ternary_fires[p]

    if total_choices > 10_000_000:
        return "TOO_LARGE"

    # Enumerate all ternary assignments
    # For each ternary proc: initial value (0,1,2) x choices at each fire step
    ternary_fire_steps = {}
    for p in ternary_pos:
        ternary_fire_steps[p] = [k for k in range(L) if word[k] == p]

    # Generate all ternary initial values
    for init_vals in iprod(range(3), repeat=len(ternary_pos)):
        # For each combo of fire choices
        fire_choice_ranges = []
        for idx, p in enumerate(ternary_pos):
            for _ in ternary_fire_steps[p]:
                fire_choice_ranges.append(range(2))  # 0 or 1 index into alternatives

        if not fire_choice_ranges:
            fire_choice_ranges = [range(1)]  # dummy

        for fire_choices in iprod(*fire_choice_ranges):
            # Build ternary value sequences
            ternary_val = {}
            fc_idx = 0
            valid = True

            for idx, p in enumerate(ternary_pos):
                ternary_val[p] = [0] * L
                current = init_vals[idx]
                step_idx = 0
                fire_steps_p = ternary_fire_steps[p]
                next_fire = fire_steps_p[0] if fire_steps_p else L

                for k in range(L):
                    ternary_val[p][k] = current
                    if word[k] == p:
                        # Fire: choose new value
                        alts = [v for v in range(3) if v != current]
                        choice = fire_choices[fc_idx]
                        fc_idx += 1
                        current = alts[choice]

                # Check cycle: final value must equal initial
                if current != init_vals[idx]:
                    valid = False
                    break

            if not valid:
                continue

            # Build full value map
            val = {}
            for p in binary_pos:
                val[p] = binary_val[p]
            for p in ternary_pos:
                val[p] = ternary_val[p]

            # Check EC at every proc
            has_ec = False
            for p in range(n):
                left_p = (p - 1) % n
                right_p = (p + 1) % n
                mover_ctx = set()
                nonmover_ctx = set()
                for k in range(L):
                    ctx = (val[left_p][k], val[p][k], val[right_p][k])
                    if word[k] == p:
                        mover_ctx.add(ctx)
                    else:
                        nonmover_ctx.add(ctx)
                if mover_ctx & nonmover_ctx:
                    has_ec = True
                    break

            if not has_ec:
                return {
                    'ec_free': True,
                    'init_vals': init_vals,
                    'val': {p: val[p][:8] for p in range(n)},
                }

    return {'ec_free': False}

def main():
    n = 5
    ms = [2, 2, 2, 3, 3]
    ri = 1

    print("=" * 60)
    print("SORRY 5 v5: EC avoidability check")
    print(f"n={n}, ms={ms}")
    print("=" * 60)

    # Enumerate mover words of length 8-12 with odd parity, no EC at ri
    for L in range(8, 14):
        odd_no_ec_ri = 0
        ec_avoidable = 0
        ec_unavoidable = 0
        examples = []

        def dfs(step, prev, fc, word):
            nonlocal odd_no_ec_ri, ec_avoidable, ec_unavoidable

            if step == L:
                first = word[0]
                diff = abs(first - prev) % n
                if diff > 1 and diff < n - 1:
                    return
                if any(fc[b] % 2 != 0 for b in [0, 1, 2]):
                    return
                if any(fc[p] == 0 for p in range(n)):
                    return
                if fc[ri] < 2:
                    return
                if all(p < 3 for p in word):
                    return

                ri_steps = [k for k in range(L) if word[k] == ri]
                for k in ri_steps:
                    if word[(k+1) % L] == ri:
                        return

                # MinFiringGap
                gaps = []
                for idx in range(len(ri_steps)):
                    a = ri_steps[idx]
                    b = ri_steps[(idx+1) % len(ri_steps)]
                    g = (b - a) % L
                    if g == 0:
                        g = L
                    gaps.append((a, b, g))

                min_g = min(g for _, _, g in gaps)
                if min_g < 2:
                    return

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

                    if lf % 2 == 0 and rf % 2 == 0:
                        return  # even parity

                    # Odd parity — check EC at ri
                    pfc = [[0]*(L+1) for _ in range(3)]
                    for k in range(L):
                        for p in range(3):
                            pfc[p][k+1] = pfc[p][k] + (1 if word[k] == p else 0)

                    mctx = set()
                    nctx = set()
                    for k in range(L):
                        c = (pfc[0][k]%2, pfc[1][k]%2, pfc[2][k]%2)
                        if word[k] == ri:
                            mctx.add(c)
                        else:
                            nctx.add(c)

                    if mctx & nctx:
                        return  # EC at ri

                    odd_no_ec_ri += 1

                    # Check full EC avoidability
                    result = check_ec_avoidability(n, ms, list(word))
                    if result and result.get('ec_free'):
                        ec_avoidable += 1
                        if len(examples) < 3:
                            examples.append((list(word), result))
                    else:
                        ec_unavoidable += 1

                    break
                return

            remaining = L - step
            unfired = sum(1 for p in range(n) if fc[p] == 0)
            if unfired > remaining:
                return

            for next_m in [(prev-1) % n, prev, (prev+1) % n]:
                fc[next_m] += 1
                word.append(next_m)
                dfs(step + 1, next_m, fc, word)
                word.pop()
                fc[next_m] -= 1

        for start in range(n):
            fc = [0] * n
            fc[start] = 1
            dfs(1, start, fc, [start])

        print(f"\nL={L}: odd_no_ec_ri={odd_no_ec_ri}, "
              f"ec_avoidable={ec_avoidable}, ec_unavoidable={ec_unavoidable}")

        if examples:
            for word, result in examples:
                print(f"  EC-FREE example: word={word}")
                print(f"    ternary init={result['init_vals']}")

        if ec_avoidable > 0:
            print(f"  *** EC IS AVOIDABLE — the sorry case is REAL ***")
        elif odd_no_ec_ri > 0:
            print(f"  All {odd_no_ec_ri} checked -> EC unavoidable (at non-ri procs)")

if __name__ == '__main__':
    main()
