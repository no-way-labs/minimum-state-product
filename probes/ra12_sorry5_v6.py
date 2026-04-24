"""
RA12 v6: Check if the EC-free mover words from v5 are actual valid good cycles.

A mover word + ternary value assignment gives a CONFIG SEQUENCE.
For it to be a valid good cycle, we need:
1. Each config is distinct (no repeated configs)
2. The transition function is consistent (no EC = this is satisfied)
3. At each step, the mover is the ONLY privileged processor

Wait — condition 3 is important. The mover being the only privileged proc means:
- mover p: f_p(L,S,R) != S (privileged)
- for all q != p: f_q(L,S,R) == S (not privileged)

The "no EC" condition ensures that f_p is well-defined (mover contexts never
overlap with non-mover contexts). But we also need that f_q is well-defined
at non-mover contexts, which is automatic (f_q = identity at those contexts).

The ADDITIONAL constraint is: at each step, f_p(L,S,R) != S for the mover
AND f_q(L,S,R) == S for all non-movers. The latter is guaranteed by
choosing f_q(L,S,R) = S for non-mover contexts. But we need to verify that
the mover contexts and non-mover contexts for each proc are disjoint
(which is exactly the no-EC condition).

So the no-EC condition is BOTH necessary and sufficient for a valid good cycle
(given that configs are distinct).

Let me verify that configs are distinct for the EC-free examples.

ALSO IMPORTANT: The Lean theorem has hypothesis n >= 9. At n=5, M_5 = 96 = 2*2*2*3*4.
With ms=[2,2,2,3,3] (product=72 < 96), the lower bound theorem DOES apply.
So at n=5 with ms=[2,2,2,3,3], no valid system exists.

But we found EC-free MOVER WORDS. The question is whether they form valid good cycles
with distinct configs. Let me check.
"""

import sys
from itertools import product as iprod

def build_config_sequence(n, ms, word, binary_init=None, ternary_init=None, ternary_choices=None):
    """Build the full config sequence from a mover word + value assignments."""
    L = len(word)
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    if binary_init is None:
        binary_init = {p: 0 for p in binary_pos}
    if ternary_init is None:
        ternary_init = {p: 0 for p in ternary_pos}

    # Build values step by step
    vals = [{} for _ in range(L)]

    # Initialize
    current = {}
    for p in binary_pos:
        current[p] = binary_init[p]
    for p in ternary_pos:
        current[p] = ternary_init[p]

    choice_idx = 0
    ternary_fire_steps = {p: [] for p in ternary_pos}

    for k in range(L):
        # Record current values
        for p in range(n):
            vals[k][p] = current[p]

        # Apply move
        mover = word[k]
        if ms[mover] == 2:
            current[mover] = 1 - current[mover]
        elif ms[mover] == 3:
            if ternary_choices is not None:
                alts = [v for v in range(3) if v != current[mover]]
                current[mover] = alts[ternary_choices[choice_idx]]
                choice_idx += 1
            else:
                current[mover] = (current[mover] + 1) % 3  # default: increment

    # Check cycle: final state = initial state
    cycle_ok = True
    for p in range(n):
        if p in binary_pos:
            if current[p] != binary_init[p]:
                cycle_ok = False
        else:
            if current[p] != ternary_init[p]:
                cycle_ok = False

    configs = [tuple(vals[k][p] for p in range(n)) for k in range(L)]
    return configs, cycle_ok

def check_full_validity(n, ms, word):
    """
    For a given mover word, check ALL possible ternary assignments.
    Return the first valid good cycle (distinct configs, no EC, cycle closes),
    or None if none exists.
    """
    L = len(word)
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    # Binary fire count parity check
    from collections import Counter
    fc = Counter(word)
    for p in binary_pos:
        if fc.get(p, 0) % 2 != 0:
            return None

    ternary_fire_steps = {p: [k for k in range(L) if word[k] == p] for p in ternary_pos}
    ternary_fire_counts = {p: len(ternary_fire_steps[p]) for p in ternary_pos}

    # Enumerate ternary initial values and fire choices
    for t_init in iprod(range(3), repeat=len(ternary_pos)):
        ternary_init = {ternary_pos[i]: t_init[i] for i in range(len(ternary_pos))}

        # Build list of fire choice indices
        total_fires = sum(ternary_fire_counts[p] for p in ternary_pos)
        for fire_combo in iprod(range(2), repeat=total_fires):
            configs, cycle_ok = build_config_sequence(
                n, ms, word,
                binary_init={p: 0 for p in binary_pos},
                ternary_init=ternary_init,
                ternary_choices=list(fire_combo)
            )

            if not cycle_ok:
                continue

            # Check distinct configs
            if len(set(configs)) != len(configs):
                continue

            # Check no EC
            has_ec = False
            for p in range(n):
                mover_ctx = set()
                nonmover_ctx = set()
                for k in range(L):
                    left_v = configs[k][(p-1) % n]
                    self_v = configs[k][p]
                    right_v = configs[k][(p+1) % n]
                    ctx = (left_v, self_v, right_v)
                    if word[k] == p:
                        mover_ctx.add(ctx)
                    else:
                        nonmover_ctx.add(ctx)
                if mover_ctx & nonmover_ctx:
                    has_ec = True
                    break

            if not has_ec:
                return {
                    'configs': configs,
                    'ternary_init': ternary_init,
                    'fire_choices': fire_combo,
                }

    return None

def main():
    n = 5
    ms = [2, 2, 2, 3, 3]

    print("=" * 60)
    print("SORRY 5 v6: Validity check of EC-free mover words")
    print(f"n={n}, ms={ms}, product={2*2*2*3*3}=72, M_5=96")
    print("=" * 60)

    # EC-free examples from v5
    examples = [
        [0, 4, 3, 2, 1, 0, 4, 3, 2, 1],  # L=10
        [0, 1, 2, 3, 4, 0, 1, 2, 3, 4],  # L=10
        [1, 0, 4, 3, 2, 1, 0, 4, 3, 2],  # L=10
    ]

    for word in examples:
        print(f"\nWord: {word} (L={len(word)})")
        result = check_full_validity(n, ms, word)
        if result:
            print(f"  VALID GOOD CYCLE FOUND!")
            print(f"  Ternary init: {result['ternary_init']}")
            print(f"  Configs: {result['configs']}")
            # Verify: this would be a valid system at sub-threshold
            # contradicting the lower bound theorem
            print(f"  *** THIS CONTRADICTS THE LOWER BOUND! ***")
        else:
            print(f"  No valid good cycle possible (all EC or not cycle or not distinct)")

    # Also check: do these words satisfy the FULL hypothesis set from the Lean theorem?
    # The Lean theorem requires n >= 9. These are at n=5.
    # Let me check: does the word [0,4,3,2,1,0,4,3,2,1] form a valid good cycle
    # even without the n>=9 constraint?

    print("\n" + "=" * 60)
    print("Detailed analysis of word [0,4,3,2,1,0,4,3,2,1]")
    print("=" * 60)

    word = [0, 4, 3, 2, 1, 0, 4, 3, 2, 1]
    L = len(word)

    # Check all 9 * 4 = 36 ternary assignments (3 init for each of 2 ternary procs × 2^2 fire choices)
    ternary_pos = [3, 4]
    fc3 = sum(1 for w in word if w == 3)
    fc4 = sum(1 for w in word if w == 4)
    print(f"Fire counts: proc3={fc3}, proc4={fc4}")

    valid_count = 0
    ec_free_count = 0
    no_cycle_count = 0
    not_distinct_count = 0

    for t3_init in range(3):
        for t4_init in range(3):
            for choices in iprod(range(2), repeat=fc3+fc4):
                configs, cycle_ok = build_config_sequence(
                    n, ms, word,
                    binary_init={0:0, 1:0, 2:0},
                    ternary_init={3: t3_init, 4: t4_init},
                    ternary_choices=list(choices)
                )

                if not cycle_ok:
                    no_cycle_count += 1
                    continue

                if len(set(configs)) != len(configs):
                    not_distinct_count += 1
                    continue

                valid_count += 1

                # Check EC
                has_ec = False
                ec_procs = []
                for p in range(n):
                    mctx = set()
                    nctx = set()
                    for k in range(L):
                        left_v = configs[k][(p-1) % n]
                        self_v = configs[k][p]
                        right_v = configs[k][(p+1) % n]
                        ctx = (left_v, self_v, right_v)
                        if word[k] == p:
                            mctx.add(ctx)
                        else:
                            nctx.add(ctx)
                    if mctx & nctx:
                        has_ec = True
                        ec_procs.append(p)

                if not has_ec:
                    ec_free_count += 1
                    print(f"  EC-FREE: init=({t3_init},{t4_init}), choices={choices}")
                    print(f"    Configs: {configs}")

    print(f"\nSummary: valid_cycles={valid_count}, ec_free={ec_free_count}, "
          f"no_cycle={no_cycle_count}, not_distinct={not_distinct_count}")

    if ec_free_count > 0:
        print("\n*** VALID EC-FREE GOOD CYCLES EXIST AT n=5 ***")
        print("This means the sorry case is REAL and needs a mechanism")
        print("that goes BEYOND entry conflict.")
        print("\nBut wait — the THEOREM says no valid system exists at product < M_n.")
        print("A valid good cycle without EC CAN have a valid transition function,")
        print("but the SYSTEM might still fail convergence or other properties.")
        print("Entry conflict is sufficient for impossibility, not necessary.")
        print("The sorry is inside a proof that uses EC as the impossibility mechanism.")
        print("If EC is not forced, the proof strategy is WRONG for this case.")
    else:
        print("\n*** All valid cycles have EC — sorry is dischargeable ***")

if __name__ == '__main__':
    main()
