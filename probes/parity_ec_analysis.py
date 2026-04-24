#!/usr/bin/env python3
"""Parity EC analysis: In a mixed phase (J≥1, K≥1) with normalForm,
does the boundary triple at t ALWAYS match between the mover step s
and some non-mover step in the phase?

The boundary triple at t is (left(t) value, t value, right(t) value).
t value is constant (t doesn't fire in phase).
left(t) value = v_L ⊕ L(k') where L(k') = # L-fires before step k'.
right(t) value = v_R ⊕ R(k') where R(k') = # R-fires before step k'.

At mover step s: L(s) = J, R(s) = K. Need k' < s with L(k')≡J mod 2 and R(k')≡K mod 2.

The question: given a sequence of L and R fires interleaved with other fires,
does the parity pair (L mod 2, R mod 2) ALWAYS visit (J mod 2, K mod 2)
at some step before the last L or R fire?

Key cases:
- J=1, K=1, target (1,1): Need (1,1) at intermediate step.
  If L fires before R: after L: (1,0). After R: (1,1). Is this before end?
  If R fires at the very last step of the phase (step s-1): parity hits (1,1) at s.
  But s is the mover step for t, not a non-mover step for t.

  ACTUALLY: step s is where t fires (mover for t). The parity at step s is
  the parity AFTER all phase fires. configs[s] has left(t) value = v_L ⊕ J
  and right(t) value = v_R ⊕ K. This is the mover step's config.

  We need a NON-mover step k' (in [a, s-1]) where left(t) value = v_L ⊕ J
  and right(t) value = v_R ⊕ K. This means L(k') ≡ J mod 2 and R(k') ≡ K mod 2,
  where k' ∈ [a, s-1] and moverAt(k') ≠ t (always true since t doesn't fire in phase).

Let me enumerate all possible orderings of L and R fires and check.
"""

def check_parity_ec(J, K, orderings=None):
    """Check if parity EC at t works for given J, K.

    An ordering is a string like 'LRLLR' indicating the order of L and R fires
    among the phase movers. Other movers (not L or R) can be interspersed.

    The parity pair starts at (0,0) and we track it through the sequence.
    Target: (J%2, K%2).
    We need the target to appear at some step AFTER a fire and BEFORE the last step.
    """
    target = (J % 2, K % 2)

    if target == (0, 0):
        # normalForm says ¬(both even). So this case shouldn't happen
        # in the mixed case with J≥1, K≥1.
        return None

    # Generate all possible orderings of J L-fires and K R-fires
    from itertools import combinations

    total = J + K
    # Choose positions for L-fires among J+K fires
    results = {'hit': 0, 'miss': 0, 'miss_examples': []}

    for L_positions in combinations(range(total), J):
        L_set = set(L_positions)
        ordering = ['L' if i in L_set else 'R' for i in range(total)]

        # Track parity
        pL, pR = 0, 0
        hit = False

        for i, fire in enumerate(ordering):
            if fire == 'L':
                pL = 1 - pL
            else:
                pR = 1 - pR

            # Check if we've hit the target at this intermediate step
            # "intermediate" means not at the very last fire
            if (pL, pR) == target and i < total - 1:
                hit = True
                break

        if hit:
            results['hit'] += 1
        else:
            results['miss'] += 1
            if len(results['miss_examples']) < 3:
                results['miss_examples'].append(''.join(ordering))

    return results

print("Parity EC analysis: mixed phases (J≥1, K≥1, normalForm)")
print("=" * 60)
print()

for J in range(1, 6):
    for K in range(1, 6):
        target = (J % 2, K % 2)
        if target == (0, 0):
            continue  # Not normalForm compatible in mixed case

        result = check_parity_ec(J, K)
        total = result['hit'] + result['miss']
        pct = result['hit'] * 100 // total if total > 0 else 0
        status = "ALL HIT" if result['miss'] == 0 else f"MISS {result['miss']}/{total}"

        print(f"J={J} K={K} target={target}: {status}")
        if result['miss'] > 0:
            for ex in result['miss_examples']:
                print(f"  miss ordering: {ex}")
                # Show parity walk
                pL, pR = 0, 0
                walk = [(0,0)]
                for c in ex:
                    if c == 'L': pL = 1-pL
                    else: pR = 1-pR
                    walk.append((pL, pR))
                print(f"  parity walk: {walk}")

print()
print("Key insight: 'miss' orderings are where the target parity is")
print("only reached at the very last fire (step s-1 = last fire step).")
print("If the last fire step is s-1 and s is the t-mover step,")
print("then parity (J%2, K%2) is only at step s, which is the mover step.")
print()
print("HOWEVER: the non-mover step we need is in [a, s-1].")
print("The parity at step s-1+1 = s is configs[s], which IS the mover step.")
print("But the parity at steps after the last fire and before s also has")
print("the target parity (since no more L/R fires change it).")
print()
print("WAIT: if there are OTHER movers between the last L/R fire and step s,")
print("those don't change L/R parities. So the parity stays at target")
print("from the last fire step until step s.")
print()

# Check: in 'miss' cases, is the last fire always at the very end?
print("Detailed analysis of miss cases:")
for J in range(1, 4):
    for K in range(1, 4):
        target = (J % 2, K % 2)
        if target == (0, 0):
            continue
        result = check_parity_ec(J, K)
        if result['miss'] > 0:
            print(f"\nJ={J} K={K}:")
            for ex in result['miss_examples']:
                # When does the target first appear?
                pL, pR = 0, 0
                first_hit = None
                for i, c in enumerate(ex):
                    if c == 'L': pL = 1-pL
                    else: pR = 1-pR
                    if (pL, pR) == target:
                        first_hit = i
                        break
                print(f"  ordering: {ex}, target first at fire index {first_hit} (last fire at {len(ex)-1})")
                if first_hit == len(ex) - 1:
                    print(f"  -> Target ONLY at last fire!")
                    print(f"  -> Last fire is {'L' if ex[-1]=='L' else 'R'}")
                    print(f"  -> If there are non-L/R movers after this fire, parity stays at target")
                    print(f"  -> Those non-L/R movers are valid non-mover steps for t!")
