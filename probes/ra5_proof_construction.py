"""
ra5_proof_construction.py — Construct the ACTUAL proof.

FINDINGS:
1. The original lemma is FALSE (Dijkstra's binary ring is a counterexample).
2. With OSCILLATION (walk goes 1→0→1 or 1→2→1 within the arc), EC holds for binary.
3. With min_fc >= 4 (binary) or >= 5 (ternary), EC holds.

The CORRECT lemma:
If the walk OSCILLATES within the 3-arc (i.e., the middle proc fires at least
once with the walk arriving from the same side as it departed), then EC exists.

PROOF IDEA for the oscillation case:
The oscillation creates a "V-pattern": ..., 1, 0, 1, ... or ..., 1, 2, 1, ...
At the first 1 in the V: proc 1 fires. config[1] = v_j → v_{j+1}.
At the 0 (or 2): flanking fire. config[0] (or config[2]) changes.
At the second 1: proc 1 fires again. config[1] = v_{j+1} → v_{j+2}.

Between the two 1-fires: only one flanking fire (at 0 or 2).
So the triple at proc 1 changes in only ONE component (L or R) between
the end of the first epoch and the start of the second epoch.

But the mover triples at the two 1-fires have DIFFERENT S values (v_j vs v_{j+1}).
So they don't directly match. However, between the flanking fire and the second
1-fire: there may be a non-arc gap where the triple is "frozen."

Actually, let me re-examine. In the oscillation ..., 1, 0, 1, ...:
- Step k: mover = 1. Triple at proc 1: (L_a, v_j, R_b). After: config[1] = v_{j+1}.
- Step k+1: mover = 0. Triple at proc 1: (L_a, v_{j+1}, R_b). After: config[0] = L_{a+1}.
  This is a non-mover step for proc 1 with S = v_{j+1}.
- Step k+2: mover = 1. Triple at proc 1: (L_{a+1}, v_{j+1}, R_b).
  This is a mover step for proc 1 with S = v_{j+1}.

EC: Step k+1 (non-mover, S=v_{j+1}) vs Step k+2 (mover, S=v_{j+1}).
Need: L matches and R matches.
Step k+1: L = L_a (before fire of proc 0)
Step k+2: L = L_{a+1} (after fire of proc 0)
L_a ≠ L_{a+1} (proc 0 changes state when it fires). NO EC!

Hmm. Let me think again...

Actually, the triple at step k+1 is the config BEFORE the move at k+1.
At step k+1 (mover = 0): config[0] is about to change from L_a to L_{a+1}.
Triple at step k+1 = (L_a, v_{j+1}, R_b).
At step k+2 (mover = 1): config[1] is v_{j+1}, about to change to v_{j+2}.
Triple at step k+2 = (L_{a+1}, v_{j+1}, R_b).
L_a vs L_{a+1}: DIFFERENT.

What about the step BEFORE k+1? If it's a non-arc step:
Step k-gap (mover outside arc): triple = (L_a, v_j+1, R_b) (same as after step k but before step k+1)
Wait, step k+1 is RIGHT after step k. After step k: config = (..., L_a, v_{j+1}, R_b, ...).
Step k+1: mover = 0, config[0] = L_a → L_{a+1}. Triple at step k+1: (L_a, v_{j+1}, R_b).

Hmm, is step k+1 the IMMEDIATE next step after k? If so, they're consecutive in the walk.
The walk goes: ..., mover=1 at step k, mover=0 at step k+1, mover=1 at step k+2, ...

Actually wait: the oscillation pattern ..., 1, 0, 1, ... means the CONSECUTIVE
movers in the walk are 1, 0, 1. So yes, steps k, k+1, k+2 are consecutive.

Now: are there any non-arc steps between k and k+1? NO — they're consecutive.
Between k+1 and k+2? Also consecutive.

So the oscillation V-pattern ..., 1, 0, 1, ... in the FULL walk means:
Step k:   mover = 1. Triple = (L_a, v_j, R_b). After: config[1] = v_{j+1}.
Step k+1: mover = 0. Triple = (L_a, v_{j+1}, R_b). After: config[0] = L_{a+1}.
Step k+2: mover = 1. Triple = (L_{a+1}, v_{j+1}, R_b). After: config[1] = v_{j+2}.

Mover steps for proc 1: k (triple (L_a, v_j, R_b)) and k+2 (triple (L_{a+1}, v_{j+1}, R_b)).
Non-mover step: k+1 (triple (L_a, v_{j+1}, R_b)).

EC between k+2 (mover) and k+1 (non-mover)?
S: v_{j+1} = v_{j+1} ✓
L: L_{a+1} vs L_a — DIFFERENT ✗

EC between k (mover) and k+1 (non-mover)?
S: v_j vs v_{j+1} — DIFFERENT ✗

So the V-pattern itself doesn't directly give EC between the adjacent steps!
But the oscillation guarantees more steps elsewhere in the cycle.

Let me reconsider. The oscillation means the middle proc fires at least 2 times,
and the walk visits the middle proc at least 3 times (fire, leave, return, fire, ...).
This means there are AT LEAST 2 middle-proc mover steps and at least 1 flanking step
between them. But the triple analysis shows the immediately adjacent steps don't match.

The EC must come from DISTANT steps in the cycle. Let me think about what the
oscillation implies for the GLOBAL structure.

When the walk oscillates at the middle: ..., 1, 0, 1, ... or ..., 1, 2, 1, ...
After the second 1-fire: the walk can go to 0 or 2 (ring-adjacent to 1).
Eventually it must leave the arc (to fire other procs) and return.

The key is that the oscillation creates a period where the triple at proc 1
"drifts" only in one flanking component at a time. After enough oscillations,
the values must repeat (pigeonhole), giving EC.

Actually, let me just verify: does oscillation ALWAYS give EC for binary?
The data says: 14758/14758 = 100% for binary with oscillation.
But for ternary: 14334/14344 = 99.93%, with 10 failures.

Let me investigate the ternary failures with oscillation.
"""

import random
from collections import defaultdict


def ring_dist(a, b, n):
    d = abs(a - b)
    return min(d, n - d)


def generate_ra_cycle(n, ms, max_depth=200):
    config = tuple(random.randint(0, ms[i]-1) for i in range(n))
    path = [config]
    movers = []
    visited = {config}

    for step in range(max_depth):
        candidates = []
        for i in range(n):
            if movers and ring_dist(movers[-1], i, n) > 1:
                continue
            for v in range(ms[i]):
                if v == config[i]:
                    continue
                new_config = list(config)
                new_config[i] = v
                new_config = tuple(new_config)
                if new_config == path[0] and len(path) >= 3:
                    if ring_dist(i, movers[0], n) <= 1:
                        candidates.append((i, v, new_config, True))
                elif new_config not in visited:
                    candidates.append((i, v, new_config, False))

        if not candidates:
            return None
        closing = [c for c in candidates if c[3]]
        if closing and len(path) >= n:
            i, v, new_config, _ = random.choice(closing)
            movers.append(i)
            return path, movers
        else:
            non_closing = [c for c in candidates if not c[3]]
            if not non_closing:
                if closing:
                    i, v, new_config, _ = random.choice(closing)
                    movers.append(i)
                    return path, movers
                return None
            i, v, new_config, _ = random.choice(non_closing)
            movers.append(i)
            config = new_config
            path.append(config)
            visited.add(config)

    return None


def check_ec_at_arc(path, movers, arc, n):
    CL = len(movers)
    for q in arc:
        left = (q-1) % n
        right = (q+1) % n
        mt = set()
        nmt = set()
        for k in range(CL):
            triple = (path[k][left], path[k][q], path[k][right])
            if movers[k] == q:
                mt.add(triple)
            else:
                nmt.add(triple)
        if mt & nmt:
            return True
    return False


def investigate_ternary_osc_failures():
    """Find ternary cycles with oscillation that fail EC."""
    print("=== Ternary Oscillation Failures ===")

    random.seed(42)
    n = 7
    ms = [3]*7

    failures = []
    total_osc = 0

    for trial in range(200000):
        result = generate_ra_cycle(n, ms)
        if result is None:
            continue
        path, movers = result
        CL = len(movers)

        fire_counts = defaultdict(int)
        for m in movers:
            fire_counts[m] += 1

        fire_set = set(movers)

        for p in range(n):
            arc = [p, (p+1)%n, (p+2)%n]
            if not all(q in fire_set for q in arc):
                continue

            # Check oscillation
            arc_set = set(arc)
            translate = {arc[0]: 0, arc[1]: 1, arc[2]: 2}
            arc_steps = [k for k in range(CL) if movers[k] in arc_set]
            arc_seq = [translate[movers[k]] for k in arc_steps]

            has_oscillation = False
            for i in range(len(arc_seq) - 2):
                if arc_seq[i] == 1 and arc_seq[i+1] in [0, 2] and arc_seq[i+2] == 1:
                    has_oscillation = True
                    break

            if not has_oscillation:
                continue

            total_osc += 1

            if not check_ec_at_arc(path, movers, arc, n):
                failures.append({
                    'path': [tuple(c) for c in path[:CL]],
                    'movers': movers[:],
                    'arc': arc[:],
                    'CL': CL,
                    'fire_counts': dict(fire_counts),
                })

    print(f"Total oscillating arcs tested: {total_osc}")
    print(f"Failures: {len(failures)}")

    for i, f in enumerate(failures[:5]):
        print(f"\n--- Failure {i+1} ---")
        print(f"CL={f['CL']}, arc={f['arc']}")
        print(f"fire_counts={f['fire_counts']}")
        arc = f['arc']
        arc_set = set(arc)
        translate = {arc[0]: 0, arc[1]: 1, arc[2]: 2}

        # Show arc-restricted mover pattern
        arc_seq = [(k, translate[f['movers'][k]]) for k in range(f['CL']) if f['movers'][k] in arc_set]
        print(f"Arc pattern (step, mover_in_arc): {[(k, m) for k, m in arc_seq]}")
        print(f"Arc movers: {[m for _, m in arc_seq]}")

        # Show triples at middle proc
        q = arc[1]
        left = (q-1) % n
        right = (q+1) % n
        print(f"\nTriples at proc {q} (middle):")
        for k in range(f['CL']):
            triple = (f['path'][k][left], f['path'][k][q], f['path'][k][right])
            if f['movers'][k] == q:
                print(f"  Step {k}: MOVER triple={triple}")

        print("All distinct non-mover triples:")
        nmt = set()
        for k in range(f['CL']):
            triple = (f['path'][k][left], f['path'][k][q], f['path'][k][right])
            if f['movers'][k] != q:
                nmt.add(triple)
        for t in sorted(nmt):
            print(f"  {t}")


def verify_binary_oscillation_perfect():
    """
    Verify that binary oscillation ALWAYS gives EC.
    Use massive sample size.
    """
    print("\n=== Verifying Binary Oscillation = Perfect EC ===")

    random.seed(42)
    total_osc = 0
    failures = 0

    for n in [7, 8, 9, 10]:
        ms = [2]*n
        for trial in range(50000):
            result = generate_ra_cycle(n, ms)
            if result is None:
                continue
            path, movers = result
            CL = len(movers)

            fire_counts = defaultdict(int)
            for m in movers:
                fire_counts[m] += 1

            fire_set = set(movers)

            for p in range(n):
                arc = [p, (p+1)%n, (p+2)%n]
                if not all(q in fire_set for q in arc):
                    continue

                arc_set = set(arc)
                translate = {arc[0]: 0, arc[1]: 1, arc[2]: 2}
                arc_seq = [translate[movers[k]] for k in range(CL) if movers[k] in arc_set]

                has_oscillation = False
                for i in range(len(arc_seq) - 2):
                    if arc_seq[i] == 1 and arc_seq[i+1] in [0, 2] and arc_seq[i+2] == 1:
                        has_oscillation = True
                        break

                if not has_oscillation:
                    continue

                total_osc += 1
                if not check_ec_at_arc(path, movers, arc, n):
                    failures += 1
                    print(f"FAILURE: n={n}, CL={CL}, arc={arc}")

    print(f"\nTotal binary oscillating arcs: {total_osc}")
    print(f"Failures: {failures}")


def prove_binary_oscillation():
    """
    PROVE: For all-binary n >= 7, if 3 adjacent procs fire and the walk
    oscillates at the middle (pattern ..., 1, 0, 1, ... or ..., 1, 2, 1, ...),
    then EC exists.

    PROOF:

    Consider the oscillation pattern ..., 1, 0, 1, ... at steps k, k+1, k+2.
    (The case ..., 1, 2, 1, ... is symmetric.)

    Step k:   mover = 1. Triple at proc 1: (L, v, R). After: config[1] = v' ≠ v.
    Step k+1: mover = 0. Triple: (L, v', R). After: config[0] = L' ≠ L.
    Step k+2: mover = 1. Triple: (L', v', R). After: config[1] = v'' ≠ v'.

    Mover triples at proc 1: (L, v, R) at step k, (L', v', R) at step k+2.
    Non-mover triple at proc 1: (L, v', R) at step k+1.

    For EC between step k+1 (non-mover) and step k+2 (mover):
    S: v' = v' ✓. L: L vs L' — different. R: R = R ✓.
    Only L differs. So NO direct EC between adjacent oscillation steps.

    Now: L = config[0] at step k+1 = original value before proc 0 fires.
    L' = config[0] after proc 0 fires at step k+1.

    For BINARY proc 0: L ∈ {0, 1} and L' = 1 - L.

    We need a mover step for proc 1 where the triple is (L, v', R).
    This requires config[0] = L and config[1] = v' (before firing) and config[2] = R.

    After step k+2: config[1] = v''. The walk continues.
    Eventually, config[1] returns to v' (it must, for the cycle to close,
    and since proc 1 is binary, it alternates: v, v', v, v', ...).

    Wait: proc 1 is binary too! Each fire toggles config[1].
    If config[1] starts at v = 0: after fire → v' = 1 → fire → v'' = 0 → ...
    So v'' = v. And config[1] cycles through 0, 1, 0, 1, ...

    Similarly, config[0] cycles through L, L', L, L', ...

    So the S-values at proc 1's mover steps alternate: v, v', v, v', ...
    Mover steps with S = v: fires 1, 3, 5, ... (odd-numbered in 1-indexing)
    Mover steps with S = v': fires 2, 4, 6, ... (even-numbered)

    Similarly, between consecutive mover steps, the non-mover steps have S = v' or S = v.

    Now, the triple at proc 1 = (config[0], config[1], config[2]).
    Since all procs are binary: each component is 0 or 1. Triple space = {0,1}^3 = 8 values.

    Proc 1 fires f1 times (f1 >= 2 for binary, since it must fire an even number of times).
    Proc 0 fires f0 >= 2 times. Proc 2 fires f2 >= 2 times.

    For the oscillation case: there's a V-pattern ..., 1, 0, 1, ... which means f0 >= 1
    and f1 >= 2. But we also require f2 >= 1 (proc 2 fires).

    With oscillation: the walk visits 1, then 0, then 1 again. This means
    proc 1 fires at least twice, and between these two fires, only proc 0 fires once.

    COUNTING ARGUMENT:
    Proc 1 fires f1 >= 2 times. Between consecutive fires of proc 1:
    - config[1] is constant (binary alternation).
    - Procs 0 and 2 may fire some number of times.

    The non-mover steps for proc 1 in each epoch have triple (L_?, S, R_?).
    The mover step at the end of the epoch has triple (L_end, S, R_end).

    For the oscillation V-pattern at epoch j: only proc 0 fires once.
    So the epoch has 1 non-mover step (the proc 0 fire).
    L changes once (L_end = L_start + 1 mod 2).
    R stays the same (R_end = R_start).

    Non-mover triple at the flanking step: (L_start, S, R_start).
    Mover triple at the next 1-fire: (L_end, S, R_start) = (1-L_start, S, R_start).
    These differ in L. No EC within this epoch.

    But now consider the epoch BEFORE the oscillation (epoch j-1):
    Proc 1's (j-1)-th fire to j-th fire. S = v_{j-1} = alternation value.
    At the end of this epoch: mover triple = (L_{some}, v_{j-1}, R_{some}).

    And the epoch AFTER the oscillation (epoch j+1):
    Non-mover steps in this epoch have S = v_{j+1} = v_{j-1} (binary alternation!).
    So the S-value repeats every 2 epochs!

    The mover triple at fire j-1 has S = v_{j-1}.
    Non-mover steps in epoch j+1 have S = v_{j+1} = v_{j-1}.
    So S matches between fire j-1 (mover) and non-mover steps in epoch j+1!

    For EC: need L and R to also match.
    Fire j-1 triple: (L_a, v_{j-1}, R_b).
    Non-mover steps in epoch j+1: (L_?, v_{j-1}, R_?).

    What are L and R in epoch j+1? They depend on the fire history.
    Between fire j-1 and epoch j+1: procs 0 and 2 have fired some number of times.
    For binary procs: L = L_a + (fires of proc 0 between) mod 2.
    R = R_b + (fires of proc 2 between) mod 2.

    If fires of proc 0 between is even: L matches!
    If fires of proc 2 between is even: R matches!

    Between fire j-1 and the start of epoch j+1 (= fire j+1 in the good cycle):
    - Epoch j (from fire j-1 to fire j): proc 0 fires d0_j times, proc 2 fires d2_j times.
    - Epoch j+1 starts at fire j. In epoch j+1: proc 0 fires d0_{j+1} times, proc 2 fires d2_{j+1} times.
    - Total fires of proc 0 between fire j-1 and start of epoch j+1: d0_j.
    - But within epoch j+1, non-mover steps have additional fires of 0 and 2.

    This is getting complicated. Let me try a cleaner formulation.
    """
    print("\n=== Binary Oscillation Proof ===")
    print()

    # KEY INSIGHT: In the binary case, the S-value at proc 1 alternates: v, v', v, v', ...
    # Between mover step j and mover step j+2: S has the SAME value.
    # So we need L and R to match between some mover step j and
    # some non-mover step in epoch j+2 (or j-2, etc.).

    # Between mover step j and mover step j+2:
    # L changes by: total fires of proc 0 in epochs j+1 and partial j+2 (mod 2).
    # R changes by: total fires of proc 2 in epochs j+1 and partial j+2 (mod 2).

    # For the oscillation V-pattern: the middle epoch (between fire j and fire j+1)
    # has exactly 1 fire of proc 0 and 0 fires of proc 2 (or vice versa).

    # So the total L-change from fire j-1 to the non-mover steps in epoch j+1:
    # = fires of proc 0 in epoch j = 1 (from the V-pattern) + fires in earlier part of epoch j+1.

    # This is still complex. Let me try the PIGEONHOLE approach instead.

    # PIGEONHOLE PROOF:
    # Each proc in the arc fires f_i >= 2 times (binary, even).
    # Total arc fires: f0 + f1 + f2 >= 6.
    # Mover triples at proc 1: f1 values, each in {0,1}^3. At most 8 distinct.
    # Non-mover triples at proc 1: (CL - f1) steps. Many more non-mover steps.
    # But the number of DISTINCT non-mover triples is bounded by the number of
    # distinct triples, which is at most 8.

    # However, mover triples might all be distinct AND disjoint from non-mover triples.
    # That's the case in the Dijkstra counterexample.

    # With oscillation: the mover triples include both (L, v, R) and (L', v', R)
    # where L' = 1-L (from the V-pattern). But we also need other arcs to have
    # non-mover triples that match these.

    # Actually, the proof might need to use the CYCLE structure more deeply.
    # Let me enumerate what happens.

    print("For binary ring with oscillation (V-pattern 1,0,1):")
    print()
    print("Config[1] alternates: v, v', v, v', ...")
    print("  Mover steps with S=v: fires 1, 3, 5, ... (0-indexed from first fire)")
    print("  Mover steps with S=v': fires 0, 2, 4, ...")
    print("  Wait, indexing matters. Let fire_0 be the first fire of proc 1.")
    print("  At fire_0: S = v_init = v (say). After: v' = 1-v.")
    print("  At fire_1: S = v'. After: v.")
    print("  At fire_2: S = v. After: v'.")
    print("  Mover triples with S=v: fire_0, fire_2, fire_4, ...")
    print("  Mover triples with S=v': fire_1, fire_3, fire_5, ...")
    print()
    print("Non-mover steps in epoch j (between fire_{j-1} and fire_j) have S=v_{j-1 mod 2}.")
    print("  Epoch 0 (before first fire): S=v. (These are non-mover steps.)")
    print("  Epoch 1 (after fire 0): S=v'. ")
    print("  Epoch 2 (after fire 1): S=v.")
    print("  ...")
    print()
    print("Mover steps with S=v: fires 0, 2, 4, ...")
    print("Non-mover steps with S=v: epochs 0, 2, 4, ...")
    print("For EC: match mover step fire_2j with non-mover step in epoch 2j'")
    print("  where (L, R) match.")
    print()
    print("At fire_0: (L, R) = (L_{I(0)}, R_{K(0)})")
    print("  where I(0) = fires of proc 0 before fire_0, K(0) = fires of proc 2 before fire_0.")
    print("At fire_2: (L, R) = (L_{I(2)}, R_{K(2)})")
    print("In epoch 0 (non-mover): (L, R) range over values as proc 0 and 2 fire.")
    print("In epoch 2 (non-mover): (L, R) range over values as proc 0 and 2 fire.")
    print()
    print("Binary L values: L_0, L_1 = 1-L_0, L_2 = L_0, ... (alternating).")
    print("L_{I(0)} = L_0 if I(0) is even, = 1-L_0 if I(0) is odd.")
    print()
    print("For EC between fire_0 and a step in epoch 0:")
    print("  Need L_{I(t)} = L_{I(0)} and R_{K(t)} = R_{K(0)}")
    print("  I.e., I(t) ≡ I(0) mod 2 and K(t) ≡ K(0) mod 2.")
    print("  I(0) = fires of proc 0 before fire_0. At step t < fire_0: I(t) ≤ I(0).")
    print("  We need I(t) ≡ I(0) mod 2, i.e., I(0) - I(t) is even.")
    print("  I.e., an even number of proc 0 fires between t and fire_0.")
    print("  Similarly for proc 2.")
    print()
    print("If I(0) ≥ 2 and K(0) ≥ 2: take t such that I(t) = I(0) - 2 and K(t) = K(0) - 2")
    print("  (go back 2 fires of each). But this requires specific ordering of fires.")
    print()
    print("Actually, the SIMPLEST approach: look at the step where (I(t), K(t)) = (I(0), K(0)).")
    print("This is the step AFTER the last fire of {0, 2} before fire_0 (or the start of the cycle).")
    print("If there IS a non-arc step between the last {0,2} fire and fire_0: EC!")
    print("This is the GAP argument again.")
    print()
    print("The GAP fails when fire_0 is immediately preceded by a {0,2} fire.")
    print("But with oscillation: fire_0 is preceded by... let's check.")


def conclusive_test():
    """
    Test the FINAL version of the lemma.

    CORRECT LEMMA: On a ring of n >= 7 processors with ring-adjacent movers,
    if 3 adjacent processors {p, p+1, p+2} all fire and the minimum fire count
    of any arc processor is >= 4 (for binary) or >= 5 (for ternary), then EC exists.

    Actually, from the data:
    - Binary min_fc >= 4: 100% EC
    - Ternary min_fc >= 5: 100% EC
    - Mixed min_fc >= 4: 100% EC

    The threshold seems to be: each arc proc fires at least m_i + 1 times
    (more than enough to cycle through all values and back).

    EVEN SHARPER: For binary, min_fc >= 4 means each proc fires >= 4 = 2*m times.
    For ternary, min_fc >= 5 means each fires >= 5 > 3 = m times. But 4 fails sometimes.

    Let me test min_fc >= 2*m (each fires at least 2m times).
    Binary: 2*2=4. Ternary: 2*3=6. Let me verify.
    """
    print("\n=== Testing min_fc >= 2*m_i Threshold ===")

    random.seed(42)
    total_tested = 0
    failures = 0

    for n in [7, 8, 9]:
        for ms in [[2]*n, [3]*n, [2,2,2]+[3]*(n-3)]:
            for trial in range(30000):
                result = generate_ra_cycle(n, ms)
                if result is None:
                    continue
                path, movers = result
                CL = len(movers)

                fire_counts = defaultdict(int)
                for m in movers:
                    fire_counts[m] += 1

                fire_set = set(movers)

                for p in range(n):
                    arc = [p, (p+1)%n, (p+2)%n]
                    if not all(q in fire_set for q in arc):
                        continue

                    # Check min_fc >= 2*m for each arc proc
                    ok = True
                    for q in arc:
                        if fire_counts[q] < 2 * ms[q]:
                            ok = False
                            break
                    if not ok:
                        continue

                    total_tested += 1
                    if not check_ec_at_arc(path, movers, arc, n):
                        failures += 1
                        print(f"FAILURE: n={n}, ms={ms}, CL={CL}, arc={arc}")
                        print(f"  arc fc: {[fire_counts[q] for q in arc]}")
                        print(f"  arc ms: {[ms[q] for q in arc]}")

    print(f"\nTotal arcs with min_fc >= 2*m: {total_tested}")
    print(f"Failures: {failures}")


if __name__ == "__main__":
    investigate_ternary_osc_failures()
    verify_binary_oscillation_perfect()
    prove_binary_oscillation()
    conclusive_test()
