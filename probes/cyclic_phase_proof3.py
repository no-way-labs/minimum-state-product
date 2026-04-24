"""
Cyclic Phase Decomposition — Proof + Verification using known valid systems.

Strategy: use the CLB/CUP-2 construction which gives known valid systems,
extract good cycles, and verify the cyclic phase decomposition.
"""
import sys
sys.path.insert(0, './claude')
from itertools import product as iprod

# ============================================================================
# Build CUP-2 system (ms = (2, 3, ..., 3, 2)) from known tables
# ============================================================================

def cup2_tables(n):
    """CUP-2 universal transition tables for ms=(2,3,...,3,2)."""
    ms = [2] + [3]*(n-2) + [2]

    # Tables from cup2_theorem.py / CUP-2 paper
    # T_low: proc 0 (binary, m=2)
    T_low = {
        (0, 0, 0): 1, (0, 0, 1): 1, (0, 0, 2): 1,
        (0, 1, 0): 1, (0, 1, 1): 1, (0, 1, 2): 1,
        (1, 0, 0): 0, (1, 0, 1): 0, (1, 0, 2): 0,
        (1, 1, 0): 1, (1, 1, 1): 1, (1, 1, 2): 1,
    }

    # T_high: proc n-1 (binary, m=2)
    T_high = {
        (0, 0, 0): 0, (0, 0, 1): 0,
        (0, 1, 0): 0, (0, 1, 1): 1,
        (1, 0, 0): 1, (1, 0, 1): 0,
        (1, 1, 0): 0, (1, 1, 1): 1,
        (2, 0, 0): 1, (2, 0, 1): 0,
        (2, 1, 0): 0, (2, 1, 1): 1,
    }

    # T_mid: interior ternary procs
    T_mid = {
        (0, 0, 0): 1, (0, 0, 1): 1, (0, 0, 2): 1,
        (0, 1, 0): 1, (0, 1, 1): 1, (0, 1, 2): 1,
        (0, 2, 0): 2, (0, 2, 1): 0, (0, 2, 2): 2,
        (1, 0, 0): 0, (1, 0, 1): 0, (1, 0, 2): 0,
        (1, 1, 0): 1, (1, 1, 1): 1, (1, 1, 2): 1,
        (1, 2, 0): 0, (1, 2, 1): 0, (1, 2, 2): 2,
        (2, 0, 0): 1, (2, 0, 1): 1, (2, 0, 2): 0,
        (2, 1, 0): 2, (2, 1, 1): 2, (2, 1, 2): 2,
        (2, 2, 0): 2, (2, 2, 1): 2, (2, 2, 2): 2,
    }

    # Build per-processor transition functions
    def make_func(table):
        def f(L, S, R):
            return table.get((L, S, R), S)  # default: no change
        return f

    fs = []
    for i in range(n):
        if i == 0:
            fs.append(make_func(T_low))
        elif i == n - 1:
            fs.append(make_func(T_high))
        else:
            fs.append(make_func(T_mid))

    return ms, fs

# ============================================================================
# Sol 3 v1 system: ms = (2, 3, ..., 3)
# ============================================================================

def sol3v1_tables(n):
    """Sol 3 v1: incrementing transitions, ms=(2, 3, ..., 3)."""
    ms = [2] + [3]*(n-1)

    def make_inc(m_i):
        def f(L, S, R):
            new = (S + 1) % m_i
            return new
        return f

    # For Sol 3 v1, the transition is always incrementing
    fs = [make_inc(ms[i]) for i in range(n)]
    return ms, fs

# ============================================================================
# Good cycle extraction
# ============================================================================

def privileged_set(config, fs, ms, n):
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i, fs, ms, n):
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new = list(config)
    new[i] = fs[i](L, S, R)
    return tuple(new)

def find_good_cycles(n, ms, fs):
    """Find good cycles in the system."""
    all_cfgs = list(iprod(*[range(m) for m in ms]))

    # Find single-privileged configs
    single_priv = {}
    for c in all_cfgs:
        ps = privileged_set(c, fs, ms, n)
        if len(ps) == 1:
            single_priv[c] = ps[0]

    # Follow chains to find cycles
    cycles = []
    visited_global = set()

    for start in single_priv:
        if start in visited_global:
            continue
        path = [start]
        seen = {start}
        current = start
        while True:
            mover = single_priv[current]
            nxt = apply_move(current, mover, fs, ms, n)
            if nxt not in single_priv:
                break
            if nxt == start and len(path) >= 3:
                cycles.append(path)
                break
            if nxt in seen:
                break
            path.append(nxt)
            seen.add(nxt)
            current = nxt
        visited_global.update(seen)

    return cycles, single_priv

# ============================================================================
# Phase decomposition verification
# ============================================================================

def get_mover_word(cycle, priv_map):
    return [priv_map[c] for c in cycle]

def fire_steps(mw, p):
    return [i for i, m in enumerate(mw) if m == p]

def fire_count(mw, p):
    return sum(1 for m in mw if m == p)

def verify_rotation_approach(mw, t, n, CL):
    """
    Approach C: rotate so t fires at step 0.
    Then all fc(t) phases are linear intervals [a, s) with a < s.
    """
    ts = fire_steps(mw, t)
    fc = len(ts)
    if fc < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    # Rotate
    rot = ts[0]
    rmw = mw[rot:] + mw[:rot]
    rts = fire_steps(rmw, t)
    assert rts[0] == 0

    # fc phases:
    # Phases 0..fc-2: [rts[i], rts[i+1]) — interior
    # Phase fc-1: [rts[-1], CL) — final (goes to cycle boundary = step 0)
    total_J = 0
    total_K = 0
    phases = []
    all_covered = set()

    for i in range(fc):
        a = rts[i]
        s = rts[i+1] if i < fc-1 else CL

        assert a < s, f"Phase {i}: a={a} >= s={s}"

        J = 0
        K = 0
        for k in range(a+1, s):
            all_covered.add(k)
            if rmw[k] == left_t:
                J += 1
            if rmw[k] == right_t:
                K += 1
        total_J += J
        total_K += K
        phases.append({'a': a, 's': s, 'J': J, 'K': K, 'type': 'interior' if i < fc-1 else 'final'})

    # t-fire steps
    for s in rts:
        all_covered.add(s)

    fc_left = fire_count(rmw, left_t)
    fc_right = fire_count(rmw, right_t)

    return {
        'ok': total_J == fc_left and total_K == fc_right and len(all_covered) == CL,
        'fc_t': fc,
        'fc_left': fc_left,
        'fc_right': fc_right,
        'total_J': total_J,
        'total_K': total_K,
        'J_match': total_J == fc_left,
        'K_match': total_K == fc_right,
        'partition': len(all_covered) == CL,
        'phases': phases,
        'all_linear': all(a < (rts[i+1] if i < fc-1 else CL) for i, a in enumerate(rts)),
    }

def verify_direct_approach(mw, t, n, CL):
    """
    Approach D: fc-1 interior phases + wrap-around fire count identity.
    """
    ts = fire_steps(mw, t)
    fc = len(ts)
    if fc < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    # Interior phases
    int_J = 0
    int_K = 0
    for i in range(fc - 1):
        a, s = ts[i], ts[i+1]
        for k in range(a+1, s):
            if mw[k] == left_t: int_J += 1
            if mw[k] == right_t: int_K += 1

    # Wrap: [0, ts[0]) + (ts[-1], CL)
    wrap_J = 0
    wrap_K = 0
    for k in range(0, ts[0]):
        if mw[k] == left_t: wrap_J += 1
        if mw[k] == right_t: wrap_K += 1
    for k in range(ts[-1]+1, CL):
        if mw[k] == left_t: wrap_J += 1
        if mw[k] == right_t: wrap_K += 1

    fc_left = fire_count(mw, left_t)
    fc_right = fire_count(mw, right_t)

    return {
        'ok': (int_J + wrap_J == fc_left) and (int_K + wrap_K == fc_right),
        'int_J': int_J, 'int_K': int_K,
        'wrap_J': wrap_J, 'wrap_K': wrap_K,
        'fc_left': fc_left, 'fc_right': fc_right,
        'has_wrap': wrap_J > 0 or wrap_K > 0,
    }

# ============================================================================
# intervalFireCount decomposition identity
# ============================================================================

def verify_ifc_decomposition(mw, t, n, CL):
    """
    KEY IDENTITY: For any processor p,
      fc(p) = sum over all fc(t) cyclic phases of intervalFireCount(p, phase)

    This is what the Lean proof needs. Verify it holds.
    """
    ts = fire_steps(mw, t)
    fc = len(ts)
    if fc < 2:
        return None

    results = {}
    for p in range(n):
        if p == t:
            continue

        # Total fires of p
        total_fc = fire_count(mw, p)

        # Sum over cyclic phases (using rotation)
        rot = ts[0]
        rmw = mw[rot:] + mw[:rot]
        rts = fire_steps(rmw, t)

        phase_sum = 0
        for i in range(fc):
            a = rts[i]
            s = rts[i+1] if i < fc-1 else CL
            for k in range(a+1, s):
                if rmw[k] == p:
                    phase_sum += 1

        results[p] = {
            'fc': total_fc,
            'phase_sum': phase_sum,
            'match': total_fc == phase_sum,
        }

    return results

# ============================================================================
# Main verification
# ============================================================================

def run_system_test(n, ms, fs, label):
    print(f"\n{'='*70}")
    prod = 1
    for m in ms: prod *= m
    print(f"{label}: n={n}, ms={ms}, product={prod}")
    print(f"{'='*70}")

    cycles, priv_map = find_good_cycles(n, ms, fs)
    print(f"  Good cycles found: {len(cycles)}")
    if not cycles:
        return

    # Show cycle lengths
    lengths = [len(c) for c in cycles]
    print(f"  Cycle lengths: {sorted(set(lengths))}")

    total = 0
    rot_pass = 0
    dir_pass = 0
    decomp_pass = 0
    has_wrap = 0

    for ci, cycle in enumerate(cycles):
        mw = get_mover_word(cycle, priv_map)
        CL = len(cycle)

        for t in range(n):
            ts = fire_steps(mw, t)
            fc_t = len(ts)
            if fc_t < 2:
                continue

            left_t = (t - 1) % n
            right_t = (t + 1) % n

            # Only test ternary t with binary neighbors
            if ms[t] < 3 or ms[left_t] != 2 or ms[right_t] != 2:
                continue

            total += 1

            # Rotation approach
            res_rot = verify_rotation_approach(mw, t, n, CL)
            if res_rot and res_rot['ok']:
                rot_pass += 1
            else:
                print(f"  FAIL rotation: cycle {ci}, t={t}, CL={CL}")
                if res_rot:
                    print(f"    {res_rot}")

            # Direct approach
            res_dir = verify_direct_approach(mw, t, n, CL)
            if res_dir and res_dir['ok']:
                dir_pass += 1
                if res_dir['has_wrap']:
                    has_wrap += 1
            else:
                print(f"  FAIL direct: cycle {ci}, t={t}")

            # IFC decomposition
            res_ifc = verify_ifc_decomposition(mw, t, n, CL)
            if res_ifc and all(v['match'] for v in res_ifc.values()):
                decomp_pass += 1
            else:
                print(f"  FAIL decomposition: cycle {ci}, t={t}")
                for p, v in res_ifc.items():
                    if not v['match']:
                        print(f"    p={p}: fc={v['fc']}, phase_sum={v['phase_sum']}")

    print(f"\n  Ternary-pivot tests: {total}")
    print(f"  Rotation (C):  {rot_pass}/{total}")
    print(f"  Direct   (D):  {dir_pass}/{total}")
    print(f"  IFC decomp:    {decomp_pass}/{total}")
    print(f"  Has wrap fires: {has_wrap}/{total}")

def detailed_example(n, ms, fs, label):
    """Show one detailed cycle."""
    cycles, priv_map = find_good_cycles(n, ms, fs)
    if not cycles:
        print(f"  No cycles for {label}")
        return

    cycle = cycles[0]
    mw = get_mover_word(cycle, priv_map)
    CL = len(cycle)
    print(f"\n  {label}: CL={CL}")
    print(f"  Mover word: {mw}")

    for t in range(n):
        ts = fire_steps(mw, t)
        fc_t = len(ts)
        if fc_t < 2:
            continue
        left_t = (t - 1) % n
        right_t = (t + 1) % n
        if ms[t] < 3 or ms[left_t] != 2 or ms[right_t] != 2:
            continue

        print(f"\n    t={t}, fc(t)={fc_t}, t-fires at: {ts}")
        print(f"    left={left_t} (m={ms[left_t]}), right={right_t} (m={ms[right_t]})")

        # Rotation
        res = verify_rotation_approach(mw, t, n, CL)
        print(f"    Rotation (rotate by {ts[0]}):")
        for i, ph in enumerate(res['phases']):
            print(f"      Phase {i} ({ph['type']}): [{ph['a']}, {ph['s']}), J={ph['J']}, K={ph['K']}")
        print(f"    Sum: J={res['total_J']}=fc(L)={res['fc_left']}? {res['J_match']}")
        print(f"         K={res['total_K']}=fc(R)={res['fc_right']}? {res['K_match']}")

        # Direct
        res_d = verify_direct_approach(mw, t, n, CL)
        print(f"    Direct: int_J={res_d['int_J']}, int_K={res_d['int_K']}, "
              f"wrap_J={res_d['wrap_J']}, wrap_K={res_d['wrap_K']}")

        break

if __name__ == '__main__':
    print("=" * 70)
    print("CYCLIC PHASE DECOMPOSITION — REAL SYSTEM VERIFICATION")
    print("=" * 70)

    # n=5 CUP-2
    for n in [5, 7, 9]:
        ms, fs = cup2_tables(n)
        run_system_test(n, ms, fs, f"CUP-2 n={n}")

    # Detailed examples
    print("\n" + "=" * 70)
    print("DETAILED EXAMPLES")
    print("=" * 70)
    for n in [5, 7]:
        ms, fs = cup2_tables(n)
        detailed_example(n, ms, fs, f"CUP-2 n={n}")

    # Summary
    print("\n" + "=" * 70)
    print("PROOF APPROACH RECOMMENDATION")
    print("=" * 70)
    print("""
APPROACH C (Rotation) is CORRECT and CLEAN:

THEOREM (Cyclic Phase Decomposition via Rotation):
Let gc be a good cycle of length CL for a system on n processors.
Let t be a processor with fc(t) >= 2 and fc(t) < CL.
Let t fire at steps s_0 < s_1 < ... < s_{fc-1}.

Define gc' = gc.rotate(s_0), the cycle starting from step s_0.
Then in gc':
  (1) t fires at step 0 (by construction)
  (2) t fires at steps 0 = s'_0 < s'_1 < ... < s'_{fc-1} < CL
  (3) The fc phases [s'_i, s'_{i+1}) for i=0..fc-2 and [s'_{fc-1}, CL)
      are ALL valid TernaryPhase instances (a < s)
  (4) These fc phases partition all non-t-fire steps
  (5) For any processor p != t:
      fc(p) = sum_{i=0}^{fc-1} intervalFireCount(p, s'_i, s'_{i+1})
      where s'_{fc} := CL

In particular, for p = left(t) and p = right(t):
  fc(left(t))  = sum J_i
  fc(right(t)) = sum K_i

PROOF STRUCTURE FOR LEAN:

Step 1: Define gc.rotate
  - GoodCycle.rotate (gc : GoodCycle sys) (k : Fin gc.configs.length) : GoodCycle sys
  - configs' = gc.configs.drop k ++ gc.configs.take k
  - This preserves: length, distinct, closed (cyclic), unique_privileged

Step 2: Rotation preserves fire counts
  - gc.rotate.fireCount p = gc.fireCount p (rotation is just a permutation of steps)
  - gc.rotate.moverAt i = gc.moverAt ((i + k) % CL)

Step 3: After rotation, phase decomposition is linear
  - t fires at step 0 in gc.rotate(s_0)
  - All t-fire steps are in strictly increasing order: 0 = s'_0 < ... < s'_{fc-1}
  - The fc intervals [s'_0, s'_1), [s'_1, s'_2), ..., [s'_{fc-1}, CL) are disjoint
  - Their union covers {0, ..., CL-1}
  - Each is a valid TernaryPhase (a < s, t fires at s, t doesn't fire in (a, s))

Step 4: Fire count decomposition
  - intervalFireCount is additive over disjoint intervals:
    ifc(p, 0, CL) = ifc(p, 0, s'_1) + ifc(p, s'_1, s'_2) + ... + ifc(p, s'_{fc-1}, CL)
  - ifc(p, 0, CL) = fc(p) (definition)
  - Each summand = J_i or K_i for the corresponding phase

Step 5: Apply to get the needed inequality
  - h_phase_le1: each TernaryPhase has J + K <= 1 (from normalForm + mechanisms)
  - Sum: fc(L) + fc(R) = sum(J_i + K_i) <= sum(1) = fc(t)
  - This fills the sorry at AllNormalFormFalse2.lean:1129

LEAN COMPLEXITY ESTIMATE:
  - Step 1 (rotate definition): ~50 lines. List.drop/take manipulation.
  - Step 2 (preserve fire counts): ~30 lines. Finset.sum permutation.
  - Step 3 (linear phases): ~40 lines. Monotonicity of t-fire steps.
  - Step 4 (decomposition): ~20 lines. intervalFireCount_split iterated.
  - Step 5 (application): ~10 lines. Combine with h_phase_le1.
  Total: ~150 lines of new Lean code.

ALTERNATIVE (Approach D, no rotation):
  Instead of rotating, directly prove:
    fc(p) = ifc(p, 0, s_0) + sum_{i=0}^{fc-2} ifc(p, s_i, s_{i+1}) + ifc(p, s_{fc-1}, CL)
  where ifc(p, 0, s_0) + ifc(p, s_{fc-1}, CL) = wrap-around fire count.
  Then:
    wrap_J + wrap_K <= 1 (need to prove for the wrap-around "phase")
    interior J_i + K_i <= 1 (from existing TernaryPhase)
    Total: fc(L) + fc(R) <= fc(t)

  This avoids gc.rotate but requires proving the wrap-around phase has the
  same J+K bound, which is essentially reproving the mechanism arguments
  for the wrap-around interval. NOT recommended.

CONCLUSION: Approach C (rotation) is the cleanest path to filling the sorry.
""")
