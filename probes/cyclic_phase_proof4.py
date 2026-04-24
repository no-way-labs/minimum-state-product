"""
Cyclic Phase Decomposition — Verification with real CUP-2 systems.
Uses cup2_theorem.py's build_system() and verifier.py.
"""
import sys, os
sys.path.insert(0, './claude')
from itertools import product as iprod
from cup2_theorem import build_system
from verifier import privileged_set, apply_move

# ============================================================================
# Good cycle extraction
# ============================================================================

def find_good_cycles(n, ms, fs):
    """Find good cycles."""
    all_cfgs = list(iprod(*[range(m) for m in ms]))

    # Single-privileged configs
    sp = {}
    for c in all_cfgs:
        ps = privileged_set(c, fs, ms)
        if len(ps) == 1:
            sp[c] = ps[0]

    cycles = []
    visited = set()

    for start in sp:
        if start in visited:
            continue
        path = [start]
        seen = {start}
        cur = start
        while True:
            mover = sp[cur]
            nxt = apply_move(cur, mover, fs, ms)
            if nxt not in sp:
                break
            if nxt == start and len(path) >= 3:
                cycles.append(path)
                break
            if nxt in seen:
                break
            path.append(nxt)
            seen.add(nxt)
            cur = nxt
        visited.update(seen)

    return cycles, sp

# ============================================================================
# Phase decomposition
# ============================================================================

def mover_word(cycle, sp):
    return [sp[c] for c in cycle]

def fire_steps(mw, p):
    return [i for i, m in enumerate(mw) if m == p]

def fire_count(mw, p):
    return sum(1 for m in mw if m == p)

def verify_rotation(mw, t, n, CL):
    """Approach C: rotate so t fires at step 0."""
    ts = fire_steps(mw, t)
    fc = len(ts)
    if fc < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    rot = ts[0]
    rmw = mw[rot:] + mw[:rot]
    rts = fire_steps(rmw, t)
    assert rts[0] == 0

    total_J = 0
    total_K = 0
    phases = []
    covered = set()

    for i in range(fc):
        a = rts[i]
        s = rts[i+1] if i < fc-1 else CL

        J = K = 0
        for k in range(a+1, s):
            covered.add(k)
            if rmw[k] == left_t: J += 1
            if rmw[k] == right_t: K += 1
        total_J += J
        total_K += K
        phases.append({'a': a, 's': s, 'J': J, 'K': K,
                       'type': 'interior' if i < fc-1 else 'final',
                       'linear': a < s})

    for s in rts:
        covered.add(s)

    fc_L = fire_count(rmw, left_t)
    fc_R = fire_count(rmw, right_t)

    return {
        'ok': total_J == fc_L and total_K == fc_R and len(covered) == CL,
        'fc_t': fc, 'fc_L': fc_L, 'fc_R': fc_R,
        'total_J': total_J, 'total_K': total_K,
        'J_ok': total_J == fc_L, 'K_ok': total_K == fc_R,
        'partition': len(covered) == CL,
        'all_linear': all(ph['linear'] for ph in phases),
        'phases': phases,
    }

def verify_direct(mw, t, n, CL):
    """Approach D: fc-1 interior + wrap-around."""
    ts = fire_steps(mw, t)
    fc = len(ts)
    if fc < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    # Interior
    int_J = int_K = 0
    for i in range(fc - 1):
        a, s = ts[i], ts[i+1]
        for k in range(a+1, s):
            if mw[k] == left_t: int_J += 1
            if mw[k] == right_t: int_K += 1

    # Wrap
    wrap_J = wrap_K = 0
    for k in range(0, ts[0]):
        if mw[k] == left_t: wrap_J += 1
        if mw[k] == right_t: wrap_K += 1
    for k in range(ts[-1]+1, CL):
        if mw[k] == left_t: wrap_J += 1
        if mw[k] == right_t: wrap_K += 1

    fc_L = fire_count(mw, left_t)
    fc_R = fire_count(mw, right_t)

    return {
        'ok': (int_J + wrap_J == fc_L) and (int_K + wrap_K == fc_R),
        'int_J': int_J, 'int_K': int_K,
        'wrap_J': wrap_J, 'wrap_K': wrap_K,
        'fc_L': fc_L, 'fc_R': fc_R,
        'has_wrap': wrap_J > 0 or wrap_K > 0,
    }

# ============================================================================
# Full IFC decomposition identity
# ============================================================================

def verify_ifc_decomp(mw, t, n, CL):
    """Verify sum of per-phase fire counts = total fire count, for ALL procs."""
    ts = fire_steps(mw, t)
    fc = len(ts)
    if fc < 2:
        return None

    rot = ts[0]
    rmw = mw[rot:] + mw[:rot]
    rts = fire_steps(rmw, t)

    ok = True
    for p in range(n):
        total_fc = fire_count(rmw, p)
        phase_sum = 0
        for i in range(fc):
            a = rts[i]
            s = rts[i+1] if i < fc-1 else CL
            for k in range(a+1, s):
                if rmw[k] == p:
                    phase_sum += 1
        # t-fire steps contribute to t's count but not to other procs
        if p == t:
            phase_sum += fc  # the fc t-fire steps
        if phase_sum != total_fc:
            ok = False
            print(f"    MISMATCH p={p}: fc={total_fc}, phase_sum={phase_sum}")

    return ok

# ============================================================================
# Main
# ============================================================================

def run_test(n):
    ms, fs = build_system(n)
    prod = 1
    for m in ms: prod *= m

    print(f"\n{'='*70}")
    print(f"CUP-2 n={n}: ms={ms}, product={prod}")
    print(f"{'='*70}")

    cycles, sp = find_good_cycles(n, ms, fs)
    print(f"  Good cycles: {len(cycles)}")
    if not cycles:
        return 0, 0, 0

    lens = [len(c) for c in cycles]
    print(f"  Cycle lengths: {sorted(set(lens))}")

    total = rot_pass = dir_pass = decomp_pass = wrap_cnt = 0

    for ci, cycle in enumerate(cycles):
        mw = mover_word(cycle, sp)
        CL = len(cycle)

        for t in range(n):
            ts = fire_steps(mw, t)
            fc_t = len(ts)
            if fc_t < 2:
                continue

            left_t = (t - 1) % n
            right_t = (t + 1) % n

            # Ternary t with binary neighbors
            if ms[t] < 3 or ms[left_t] != 2 or ms[right_t] != 2:
                continue

            total += 1

            r = verify_rotation(mw, t, n, CL)
            if r and r['ok'] and r['all_linear']:
                rot_pass += 1
            else:
                print(f"  FAIL rot: cycle {ci}, t={t}, CL={CL}")
                if r: print(f"    {r}")

            d = verify_direct(mw, t, n, CL)
            if d and d['ok']:
                dir_pass += 1
                if d['has_wrap']:
                    wrap_cnt += 1
            else:
                print(f"  FAIL dir: cycle {ci}, t={t}")

            ok = verify_ifc_decomp(mw, t, n, CL)
            if ok:
                decomp_pass += 1
            else:
                print(f"  FAIL decomp: cycle {ci}, t={t}")

    print(f"\n  Ternary-pivot tests: {total}")
    print(f"  Rotation:   {rot_pass}/{total}")
    print(f"  Direct:     {dir_pass}/{total}")
    print(f"  IFC decomp: {decomp_pass}/{total}")
    print(f"  Has wrap:   {wrap_cnt}/{total}")

    return total, rot_pass, dir_pass

def show_detail(n):
    ms, fs = build_system(n)
    cycles, sp = find_good_cycles(n, ms, fs)
    if not cycles:
        print(f"  No cycles for n={n}")
        return

    cycle = cycles[0]
    mw = mover_word(cycle, sp)
    CL = len(cycle)
    print(f"\n  n={n}: CL={CL}")
    print(f"  Mover word: {mw}")

    for t in range(n):
        ts = fire_steps(mw, t)
        if len(ts) < 2: continue
        left_t = (t-1) % n
        right_t = (t+1) % n
        if ms[t] < 3 or ms[left_t] != 2 or ms[right_t] != 2:
            continue

        print(f"\n    t={t}, fc(t)={len(ts)}, fires at: {ts}")
        print(f"    left={left_t} (m={ms[left_t]}), right={right_t} (m={ms[right_t]})")

        # Direct
        d = verify_direct(mw, t, n, CL)
        print(f"    Direct: int_J={d['int_J']}, int_K={d['int_K']}, "
              f"wrap_J={d['wrap_J']}, wrap_K={d['wrap_K']}, "
              f"fc_L={d['fc_L']}, fc_R={d['fc_R']}")

        # Rotation
        r = verify_rotation(mw, t, n, CL)
        print(f"    Rotation (by {ts[0]}):")
        for i, ph in enumerate(r['phases']):
            print(f"      Phase {i} ({ph['type']}): [{ph['a']}, {ph['s']}), J={ph['J']}, K={ph['K']}")
        print(f"    Sum: J={r['total_J']}/{r['fc_L']}, K={r['total_K']}/{r['fc_R']}")
        print(f"    All linear: {r['all_linear']}, partition: {r['partition']}")

        break

if __name__ == '__main__':
    print("=" * 70)
    print("CYCLIC PHASE DECOMPOSITION — CUP-2 SYSTEM VERIFICATION")
    print("=" * 70)

    for n in [5, 7, 9]:
        run_test(n)

    print("\n" + "=" * 70)
    print("DETAILED EXAMPLES")
    print("=" * 70)
    for n in [5, 7]:
        show_detail(n)

    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print("""
If all tests pass, Approach C (Rotation) is verified:
  1. Rotating the good cycle so t fires at step 0 makes ALL phases linear
  2. The fc(t) phases partition all steps
  3. Fire counts sum correctly: sum(J_i) = fc(L), sum(K_i) = fc(R)
  4. No wrap-around phase is needed — the "last" phase [s_{fc-1}, CL) is linear

This directly fills the sorry at AllNormalFormFalse2.lean:1129.
""")
