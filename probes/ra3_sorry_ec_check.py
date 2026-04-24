#!/usr/bin/env python3
"""
For sorry-pattern mover sequences, simulate with random transitions and
check every processor for entry conflict.

Key: The sorry pattern has the mover walk from one side of t all the way
around the ring. E.g., sorry-L at n=9,t=1:
  R(2) -> RR(3) -> 4 -> 5 -> 6 -> 7 -> LL(8) -> L(0) -> T(1)

This is a "long arc" walk. Every processor fires exactly once (except t
which fires at the end). The question: does this always produce an EC?
"""
import random
from collections import defaultdict

random.seed(42)

def ring_adj(a, b, n):
    return min((a - b) % n, (b - a) % n) == 1

def simulate_phase_ec(n, ms, t, mover_seq, num_trials=500000):
    """For a mover sequence, random transitions + configs, check EC at each proc."""
    CL = len(mover_seq)
    ec_at = defaultdict(int)
    ec_at_in_phase = defaultdict(int)  # EC using only steps within the phase
    no_ec_count = 0
    total = 0
    no_ec_examples = []

    for trial in range(num_trials):
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        configs = [config]
        valid = True

        for k in range(CL):
            p = mover_seq[k]
            L = config[(p-1)%n]
            S = config[p]
            R = config[(p+1)%n]
            new_val = sys_f[p][(L, S, R)]
            if new_val == S:
                valid = False
                break
            nc = list(config)
            nc[p] = new_val
            config = tuple(nc)
            configs.append(config)

        if not valid:
            continue
        if len(set(configs[:CL])) != CL:  # configs[0..CL-1] must be distinct
            continue

        total += 1

        found_ec = False
        for p in range(n):
            mover_triples = set()
            nonmover_triples = set()
            for k in range(CL):
                L_val = configs[k][(p-1)%n]
                S_val = configs[k][p]
                R_val = configs[k][(p+1)%n]
                triple = (L_val, S_val, R_val)
                if mover_seq[k] == p:
                    mover_triples.add(triple)
                else:
                    nonmover_triples.add(triple)
            if mover_triples & nonmover_triples:
                ec_at[p] += 1
                found_ec = True

        if not found_ec:
            no_ec_count += 1
            if len(no_ec_examples) < 10:
                no_ec_examples.append((configs, mover_seq, sys_f))

    return total, ec_at, no_ec_count, no_ec_examples


def analyze_ec_at_t(n, ms, t, mover_seq, num_trials=500000):
    """Specifically analyze EC at processor t.

    In the phase, t does not fire until the last step.
    At step s (last), t fires with boundary (v_L', v_t, v_R').
    At step k < s (non-mover for t), boundary is (v_L(k), v_t, v_R(k)).

    Since t doesn't fire in [0, s-1], v_t is CONSTANT throughout.
    v_L changes when lt fires, v_R changes when rt fires.

    EC at t: exists k<s where (v_L(k), v_t, v_R(k)) = (v_L(s), v_t, v_R(s)).
    Since v_t constant, this reduces to: v_L(k)=v_L(s) AND v_R(k)=v_R(s).
    """
    lt = (t - 1) % n
    rt = (t + 1) % n
    CL = len(mover_seq)

    # Find which steps change v_L and v_R
    lt_steps = [k for k in range(CL) if mover_seq[k] == lt]
    rt_steps = [k for k in range(CL) if mover_seq[k] == rt]

    print(f"\n  t={t}, lt_fires_at={lt_steps}, rt_fires_at={rt_steps}")

    ec_at_t = 0
    no_ec_at_t = 0
    total = 0

    for trial in range(num_trials):
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        configs = [config]
        valid = True

        for k in range(CL):
            p = mover_seq[k]
            L = config[(p-1)%n]
            S = config[p]
            R = config[(p+1)%n]
            new_val = sys_f[p][(L, S, R)]
            if new_val == S:
                valid = False
                break
            nc = list(config)
            nc[p] = new_val
            config = tuple(nc)
            configs.append(config)

        if not valid:
            continue
        if len(set(configs[:CL])) != CL:
            continue

        total += 1

        # Check EC at t
        # t fires at step CL-1 (last step). Config at that step is configs[CL-1].
        # The boundary triple at t at step CL-1:
        s = CL - 1
        L_s = configs[s][(t-1)%n]
        S_s = configs[s][t]
        R_s = configs[s][(t+1)%n]

        # At non-mover steps for t (all steps except s):
        found = False
        for k in range(s):
            L_k = configs[k][(t-1)%n]
            S_k = configs[k][t]
            R_k = configs[k][(t+1)%n]
            if (L_k, S_k, R_k) == (L_s, S_s, R_s):
                found = True
                break

        if found:
            ec_at_t += 1
        else:
            no_ec_at_t += 1

    return total, ec_at_t, no_ec_at_t


def main():
    n = 9
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
    t = 1
    lt = 0; rt = 2; llt = 8; rrt = 3

    name_map = {0: 'L', 1: 'T', 2: 'R', 3: 'RR', 4: '4', 5: '5', 6: '6', 7: '7', 8: 'LL'}

    # The canonical sorry-L sequence: R RR 4 5 6 7 LL L T
    sorry_L = [2, 3, 4, 5, 6, 7, 8, 0, 1]
    # The canonical sorry-R sequence: L LL 7 6 5 4 RR R T
    sorry_R = [0, 8, 7, 6, 5, 4, 3, 2, 1]

    print(f"n={n}, ms={ms}, t={t}")
    print()

    for label, seq in [("Sorry-L", sorry_L), ("Sorry-R", sorry_R)]:
        annotated = ' '.join(name_map.get(m, str(m)) for m in seq)
        print(f"=== {label}: {annotated} ===")

        total, ec_at, no_ec, no_ec_ex = simulate_phase_ec(n, ms, t, seq, num_trials=500000)
        print(f"Valid trials: {total}")
        print(f"No EC anywhere: {no_ec} ({no_ec/max(total,1)*100:.2f}%)")

        print("EC by processor:")
        for p in range(n):
            if ec_at.get(p, 0) > 0:
                pname = name_map.get(p, str(p))
                print(f"  {pname}(proc {p}, m={ms[p]}): {ec_at[p]}/{total} = {ec_at[p]/total:.4f}")

        # Detailed analysis at t
        print(f"\nDetailed EC at t:")
        total2, ec_t, no_ec_t = analyze_ec_at_t(n, ms, t, seq, num_trials=200000)
        print(f"  EC at t: {ec_t}/{total2} = {ec_t/max(total2,1):.4f}")
        print(f"  No EC at t: {no_ec_t}/{total2}")

        # If there are no-EC examples, analyze them
        if no_ec_ex:
            print(f"\nNo-EC example analysis:")
            for i, (configs, movers, sys_f) in enumerate(no_ec_ex[:3]):
                print(f"  Example {i+1}:")
                for k in range(len(movers)):
                    p = movers[k]
                    pname = name_map.get(p, str(p))
                    c = configs[k]
                    print(f"    Step {k}: mover={pname}, config={c}")

                # Show boundary triples at each processor
                for p in range(n):
                    pname = name_map.get(p, str(p))
                    triples = []
                    for k in range(len(movers)):
                        L_val = configs[k][(p-1)%n]
                        S_val = configs[k][p]
                        R_val = configs[k][(p+1)%n]
                        is_mover = 'M' if movers[k] == p else ' '
                        triples.append(f"[{is_mover}]({L_val},{S_val},{R_val})")
                    print(f"    Proc {pname}: {' '.join(triples)}")
        print()


if __name__ == '__main__':
    main()
