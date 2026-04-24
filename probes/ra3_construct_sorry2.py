#!/usr/bin/env python3
"""
Construct sorry-pattern mover sequences more carefully.

Phase structure: t fired previously (at step a-1). Then in [a, s):
  movers m_a, m_{a+1}, ..., m_{s-1}, and t fires at step s.
  All consecutive movers ring-adjacent (including m_{a-1}=t adj to m_a,
  and m_{s-1} adj to m_s=t).

Sorry case:
  - J >= 1 fires of lt, K >= 1 fires of rt in [a, s)
  - Let fL = first step where lt fires, fR = first step where rt fires
  - mover at fL-1 = llt (left²(t) fires immediately before first lt fire)
  - mover at fR-1 = rrt (right²(t) fires immediately before first rt fire)
  - (fL >= a+1 and fR >= a+1, so fL-1 and fR-1 are within the phase)

Since t is at position 1, lt=0, rt=2, llt=8, rrt=3.
Ring adjacency: 0-1, 1-2, 2-3, ..., 7-8, 8-0.

The phase starts at a. mover at a-1 was t=1. So m_a must be adjacent to 1:
  m_a in {0, 2} (lt or rt).

For sorry case:
  - If first lt fire is at fL, then fL > a (since we need mover at fL-1 = llt=8).
    But m_a is adj to t=1 -> m_a in {0,1,2}. Can't be 8.
    So if fL = a+1, then m_a = llt = 8. But m_a must be adj to t=1.
    Ring dist(8, 1) in n=9: min(7, 2) = 2. NOT adjacent!

    So fL >= a+2: we need at least 2 steps before the first lt fire.
    At step fL-1: mover = 8 (llt). At step fL-2: mover must be adj to 8 -> {7, 0}.
    But also we need to get FROM m_a (in {0,2}) TO position 7 or 0 through
    ring-adjacent steps without firing lt or rt first.

Let me just enumerate properly with DFS.
"""
import random
from itertools import product as iterproduct
from collections import defaultdict

def ring_adj(a, b, n):
    d = min((a - b) % n, (b - a) % n)
    return d == 1

def enumerate_sorry_sequences(n, t, max_len=25, max_results=5000):
    """Enumerate sorry-pattern mover sequences via DFS."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n

    results = []

    def dfs(seq, first_lt, first_rt):
        if len(seq) > max_len:
            return
        if len(results) >= max_results:
            return

        last = seq[-1]

        # Try ending with t
        if ring_adj(last, t, n) and first_lt is not None and first_rt is not None:
            # Check sorry pattern
            if first_lt >= 1 and seq[first_lt - 1] == llt:
                if first_rt >= 1 and seq[first_rt - 1] == rrt:
                    results.append(list(seq) + [t])
                    if len(results) >= max_results:
                        return

        # Try extending with another non-t processor
        for nxt in range(n):
            if nxt == t:
                continue
            if not ring_adj(last, nxt, n):
                continue

            new_fL = first_lt
            new_fR = first_rt
            if nxt == lt and first_lt is None:
                new_fL = len(seq)
            if nxt == rt and first_rt is None:
                new_fR = len(seq)

            dfs(seq + [nxt], new_fL, new_fR)

    # Phase starts after t fires. First mover must be adjacent to t.
    for start in range(n):
        if start == t:
            continue
        if not ring_adj(start, t, n):
            continue
        fL = 0 if start == lt else None
        fR = 0 if start == rt else None
        dfs([start], fL, fR)

    return results


def simulate_phase_with_ec_check(n, ms, t, mover_seq, num_trials=100000):
    """For a given mover sequence, random transitions + configs, check EC."""
    CL = len(mover_seq)
    ec_at = defaultdict(int)
    no_ec_count = 0
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

        if len(set(configs)) != len(configs):
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

    return total, ec_at, no_ec_count


def main():
    n = 9
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
    t = 1  # ternary
    lt = 0  # binary
    rt = 2  # binary
    llt = 8
    rrt = 3

    print(f"n={n}, t={t}, lt={lt}(m=2), rt={rt}(m=2), llt={llt}, rrt={rrt}")
    print(f"ms={ms}")
    print()

    print("=== Enumerating sorry-pattern mover sequences ===")
    seqs = enumerate_sorry_sequences(n, t, max_len=18, max_results=5000)
    print(f"Found {len(seqs)} sequences")

    if not seqs:
        print("No sorry sequences found! Trying smaller n...")
        # Try n=5 with a simpler ring
        n = 5
        ms = [2, 3, 2, 3, 3]
        t = 1
        lt = 0; rt = 2; llt = 4; rrt = 3
        print(f"\nRetrying with n={n}, ms={ms}, t={t}")
        seqs = enumerate_sorry_sequences(n, t, max_len=15, max_results=5000)
        print(f"Found {len(seqs)} sequences")

        if not seqs:
            return

    # Length distribution
    len_counts = defaultdict(int)
    for seq in seqs:
        len_counts[len(seq)] += 1
    print("\nLength distribution:")
    for l in sorted(len_counts):
        print(f"  len={l}: {len_counts[l]}")

    # Name mapping
    name_map = {lt: 'L', rt: 'R', t: 'T', llt: 'LL', rrt: 'RR'}

    # Show shortest sequences
    shortest = min(len(s) for s in seqs)
    short_seqs = [s for s in seqs if len(s) == shortest]
    print(f"\nShortest sequences (len={shortest}): {len(short_seqs)}")
    for seq in short_seqs[:20]:
        annotated = [name_map.get(m, str(m)) for m in seq]
        print(f"  {' '.join(annotated)}")

    print("\n=== Simulating EC checks ===")
    random.seed(123)
    for idx, seq in enumerate(short_seqs[:10]):
        annotated = [name_map.get(m, str(m)) for m in seq]
        total, ec_at, no_ec = simulate_phase_with_ec_check(n, ms, t, seq, num_trials=100000)
        print(f"\nSeq {idx}: {' '.join(annotated)}")
        print(f"  Valid: {total}, no-EC: {no_ec} ({no_ec/max(total,1)*100:.1f}%)")
        for p in range(n):
            if ec_at.get(p, 0) > 0:
                pname = name_map.get(p, str(p))
                print(f"    EC at {pname}(proc {p}, m={ms[p]}): {ec_at[p]}/{total} = {ec_at[p]/total:.3f}")

    # Also check a few longer sequences
    if len(seqs) > len(short_seqs):
        med_len = shortest + 1
        med_seqs = [s for s in seqs if len(s) == med_len]
        if med_seqs:
            print(f"\n=== Medium length sequences (len={med_len}) ===")
            for idx, seq in enumerate(med_seqs[:5]):
                annotated = [name_map.get(m, str(m)) for m in seq]
                total, ec_at, no_ec = simulate_phase_with_ec_check(n, ms, t, seq, num_trials=100000)
                print(f"\nSeq: {' '.join(annotated)}")
                print(f"  Valid: {total}, no-EC: {no_ec} ({no_ec/max(total,1)*100:.1f}%)")
                for p in range(n):
                    if ec_at.get(p, 0) > 0:
                        pname = name_map.get(p, str(p))
                        print(f"    EC at {pname}(proc {p}, m={ms[p]}): {ec_at[p]}/{total} = {ec_at[p]/total:.3f}")


if __name__ == '__main__':
    main()
