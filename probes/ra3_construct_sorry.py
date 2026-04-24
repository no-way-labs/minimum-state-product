#!/usr/bin/env python3
"""
Construct mixed-phase scenarios directly rather than searching randomly.

The sorry case: Ring of n processors, t=1 ternary, lt=0 binary, rt=2 binary.
In a phase [a, s) where t fires at s:
  - Both lt and rt fire (mixed phase)
  - All consecutive movers ring-adjacent
  - left²(t) fires immediately before first lt fire
  - right²(t) fires immediately before first rt fire

We don't need a full valid good cycle. We can construct PARTIAL sequences
(mover sequences + config sequences) satisfying all the local constraints,
then check whether entry conflict is FORCED.

Key insight: Under ¬EC + all-adjacent, what are the constraints on configs?
- At each step k, the boundary triple at movers[k] determines the new value.
- At each step k, no processor p != movers[k] has its mover-triple appear at
  a non-mover step (no EC).
- All configs are distinct.

Let's work in a more abstract way: enumerate mover sequences for the phase
and check what constraints arise.
"""
import random
from itertools import product as iterproduct
from collections import defaultdict

def ring_adj(a, b, n):
    return (a - b) % n <= 1 or (b - a) % n <= 1

def enumerate_adjacent_mover_sequences(n, t, max_len=20):
    """Enumerate mover sequences where:
    - All consecutive movers are ring-adjacent
    - t fires at position s (last position)
    - t does NOT fire in interior
    - Both lt and rt fire at least once
    - left²(t) fires immediately before first lt fire
    - right²(t) fires immediately before first rt fire
    """
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n

    # BFS: build mover sequences ending with t
    # Each sequence is a list of movers
    # We need to track: has_lt, has_rt, first_lt_idx, first_rt_idx, prev_of_first_lt, prev_of_first_rt

    results = []

    # We'll enumerate by DFS
    def dfs(seq, has_lt, has_rt, first_lt_idx, first_rt_idx):
        if len(seq) > max_len:
            return

        last = seq[-1]
        # Try extending with ring-adjacent processor (not t)
        for nxt in range(n):
            if nxt == t:
                # t fires at end -> check if mixed phase
                if has_lt and has_rt:
                    if not ring_adj(last, t, n):
                        continue
                    # Check sorry pattern
                    if first_lt_idx is not None and first_lt_idx > 0:
                        prev_of_fL = seq[first_lt_idx - 1]
                        if prev_of_fL == llt:
                            if first_rt_idx is not None and first_rt_idx > 0:
                                prev_of_fR = seq[first_rt_idx - 1]
                                if prev_of_fR == rrt:
                                    full_seq = seq + [t]
                                    results.append(full_seq)
                                    if len(results) >= 10000:
                                        return
                continue

            if not ring_adj(last, nxt, n):
                continue

            new_has_lt = has_lt or (nxt == lt)
            new_has_rt = has_rt or (nxt == rt)
            new_fL = first_lt_idx if first_lt_idx is not None else (len(seq) if nxt == lt else None)
            new_fR = first_rt_idx if first_rt_idx is not None else (len(seq) if nxt == rt else None)

            dfs(seq + [nxt], new_has_lt, new_has_rt, new_fL, new_fR)

            if len(results) >= 10000:
                return

    # Start: the first mover in the phase. It must be ring-adjacent to previous t-fire.
    # So mover at position a is ring-adjacent to t: lt or rt.
    # But actually the start could be further away. Let me think...
    # Phase [a, s): moverAt(a) is the first mover after previous t-fire.
    # Previous mover was t (at a-1). So moverAt(a) must be ring-adj to t.
    for start in [lt, rt]:
        has_lt = (start == lt)
        has_rt = (start == rt)
        fL = 0 if start == lt else None
        fR = 0 if start == rt else None
        dfs([start], has_lt, has_rt, fL, fR)

    return results


def check_ec_in_phase_abstract(mover_seq, n, ms, t):
    """
    Given a mover sequence for a phase, try to construct configs and check EC.

    We track the state at each step. For simplicity, we work with binary
    processors as Z/2 and ternary as Z/m.

    At each step, the mover changes its value. The boundary triple at the
    mover determines the new value (via transition function).

    Under ¬EC: for every non-mover p at step k, the boundary triple (L,S,R)
    at p must NOT equal any boundary triple at p when p is the mover.

    Key insight: we don't need to fix transition functions. We just need to
    check if the CONFIG CONSTRAINTS force an EC.
    """
    pass


def analyze_mover_sequences(n, ms, t):
    """Analyze the structure of sorry-pattern mover sequences."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n

    print(f"n={n}, t={t}, lt={lt}, rt={rt}, llt={llt}, rrt={rrt}")
    print(f"ms={ms}")
    print()

    seqs = enumerate_adjacent_mover_sequences(n, t, max_len=15)
    print(f"Found {len(seqs)} sorry-pattern mover sequences (max_len=15)")

    if not seqs:
        print("No sequences found!")
        return

    # Analyze structure
    len_counts = defaultdict(int)
    for seq in seqs:
        len_counts[len(seq)] += 1

    print("\nSequence length distribution:")
    for l in sorted(len_counts):
        print(f"  len={l}: {len_counts[l]}")

    # Show first few
    print("\nFirst 20 sequences:")
    for seq in seqs[:20]:
        # Annotate: L=lt, R=rt, T=t, LL=llt, RR=rrt, else number
        names = {lt: 'L', rt: 'R', t: 'T', llt: 'LL', rrt: 'RR'}
        annotated = [names.get(m, str(m)) for m in seq]
        print(f"  {' '.join(annotated)}")

    # Key question: in these sequences, which processors change state?
    # And what parity constraints arise?
    print("\n=== Parity analysis ===")
    for seq in seqs[:10]:
        fire_counts = defaultdict(int)
        for m in seq[:-1]:  # exclude final t-fire
            fire_counts[m] += 1

        parity_info = {}
        for p in range(n):
            fc = fire_counts.get(p, 0)
            if ms[p] == 2:
                parity_info[p] = f"{'even' if fc % 2 == 0 else 'odd'}({fc})"
            else:
                parity_info[p] = f"{fc}"

        names = {lt: 'L', rt: 'R', t: 'T', llt: 'LL', rrt: 'RR'}
        annotated = [names.get(m, str(m)) for m in seq]
        print(f"  {' '.join(annotated)}")
        for p in sorted(parity_info):
            pname = names.get(p, str(p))
            print(f"    {pname}(proc {p}, m={ms[p]}): fires={parity_info[p]}")

    return seqs


def simulate_phase_with_ec_check(n, ms, t, mover_seq, num_trials=50000):
    """
    For a given mover sequence, generate random initial configs + transitions,
    build the config sequence step by step, then check for EC.

    This doesn't require a full valid good cycle -- just a consistent segment.
    """
    lt = (t - 1) % n
    rt = (t + 1) % n
    CL = len(mover_seq)

    ec_at = defaultdict(int)
    no_ec_count = 0
    invalid_count = 0
    total = 0

    for trial in range(num_trials):
        # Random transition function
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        # Random initial config
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
                # Not privileged -> invalid execution
                valid = False
                break
            nc = list(config)
            nc[p] = new_val
            config = tuple(nc)
            configs.append(config)

        if not valid:
            invalid_count += 1
            continue

        # Check distinct configs
        if len(set(configs)) != len(configs):
            invalid_count += 1
            continue

        total += 1

        # Check EC at each processor
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
            overlap = mover_triples & nonmover_triples
            if overlap:
                ec_at[p] += 1
                found_ec = True

        if not found_ec:
            no_ec_count += 1

    return total, ec_at, no_ec_count, invalid_count


def main():
    n = 9
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
    t = 1

    print("=== Phase 1: Enumerate sorry-pattern mover sequences ===")
    seqs = analyze_mover_sequences(n, ms, t)

    if not seqs:
        return

    print("\n=== Phase 2: Simulate phases with random transitions ===")
    # Pick a few representative sequences
    test_seqs = seqs[:min(20, len(seqs))]

    names = {0: 'L', 2: 'R', 1: 'T', 8: 'LL', 3: 'RR'}

    for idx, seq in enumerate(test_seqs):
        annotated = [names.get(m, str(m)) for m in seq]
        total, ec_at, no_ec, invalid = simulate_phase_with_ec_check(n, ms, t, seq, num_trials=50000)
        print(f"\nSeq {idx}: {' '.join(annotated)}  (len={len(seq)})")
        print(f"  Valid trials: {total}, no-EC: {no_ec}")
        if total > 0:
            for p in range(n):
                if ec_at.get(p, 0) > 0:
                    pname = names.get(p, str(p))
                    print(f"    EC at {pname}(proc {p}): {ec_at[p]}/{total} = {ec_at[p]/total:.3f}")

    # Summarize: which processor ALWAYS has EC?
    print("\n=== Phase 3: Check if EC is universal at some processor ===")
    # Run more trials on shortest sequences
    shortest = min(len(s) for s in seqs)
    short_seqs = [s for s in seqs if len(s) == shortest][:5]

    for idx, seq in enumerate(short_seqs):
        annotated = [names.get(m, str(m)) for m in seq]
        total, ec_at, no_ec, invalid = simulate_phase_with_ec_check(n, ms, t, seq, num_trials=200000)
        print(f"\nSeq: {' '.join(annotated)}  (len={len(seq)})")
        print(f"  Valid: {total}, no-EC: {no_ec} ({no_ec/max(total,1)*100:.2f}%)")
        for p in range(n):
            if ec_at.get(p, 0) > 0:
                pname = names.get(p, str(p))
                print(f"    EC at {pname}(proc {p}): {ec_at[p]}/{total} = {ec_at[p]/total:.3f}")


if __name__ == '__main__':
    main()
