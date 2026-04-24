#!/usr/bin/env python3
"""
Collective Pigeonhole Part 5: The REAL collective argument.

DISCOVERY: The collective pigeonhole across binary procs FAILS.
Binary procs use only 6/18 context slots — far too little pressure.

But EC at TERNARY procs is forced for the V-word (and all non-sweep words).
The existing Palindromic Entry Conflict (CIC Expl 14) explains why:
consecutive binary procs create a palindromic constraint that forces
EC at the ternary procs adjacent to the binary block.

Let me now investigate: can we unify the collective argument?

REFINED CONJECTURE: For any non-sweep fc=2 word on a ring with ≥3 binary
at sub-threshold product, the ternary procs in the "interior" of the
bidirectional walk segment have entry conflict.

The mechanism: at a non-sweep turnaround, the walk reverses direction.
A ternary proc j that appears as both a CW mover and a CCW nonmover
(or vice versa) sees the SAME (L,R) context but different mover/nonmover
roles — forcing EC if the S values match.

Formal verification of the mechanism for all non-sweep types.
"""

from itertools import product as iproduct
from collections import Counter


def enumerate_fc2_walks(n):
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == 2 * n:
            nxt = path[0]
            if abs(pos - nxt) == 1 or abs(pos - nxt) == n - 1:
                if all(f == 2 for f in fc):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < 2:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    unique = set()
    result = []
    for w in walks:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def is_sweep(word, n):
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    return all(d == 1 for d in dirs) or all(d == n - 1 for d in dirs)


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def build_good_cycle(word, n, ms, combo):
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]


def analyze_ec_mechanism(word, n, ms, good):
    """For each proc with EC, identify the mechanism:
    which step pairs cause the mover/nonmover overlap?"""
    L = len(word)
    results = {}

    for j in range(n):
        mover_info = []  # (step, ctx, new_S)
        nonmover_info = []  # (step, ctx, S)

        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            ctx = (c[(j-1)%n], c[j], c[(j+1)%n])
            if word[t] == j:
                mover_info.append((t, ctx, cn[j]))
            else:
                nonmover_info.append((t, ctx, c[j]))

        # Find overlapping contexts
        mover_ctx_map = {info[1]: info for info in mover_info}
        overlaps = []
        for t, ctx, s in nonmover_info:
            if ctx in mover_ctx_map:
                mt, mctx, mnew = mover_ctx_map[ctx]
                overlaps.append({
                    'mover_step': mt,
                    'nonmover_step': t,
                    'ctx': ctx,
                    'mover_new_S': mnew,
                    'nonmover_S': s,
                })

        if overlaps:
            # Classify: what's the walk direction at mover step vs nonmover step?
            for ov in overlaps:
                mt = ov['mover_step']
                nt = ov['nonmover_step']
                mdir = (word[(mt+1)%L] - word[mt]) % n
                if mdir > n//2:
                    mdir -= n
                # At nonmover step, j is not the mover
                # Walk direction at that step
                ndir = (word[(nt+1)%L] - word[nt]) % n
                if ndir > n//2:
                    ndir -= n
                ov['mover_walk_dir'] = mdir
                ov['nonmover_walk_dir'] = ndir

            results[j] = {
                'mover': mover_info,
                'nonmover': nonmover_info,
                'overlaps': overlaps,
            }

    return results


def main():
    print("=" * 80)
    print("EC MECHANISM ANALYSIS: WHERE and WHY does EC happen?")
    print("=" * 80)

    for n in [5, 7, 9]:
        ms = [2, 2, 2] + [3] * (n - 3)
        print(f"\n{'='*70}")
        print(f"n = {n}, ms = {ms}")
        print(f"{'='*70}")

        walks = enumerate_fc2_walks(n)
        non_sweep = [w for w in walks if not is_sweep(w, n)]

        for w in non_sweep:
            L = len(w)
            fc = Counter(w)
            proc_seqs = {p: enumerate_state_sequences(ms[p], fc.get(p,0)) for p in range(n)}
            sl = [proc_seqs[p] for p in range(n)]

            # Use first valid combo
            for combo in iproduct(*sl):
                good = build_good_cycle(w, n, ms, combo)
                if good is None:
                    continue

                # Get walk structure
                dirs = []
                for t in range(L):
                    d = (w[(t+1)%L] - w[t]) % n
                    if d > n//2:
                        d -= n
                    dirs.append(d)
                turns = sum(1 for t in range(L) if dirs[t] != dirs[(t-1)%L])

                results = analyze_ec_mechanism(w, n, ms, good)
                ec_procs = sorted(results.keys())

                binary_ec = [j for j in ec_procs if ms[j] == 2]
                ternary_ec = [j for j in ec_procs if ms[j] == 3]

                print(f"\n  Word: {w} ({turns}-turn)")
                print(f"  EC at binary: {binary_ec}, ternary: {ternary_ec}")
                print(f"  Total EC procs: {len(ec_procs)}/{n}")

                # For first ternary EC proc, show mechanism
                if ternary_ec:
                    j = ternary_ec[0]
                    ov = results[j]['overlaps'][0]
                    print(f"  First ternary EC (proc {j}):")
                    print(f"    ctx = {ov['ctx']}")
                    print(f"    mover step {ov['mover_step']}: "
                          f"walk_dir={ov['mover_walk_dir']}, "
                          f"new_S={ov['mover_new_S']}")
                    print(f"    nonmover step {ov['nonmover_step']}: "
                          f"walk_dir={ov['nonmover_walk_dir']}, "
                          f"S={ov['nonmover_S']}")

                    # Key: is the nonmover step during the REVERSE pass?
                    cw_steps = [t for t in range(L) if dirs[t] == 1]
                    ccw_steps = [t for t in range(L) if dirs[t] == -1]
                    mt_dir = 'CW' if ov['mover_walk_dir'] == 1 else 'CCW'
                    nt_dir = 'CW' if ov['nonmover_walk_dir'] == 1 else 'CCW'
                    print(f"    Mover during {mt_dir} pass, nonmover during {nt_dir} pass")
                    opposite = (mt_dir != nt_dir)
                    print(f"    Opposite directions: {opposite}")

                break  # First combo only

    # COUNT: how many ternary procs have EC for each word type?
    print("\n" + "=" * 80)
    print("TERNARY EC COUNT BY WORD TYPE")
    print("=" * 80)

    for n in [5, 6, 7, 8, 9]:
        ms = [2, 2, 2] + [3] * (n - 3)
        walks = enumerate_fc2_walks(n)
        non_sweep = [w for w in walks if not is_sweep(w, n)]

        print(f"\nn={n}, {len(non_sweep)} non-sweep words:")

        for w in non_sweep:
            L = len(w)
            fc = Counter(w)
            proc_seqs = {p: enumerate_state_sequences(ms[p], fc.get(p,0)) for p in range(n)}
            sl = [proc_seqs[p] for p in range(n)]

            # Count EC across ALL combos: what's the minimum # of ternary EC procs?
            min_ternary_ec = n
            max_ternary_ec = 0

            count = 0
            for combo in iproduct(*sl):
                good = build_good_cycle(w, n, ms, combo)
                if good is None:
                    continue
                count += 1

                ternary_ec = 0
                binary_ec = 0
                for j in range(n):
                    mctx = set()
                    nctx = set()
                    for t in range(L):
                        c = good[t]
                        ctx = (c[(j-1)%n], c[j], c[(j+1)%n])
                        if w[t] == j:
                            mctx.add(ctx)
                        else:
                            nctx.add(ctx)
                    if mctx & nctx:
                        if ms[j] == 3:
                            ternary_ec += 1
                        else:
                            binary_ec += 1

                min_ternary_ec = min(min_ternary_ec, ternary_ec)
                max_ternary_ec = max(max_ternary_ec, ternary_ec)

            dirs = []
            for t in range(L):
                d = (w[(t+1)%L] - w[t]) % n
                if d > n//2:
                    d -= n
                dirs.append(d)
            turns = sum(1 for t in range(L) if dirs[t] != dirs[(t-1)%L])

            print(f"  {w}: {turns}-turn, combos={count}, "
                  f"ternary_EC=[{min_ternary_ec}, {max_ternary_ec}]")


if __name__ == '__main__':
    main()
