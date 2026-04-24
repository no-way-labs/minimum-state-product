#!/usr/bin/env python3
"""
RA12: Check asymmetric placements for longer cycles and
verify EC-free walks can/cannot form valid systems.

Part 1: For asymmetric placements with 0 min-length walks,
check if walks exist at longer lengths.

Part 2: For the 8 EC-free walks at (3,3,3), attempt to build
a valid self-stabilizing system containing the cycle.
"""

from itertools import combinations, product as iproduct
from collections import Counter
import time


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
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


def enumerate_walks_multi(n, ms, fc_mult):
    """Enumerate ring walks where fc[p] = fc_mult * ms[p]."""
    target_fc = [fc_mult * ms[p] for p in range(n)]
    total_len = sum(target_fc)
    walks = []

    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == total_len:
            nxt = path[0]
            if abs(pos - nxt) % n in (1, n - 1):
                if all(fc[p] == target_fc[p] for p in range(n)):
                    walks.append(tuple(path))
            return
        # Pruning: remaining steps
        remaining = total_len - step
        needed = sum(max(0, target_fc[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1

    for p0 in range(n):
        if target_fc[p0] > 0:
            fc = [0] * n
            fc[p0] = 1
            dfs([p0], fc)

    # Deduplicate under rotation
    unique = set()
    result = []
    for w in walks:
        ell = len(w)
        best = w
        for i in range(ell):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(w)
    return result


def has_ec_any_combo(word, n, ms):
    """Check if there exists ANY state-seq combo without EC for this word."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
    sl = [proc_seqs[p] for p in range(n)]

    total = 0
    ec_free = 0

    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue
        total += 1
        good = configs[:L]

        has_conflict = False
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            mover_ctxs = set()
            nonmover_ctxs = set()
            for t in range(L):
                ctx = (good[t][Lp], good[t][j], good[t][Rp])
                if word[t] == j:
                    next_val = good[(t + 1) % L][j]
                    if next_val != ctx[1]:
                        mover_ctxs.add(ctx)
                else:
                    nonmover_ctxs.add(ctx)
            if mover_ctxs & nonmover_ctxs:
                has_conflict = True
                break
        if not has_conflict:
            ec_free += 1

    return total, ec_free


def check_system_completion(word, n, ms, combo):
    """Given a good cycle (word + state-seq combo), try to complete it
    to a valid self-stabilizing system. Check if there's a consistent
    transition function that:
    1. Makes the good cycle a valid good cycle
    2. Has no OTHER good cycle (which would break convergence)

    Actually, just check if transition tables are consistent
    (no conflicting entries).
    """
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    good = configs[:L]

    # Extract transition table entries
    tables = {}  # (proc, L, S, R) -> required_output
    conflicts = []

    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        mover = word[t]

        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            key = (j, c[Lp], c[j], c[Rp])

            if j == mover:
                # Must change to cn[j]
                required = cn[j]
            else:
                # Must stay at c[j]
                required = c[j]

            if key in tables:
                if tables[key] != required:
                    conflicts.append((key, tables[key], required))
            else:
                tables[key] = required

    return len(conflicts) == 0, len(tables), conflicts


def main():
    n = 9
    threshold = 4 * (3 ** 7)

    print("=" * 70)
    print("RA12: Asymmetric placement check + system completion")
    print("=" * 70)

    # Part 1: Check if asymmetric placements have ANY walks
    print(f"\nPART 1: Asymmetric placements - do walks exist at any length?")
    print("-" * 70)

    asymmetric = [
        ((0, 2, 4), (2, 2, 5)),
        ((0, 2, 5), (2, 3, 4)),
        ((0, 2, 6), (2, 4, 3)),
    ]

    for pos, gaps in asymmetric:
        ms = make_ms(n, pos)
        print(f"\nPlacement: pos={pos}, gaps={gaps}, ms={ms}")

        # Why might there be 0 walks? Check parity/reachability.
        # A ring walk of length L starting at p must return to a neighbor of p.
        # The net displacement mod n must be +1 or -1 (mod n).
        # With fc[p] = ms[p], total steps = sum(ms) = 24.
        # Each step moves +1 or -1. Net displacement = sum of directions.
        # For a valid cycle: net displacement = +1 or -1 (mod n).
        # But sum of 24 directions, each +/-1, has parity = 24 mod 2 = 0.
        # So net displacement is EVEN. But we need +1 or -1 (odd). IMPOSSIBLE!
        # Wait -- wrap-adjacency means last->first is adjacent.
        # The walk visits L=24 procs: word[0], word[1], ..., word[23].
        # Adjacency condition: |word[23] - word[0]| = 1 mod n.
        # This is a property of the walk, not displacement.
        # Actually the walk is a sequence of n-valued positions.
        # Let me reconsider...

        # The walk consists of steps where each step goes to an adjacent proc.
        # So word[t+1] = word[t] +/- 1 (mod n).
        # The total walk is L=24 steps.
        # The "displacement" from word[0] to word[23] is the sum of 23 steps.
        # For wrap-adjacency, |word[23] - word[0]| = 1 (mod n).
        # So the displacement after 23 steps must be +1 or -1 (mod n).
        # Each step is +1 or -1, so displacement parity = 23 mod 2 = 1 (odd). OK!

        # But we also need fc[p] = ms[p] for each p.
        # Let's check what fc constraint implies about the walk structure.

        # Detailed check: try longer walks (mult=2 gives length 48)
        for mult in [1]:
            target_fc = [mult * ms[p] for p in range(n)]
            total_len = sum(target_fc)
            print(f"  mult={mult}: target length={total_len}, "
                  f"target_fc={target_fc}")

            # Check parity constraint
            # After total_len-1 steps, displacement parity = (total_len-1) % 2
            disp_parity = (total_len - 1) % 2
            print(f"  Displacement parity after {total_len-1} steps: {disp_parity}")
            print(f"  Need displacement +/-1 (odd): "
                  f"{'POSSIBLE' if disp_parity == 1 else 'IMPOSSIBLE (parity)'}")

            if disp_parity != 1:
                print(f"  PARITY BLOCKS min-length walks!")
                continue

            t0 = time.time()
            walks = enumerate_walks_multi(n, ms, mult)
            t1 = time.time()
            print(f"  Walks found: {len(walks)} ({t1-t0:.1f}s)")

            if walks and mult <= 1:
                for w in walks[:3]:
                    total_v, ec_f = has_ec_any_combo(w, n, ms)
                    print(f"    Walk {list(w)[:8]}...: valid={total_v}, EC-free={ec_f}")

    # Hmm, but the (3,3,3) placement DID have walks. Let me check its parity.
    ms_sym = make_ms(n, (0, 3, 6))
    total_sym = sum(ms_sym)
    disp_sym = (total_sym - 1) % 2
    print(f"\n(3,3,3) check: total_len={total_sym}, "
          f"disp_parity={(total_sym-1)%2}")

    # ALL have total_len=24, disp_parity=1 (odd). So parity is fine.
    # The issue must be structural — the walk can't visit all procs
    # the right number of times with the asymmetric placement.

    # Let me check: for (2,2,5) placement (binary at 0,2,4),
    # binary procs need fc=2, ternary need fc=3.
    # The walk must pass through 5 consecutive ternary procs (P5..P8,P0 is binary).
    # To visit each of P5,P6,P7,P8 exactly 3 times in a ring walk...
    # The walk must traverse the arc P5-P6-P7-P8 back and forth.

    # Let me verify by just checking all starting procs more carefully.
    print(f"\nDetailed walk check for (2,2,5):")
    ms_check = make_ms(n, (0, 2, 4))
    print(f"  ms={ms_check}")
    print(f"  Binary: P0(fc=2), P2(fc=2), P4(fc=2)")
    print(f"  Ternary: P1(fc=3), P3(fc=3), P5(fc=3), P6(fc=3), P7(fc=3), P8(fc=3)")

    # For minimum cycle, try just binary starting
    for p0 in range(n):
        count = 0
        def dfs_count(path, fc, limit=10000):
            nonlocal count
            if count >= limit:
                return
            pos = path[-1]
            step = len(path)
            if step == 24:
                nxt = path[0]
                if abs(pos - nxt) % n in (1, n - 1):
                    if all(fc[p] == ms_check[p] for p in range(n)):
                        count += 1
                return
            remaining = 24 - step
            needed = sum(max(0, ms_check[p] - fc[p]) for p in range(n))
            if needed > remaining:
                return
            for d in [1, -1]:
                nxt = (pos + d) % n
                if fc[nxt] < ms_check[nxt]:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs_count(path, fc, limit)
                    path.pop()
                    fc[nxt] -= 1

        fc = [0] * n
        fc[p0] = 1
        dfs_count([p0], fc)
        if count > 0:
            print(f"  Starting at P{p0}: {count} walks")

    if count == 0:
        print(f"  NO walks exist for (2,2,5) at min length!")

    # Part 2: System completion for EC-free walks
    print(f"\n\n{'='*70}")
    print("PART 2: System completion check for EC-free walks at (3,3,3)")
    print("=" * 70)

    ms = make_ms(n, (0, 3, 6))
    walks = enumerate_walks_multi(n, ms, 1)
    ec_free_walks = []

    for word in walks:
        proc_seqs = {p: enumerate_state_sequences(ms[p], ms[p]) for p in range(n)}
        sl = [proc_seqs[p] for p in range(n)]
        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            fcc = [0] * n
            configs = [tuple(ss[p][0] for p in range(n))]
            for t in range(len(word)):
                fcc[word[t]] += 1
                configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
            if configs[-1] != configs[0]:
                continue
            if len(set(configs[:len(word)])) != len(word):
                continue
            good = configs[:len(word)]

            # Check EC
            has_conflict = False
            for j in range(n):
                Lp = (j - 1) % n
                Rp = (j + 1) % n
                mc = set()
                nc = set()
                for t in range(len(word)):
                    ctx = (good[t][Lp], good[t][j], good[t][Rp])
                    if word[t] == j:
                        nv = good[(t + 1) % len(word)][j]
                        if nv != ctx[1]:
                            mc.add(ctx)
                    else:
                        nc.add(ctx)
                if mc & nc:
                    has_conflict = True
                    break

            if not has_conflict:
                ec_free_walks.append((word, combo))

    print(f"Total EC-free (word, combo) pairs: {len(ec_free_walks)}")

    # Check system completion for first few
    consistent = 0
    inconsistent = 0
    for word, combo in ec_free_walks[:10]:
        ok, num_entries, conflicts = check_system_completion(word, n, ms, combo)
        if ok:
            consistent += 1
            print(f"  CONSISTENT: word start={list(word)[:6]}..., "
                  f"{num_entries} table entries, no conflicts")
        else:
            inconsistent += 1

    print(f"\nConsistent: {consistent}/{min(10, len(ec_free_walks))}")
    print(f"Inconsistent: {inconsistent}/{min(10, len(ec_free_walks))}")

    # If consistent, that means transition tables have no internal conflicts
    # But this doesn't mean a VALID system exists (need convergence too)
    if consistent > 0:
        print("\nWARNING: Consistent means no EC, but system might still")
        print("fail due to: shadow cycles, additional good cycles, liveness, etc.")
        print("EC is a SUFFICIENT obstruction, not necessary.")


if __name__ == "__main__":
    main()
