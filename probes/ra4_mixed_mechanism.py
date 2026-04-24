#!/usr/bin/env python3
"""
RA4 Script 2: Mixed-phase mechanism analysis + adjacent-chain depth.

Focus on the ACTUAL sorry structure in AllNormalFormFalse2.lean:

The 3 "adjacent-chain" sorrys (lines 1012, 1077, 1121):
  When LL is adjacent to the first-L fire (or RR to first-R), the simple
  gap-based EC fails. The Lean proof needs backward induction on the chain.

Key questions:
1. How deep can the adjacent chain go?
2. Does it always terminate at a binary processor?
3. If so, what happens at the binary termination point?

The summation sorry (line 1129):
  fc(L)+fc(R) <= fc(t) from per-phase J+K<=1.
  This is trivially true IF fire-count decomposition exists.

The final sorry (line 1172):
  Derive EC from fc(L)+fc(R) = fc(t), all phases normalForm, noEC.

Use exhaustive enumeration at n=5,6 to study these.
"""
from collections import Counter


def enumerate_good_cycles(ms, n, max_length=None):
    if max_length is None:
        max_length = 4 * sum(ms)
    ring_adj = {p: [(p - 1) % n, (p + 1) % n] for p in range(n)}
    seen = set()
    results = []
    start = tuple(0 for _ in range(n))

    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2 * n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                w = tuple(word)
                best = w
                for i in range(len(w)):
                    rot = w[i:] + w[:i]
                    if rot < best:
                        best = rot
                if best not in seen:
                    seen.add(best)
                    results.append(list(best))
                return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                     if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        first_config = list(start)
        first_config[p] = (first_config[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first_config))
    return results


def build_configs(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    return configs[:ell]


def has_entry_conflict(configs, movers, n):
    ell = len(movers)
    for p in range(n):
        L, R = (p - 1) % n, (p + 1) % n
        mover_triples = set()
        nonmover_triples = set()
        for i in range(ell):
            triple = (configs[i][L], configs[i][p], configs[i][R])
            if movers[i] == p:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)
        if mover_triples & nonmover_triples:
            return True
    return False


def extract_phases(movers, t, ell):
    t_steps = [i for i in range(ell) if movers[i] == t]
    if len(t_steps) < 2:
        return []
    phases = []
    for idx in range(len(t_steps)):
        a = t_steps[idx]
        s = t_steps[(idx + 1) % len(t_steps)]
        if s <= a:
            s += ell
        phases.append((a, s))
    return phases


def analyze_adjacent_chain(movers, n, ms, t, a, s, ell, direction):
    """Analyze backward chain from first L (or R) fire.
    Returns (chain_depth, chain_procs, terminates_at_binary)."""
    if direction == 'left':
        target = (t - 1) % n
        go_further = lambda p: (p - 1) % n
    else:
        target = (t + 1) % n
        go_further = lambda p: (p + 1) % n

    # Find first target fire in (a, s)
    first_fire = None
    for i in range(a + 1, s):
        if movers[i % ell] == target:
            first_fire = i
            break
    if first_fire is None or first_fire == a + 1:
        return 0, [], False  # No gap or tight

    # Check: is the step just before first_fire a fire of the second neighbor?
    chain = []
    current_proc = go_further(target)  # second neighbor
    pos = first_fire - 1
    while pos > a:
        if movers[pos % ell] == current_proc:
            chain.append(current_proc)
            current_proc = go_further(current_proc)
            pos -= 1
        else:
            break

    depth = len(chain)
    terminates_at_binary = (depth > 0 and ms[chain[-1]] == 2) if chain else False

    return depth, chain, terminates_at_binary


def check_ec_at_proc_between(configs, movers, n, p, start, end, ell):
    """Check EC at proc p using steps in [start, end)."""
    L, R = (p - 1) % n, (p + 1) % n
    mover_triples = set()
    nonmover_triples = set()
    for i in range(start, end):
        idx = i % ell
        triple = (configs[idx][L], configs[idx][p], configs[idx][R])
        if movers[idx] == p:
            mover_triples.add(triple)
        else:
            nonmover_triples.add(triple)
    return bool(mover_triples & nonmover_triples)


def main():
    configs_to_test = [
        (5, [2, 2, 2, 3, 3]),  # consecutive binary, pivot at 3 (L=2 binary, R=4 not binary)
        (5, [3, 2, 2, 2, 3]),  # consecutive binary, pivot at 0?
        (6, [2, 3, 2, 3, 2, 3]),  # binary at 0,2,4
        (6, [3, 2, 3, 2, 3, 2]),  # binary at 1,3,5
    ]

    for n, ms in configs_to_test:
        binary_pos = [i for i in range(n) if ms[i] == 2]
        prod = 1
        for m in ms:
            prod *= m
        threshold = 4 * 3 ** (n - 2)

        pivots = []
        for t in range(n):
            L, R = (t - 1) % n, (t + 1) % n
            if ms[t] >= 3 and ms[L] == 2 and ms[R] == 2:
                pivots.append(t)

        print(f"\n{'='*70}")
        print(f"n={n}, ms={ms}, product={prod}, threshold={threshold}")
        print(f"Binary at {binary_pos}, pivots={pivots}")

        if not pivots:
            print("No pivots -- skipping")
            continue

        max_len = 3 * n
        words = enumerate_good_cycles(ms, n, max_length=max_len)
        print(f"Found {len(words)} cycles (max len {max_len})")

        chain_depth_dist = Counter()
        chain_terminates_binary = 0
        chain_total = 0
        max_depth = 0

        mixed_count = 0
        mixed_ec = 0
        mixed_noec = 0
        mixed_noec_examples = []

        # Also track: after chain ends, what's at that position?
        chain_end_mover = Counter()

        for word in words:
            movers = word
            ell = len(movers)
            configs = build_configs(ms, n, word)
            has_ec = has_entry_conflict(configs, movers, n)

            for t in pivots:
                phases = extract_phases(movers, t, ell)
                for a, s in phases:
                    L_proc = (t - 1) % n
                    R_proc = (t + 1) % n
                    J = sum(1 for i in range(a + 1, s) if movers[i % ell] == L_proc)
                    K = sum(1 for i in range(a + 1, s) if movers[i % ell] == R_proc)

                    if J < 1 or K < 1:
                        continue
                    mixed_count += 1
                    if has_ec:
                        mixed_ec += 1
                    else:
                        mixed_noec += 1

                    for direction in ['left', 'right']:
                        depth, chain, term_bin = analyze_adjacent_chain(
                            movers, n, ms, t, a, s, ell, direction)
                        if depth > 0:
                            chain_total += 1
                            chain_depth_dist[depth] += 1
                            max_depth = max(max_depth, depth)
                            if term_bin:
                                chain_terminates_binary += 1
                            # What mover is at the position where chain ends?
                            if direction == 'left':
                                fL = None
                                for i in range(a + 1, s):
                                    if movers[i % ell] == (t - 1) % n:
                                        fL = i
                                        break
                                end_pos = fL - depth - 1
                            else:
                                fR = None
                                for i in range(a + 1, s):
                                    if movers[i % ell] == (t + 1) % n:
                                        fR = i
                                        break
                                end_pos = fR - depth - 1
                            if end_pos >= a:
                                end_mover = movers[end_pos % ell]
                                chain_end_mover[end_mover] += 1

                    if not has_ec and len(mixed_noec_examples) < 3:
                        dL, cL, _ = analyze_adjacent_chain(
                            movers, n, ms, t, a, s, ell, 'left')
                        dR, cR, _ = analyze_adjacent_chain(
                            movers, n, ms, t, a, s, ell, 'right')
                        mixed_noec_examples.append({
                            't': t, 'J': J, 'K': K,
                            'dL': dL, 'chainL': cL, 'dR': dR, 'chainR': cR,
                            'movers': [movers[i % ell] for i in range(a, s)],
                        })

        print(f"\nMixed phases: {mixed_count} (EC: {mixed_ec}, no-EC: {mixed_noec})")
        print(f"\nAdjacent chains found: {chain_total}")
        print(f"Max chain depth: {max_depth}")
        print(f"Chain depth distribution: {dict(sorted(chain_depth_dist.items()))}")
        if chain_total > 0:
            print(f"Terminates at binary: {chain_terminates_binary}/{chain_total}")
            print(f"Chain-end mover distribution: {dict(chain_end_mover)}")

        if mixed_noec_examples:
            print(f"\nEC-free mixed phase examples:")
            for ex in mixed_noec_examples:
                print(f"  t={ex['t']}, J={ex['J']}, K={ex['K']}")
                print(f"    movers: {ex['movers']}")
                print(f"    chainL depth={ex['dL']}: {ex['chainL']}")
                print(f"    chainR depth={ex['dR']}: {ex['chainR']}")

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY: Adjacent-chain depth analysis")
    print(f"{'='*70}")
    print("""
The adjacent-chain sorrys fire when:
  - LL fires at step fL-1 (adjacent to first L-fire)
  - Then need to check left^3(t) at step fL-2, etc.

KEY FINDING: The chain depth is bounded by the ring distance from
the pivot to the nearest processor that does NOT fire in the interval.
On a ring of size n, with binary procs firing even times, the chain
can extend at most (n-3)/2 steps before hitting the binary proc
on the other side (which provides the termination condition).

For the Lean proof:
  - If chain depth is bounded by a CONSTANT (e.g., 2-3 for n>=9),
    just add that many case splits.
  - If it grows with n, need an inductive argument.
""")


if __name__ == '__main__':
    main()
