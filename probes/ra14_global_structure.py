#!/usr/bin/env python3
"""
ra14_global_structure.py — Understand the global EC structure.

Key question: The anatomy showed EC exists at SOME proc for every OW-NU word.
But not every B-T-B has EC. So what's the GLOBAL argument?

New approach: look at binary processors. For binary p:
- fc(p) = 2 (fires exactly twice)
- pfc_p takes values 0, 1 across the cycle
- At mover step 1: pfc_p = 0; at mover step 2: pfc_p = 1
- Non-mover steps have pfc_p in {0, 1, 0} pattern (0 before first fire, 1 between fires, 0 after)

For binary p with non-consecutive binary:
- Both neighbors are ternary: space = 3 * 2 * 3 = 18
- CL = 3n-3 for n >= 5

But wait: at binary p, the mover steps have pfc_p = 0 and 1.
So there's one mover at pfc_p=0, one at pfc_p=1.
Non-movers split into three phases:
  Phase 0: pfc_p=0 (before first fire)
  Phase 1: pfc_p=1 (between fires)
  Phase 2: pfc_p=0 again (after second fire, since 2 mod 2 = 0)

The mover at pfc_p=0 conflicts with non-movers in Phase 0 or Phase 2 if
(pfc_L mod 3, pfc_R mod 3) matches.

The mover at pfc_p=1 conflicts with non-movers in Phase 1 if
(pfc_L mod 3, pfc_R mod 3) matches.

For pfc_p=0 mover: residue pair is (pfc_L(s1) mod 3, pfc_R(s1) mod 3).
For pfc_p=0 non-movers: same formula but at different steps.

Space for (pfc_L mod 3, pfc_R mod 3) = 9 points.

How many non-mover steps have pfc_p=0? All steps before first p-fire + all steps after last p-fire.
The mover at pfc_p=0 needs to be "hidden" from all these non-movers in the 9-element space.

Let's count precisely.
"""
import time
from itertools import combinations
from collections import defaultdict, Counter


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def gen_words(n, fc_target, max_results=500, timeout_s=15):
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
            dfs([start], fc)
    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def analyze_binary_phases(word, n, ms):
    """
    For each binary processor p, analyze the phase structure.
    Binary p fires 2 times.
    pfc_p mod 2 partitions steps into parity-0 and parity-1.
    """
    L = len(word)
    results = []

    for p in range(n):
        if ms[p] != 2:
            continue
        lp = (p - 1) % n
        rp = (p + 1) % n

        pfc = {}
        for q in range(n):
            pfc[q] = [0] * (L + 1)
            for t in range(L):
                pfc[q][t + 1] = pfc[q][t] + (1 if word[t] == q else 0)

        # Find the two mover steps for p
        mover_steps = [t for t in range(L) if word[t] == p]
        assert len(mover_steps) == 2

        # For each mover step, what's the (pfc_L mod m_L, pfc_R mod m_R) pair?
        # And pfc_p mod 2 (should be 0 for first fire, 1 for second)
        for s1 in mover_steps:
            parity_p = pfc[p][s1] % 2
            pair_LR = (pfc[lp][s1] % ms[lp], pfc[rp][s1] % ms[rp])

            # Count non-mover steps with same pfc_p parity
            nonmover_same_parity = []
            for t in range(L):
                if word[t] != p and pfc[p][t] % 2 == parity_p:
                    nonmover_same_parity.append(t)

            nonmover_pairs = set()
            for t in nonmover_same_parity:
                nonmover_pairs.add((pfc[lp][t] % ms[lp], pfc[rp][t] % ms[rp]))

            ec = pair_LR in nonmover_pairs
            results.append({
                'p': p,
                'parity': parity_p,
                'mover_pair': pair_LR,
                'nonmover_count': len(nonmover_same_parity),
                'nonmover_distinct_pairs': len(nonmover_pairs),
                'space_size': ms[lp] * ms[rp],
                'ec': ec,
            })

    return results


def main():
    print("RA14: Global EC Structure - Binary Phase Analysis")
    print("=" * 70)

    # First: understand the decomposition.
    # For binary p (fc=2, ms=2):
    #   Mover at pfc_p=0: one step. Pair in {0,..,m_L-1} x {0,..,m_R-1}.
    #   Mover at pfc_p=1: one step. Pair in same space.
    #   Non-mover at pfc_p=0: some steps. Their pairs cover a subset.
    #   Non-mover at pfc_p=1: some steps. Their pairs cover a subset.
    #
    # EC at (p, parity=0) iff mover pair at parity=0 is in non-mover pairs at parity=0.
    # EC at (p, parity=1) iff mover pair at parity=1 is in non-mover pairs at parity=1.
    #
    # For non-consecutive binary: neighbors are ternary, space = 3x3 = 9.
    #
    # How many non-mover steps at each parity?
    # Steps at parity 0: all steps before first p-fire + all steps after second p-fire (wrapping)
    # Steps at parity 1: all steps between first and second p-fire
    # Minus the 1 mover step at each parity.

    for n in [5, 7]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\nn={n}, threshold={threshold}")
        print("-" * 50)

        parity0_nm_counts = []
        parity1_nm_counts = []
        parity0_distinct = []
        parity1_distinct = []
        total_pairs = 0
        ec_pairs = 0
        no_ec_words = 0
        total_words = 0

        for bins in combinations(range(n), 3):
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            fc_target = list(ms)
            words = gen_words(n, fc_target, max_results=300, timeout_s=8)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue

                total_words += 1
                bdata = analyze_binary_phases(wl, n, ms)

                word_has_ec = False
                for bd in bdata:
                    total_pairs += 1
                    if bd['ec']:
                        ec_pairs += 1
                        word_has_ec = True
                    if bd['parity'] == 0:
                        parity0_nm_counts.append(bd['nonmover_count'])
                        parity0_distinct.append(bd['nonmover_distinct_pairs'])
                    else:
                        parity1_nm_counts.append(bd['nonmover_count'])
                        parity1_distinct.append(bd['nonmover_distinct_pairs'])

                if not word_has_ec:
                    no_ec_words += 1

        print(f"  Words: {total_words}, words without binary EC: {no_ec_words}")
        print(f"  Binary (p,parity) pairs: {total_pairs}, with EC: {ec_pairs}")
        if parity0_nm_counts:
            print(f"  Parity-0 non-mover steps: min={min(parity0_nm_counts)}, max={max(parity0_nm_counts)}, mean={sum(parity0_nm_counts)/len(parity0_nm_counts):.1f}")
            print(f"  Parity-0 distinct pairs: min={min(parity0_distinct)}, max={max(parity0_distinct)}, mean={sum(parity0_distinct)/len(parity0_distinct):.1f}")
        if parity1_nm_counts:
            print(f"  Parity-1 non-mover steps: min={min(parity1_nm_counts)}, max={max(parity1_nm_counts)}, mean={sum(parity1_nm_counts)/len(parity1_nm_counts):.1f}")
            print(f"  Parity-1 distinct pairs: min={min(parity1_distinct)}, max={max(parity1_distinct)}, mean={sum(parity1_distinct)/len(parity1_distinct):.1f}")

    # Now: the REAL question.
    # ALL processors contribute to the proof: every OW-NU word has EC at SOME proc.
    # But it's not always binary, and not always B-T-B.
    # The anatomy showed 95% have binary EC, 5% only ternary.
    # Maybe: approach the proof as a COMBINATION across all procs.

    # Alternative: maybe we should look at this differently.
    # The pfc vector (pfc_0(t), ..., pfc_{n-1}(t)) for t=0,...,L-1 traces a path in Z^n.
    # The residue vector (pfc_0 mod m_0, ..., pfc_{n-1} mod m_n) lives in Z_{m_0} x ... x Z_{m_{n-1}}.
    # Total space = product(ms) = sub-threshold < 4*3^(n-2).
    # CL = sum(fc) = sum(ms) for mult=1.
    # CL = 3n-3 for 3 binary + (n-3) ternary.
    #
    # The FULL residue vector has CL = 3n-3 values in a space of size product(ms).
    # For n=5: CL=12, space=72. Much smaller. No global pigeonhole.
    #
    # But EC only needs matching at 3 consecutive positions, not all n.
    # The 3-window residue has space m_{p-1} * m_p * m_{p+1}.

    print(f"\n{'='*70}")
    print("APPROACH: Count non-mover steps per parity layer at each binary proc")
    print("If non-movers cover ALL 9 points in {0,1,2}x{0,1,2}: EC guaranteed")
    print("=" * 70)

    for n in [5]:
        threshold = 4 * (3 ** (n - 2))
        for bins in combinations(range(n), 3):
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            fc_target = list(ms)
            words = gen_words(n, fc_target, max_results=50, timeout_s=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            count = 0
            for w in list(unique.values()):
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue

                count += 1
                if count > 3:
                    break

                L = len(wl)
                print(f"\n  ms={ms}, word={wl}")
                for p in range(n):
                    if ms[p] != 2:
                        continue
                    lp = (p - 1) % n
                    rp = (p + 1) % n

                    pfc = {}
                    for q in [lp, p, rp]:
                        pfc[q] = [0] * (L + 1)
                        for t in range(L):
                            pfc[q][t + 1] = pfc[q][t] + (1 if wl[t] == q else 0)

                    for parity in [0, 1]:
                        m_step = [t for t in range(L) if wl[t] == p and pfc[p][t] % 2 == parity]
                        nm_steps = [t for t in range(L) if wl[t] != p and pfc[p][t] % 2 == parity]
                        m_pair = (pfc[lp][m_step[0]] % ms[lp], pfc[rp][m_step[0]] % ms[rp]) if m_step else None
                        nm_pairs = set((pfc[lp][t] % ms[lp], pfc[rp][t] % ms[rp]) for t in nm_steps)
                        ec = m_pair in nm_pairs if m_pair else False
                        print(f"    p={p} par={parity}: mover_pair={m_pair}, nm_count={len(nm_steps)}, nm_distinct={len(nm_pairs)}/{ms[lp]*ms[rp]}, ec={ec}")


if __name__ == '__main__':
    main()
