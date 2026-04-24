#!/usr/bin/env python3
"""
RA12 Part 2: Deep analysis of phase patterns.

Key finding from Part 1:
- (0,0) phase NEVER exists at ANY proc in ZW cycles with fc>=3. Rate = 0%.
- BUT: 100% of such cycles have entry conflicts.

So the question shifts to: what phase patterns DO exist, and can we
prove EC through one-sided phases (J=0, K>=1) or (J>=1, K=0)?

Focus:
1. Every fc>=3 proc has a left-silent (J=0) and a right-silent (K=0) phase
2. What are K values in left-silent phases? Always K>=2?
3. Are the silent-side neighbors always binary?
4. Can we use the one-sided phase dispatch even without both-silent?
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import time


def enumerate_state_sequences(m, k):
    if k == 0:
        return [[0]]
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


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1:
            cw += 1
        elif diff == n - 1:
            ccw += 1
    return cw, ccw


def analyze_phases(word, n, q):
    L = len(word)
    left_q = (q - 1) % n
    right_q = (q + 1) % n
    fire_steps = [t for t in range(L) if word[t] == q]
    fc_q = len(fire_steps)
    if fc_q == 0:
        return []
    phases = []
    for idx in range(fc_q):
        s = fire_steps[idx]
        a = fire_steps[(idx - 1) % fc_q]
        J = K = 0
        t = (a + 1) % L
        while t != s:
            if word[t] == left_q:
                J += 1
            if word[t] == right_q:
                K += 1
            t = (t + 1) % L
        phases.append((J, K))
    return phases


def build_configs(word, n, combo, fc):
    L = len(word)
    fire_count = [0] * n
    configs = [tuple(combo[p][0] for p in range(n))]
    for t in range(L):
        mover = word[t]
        fire_count[mover] += 1
        new_config = list(configs[-1])
        new_config[mover] = combo[mover][fire_count[mover]]
        configs.append(tuple(new_config))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]


def _enumerate_walks_dfs(n, length, ms):
    results = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == length:
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1:
                return
            if any(f < 2 for f in fc):
                return
            if all(f <= 2 for f in fc):
                return
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw:
                return
            results.append(tuple(path))
            return
        remaining = length - step
        unfired = sum(1 for f in fc if f < 2)
        if unfired > remaining:
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2:
                continue
            if fc[nxt] >= 2 * ms[nxt]:
                continue
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
    for w in results:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def generate_subthreshold_multisets(n, threshold):
    results = []
    max_state = min(threshold // (2 ** (n - 1)) + 1, 10)
    def gen(pos, min_val, current, prod):
        if pos == n:
            if prod < threshold:
                num_bin = sum(1 for m in current if m == 2)
                if num_bin >= 3:
                    results.append(tuple(current))
            return
        remaining = n - pos
        for m in range(max(2, min_val), max_state + 1):
            new_prod = prod * m
            if new_prod >= threshold:
                break
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2:
                    break
            gen(pos + 1, m, current + [m], new_prod)
    gen(0, 2, [], 1)
    return results


def main():
    print("RA12 Part 2: Deep Phase Pattern Analysis")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        multisets = generate_subthreshold_multisets(n, threshold)

        # Track detailed phase stats
        total_cycles = 0
        total_fc3_instances = 0

        # For fc>=3 procs:
        has_left_silent = 0  # some phase with J=0
        has_right_silent = 0  # some phase with K=0
        has_left_silent_k_ge2 = 0  # J=0, K>=2
        has_right_silent_j_ge2 = 0  # K=0, J>=2
        has_one_sided_ge2 = 0  # (J=0,K>=2) or (J>=2,K=0)
        has_even_even = 0  # some phase with J%2==0, K%2==0
        has_even_even_nonzero = 0  # J%2==0, K%2==0, not both 0

        # For ALL procs (fc>=2):
        any_proc_left_silent_k_ge2 = 0
        any_proc_one_sided_ge2 = 0

        # One-sided neighbor analysis
        onesided_binary_neighbor = 0
        onesided_ternary_neighbor = 0

        # Phase type distribution
        phase_type_counter = Counter()

        for ms in multisets:
            if time.time() - t0 > 120:
                print("  TIME LIMIT")
                break

            max_len = sum(ms)
            if max_len > 4 * n:
                max_len = 4 * n
            min_len = 2 * n + 1

            for cycle_len in range(min_len, max_len + 1):
                walks = _enumerate_walks_dfs(n, cycle_len, ms)
                for w in walks:
                    fc = [0] * n
                    for p in w:
                        fc[p] += 1

                    proc_seqs = {}
                    feasible = True
                    for p in range(n):
                        seqs = enumerate_state_sequences(ms[p], fc[p])
                        if not seqs:
                            feasible = False
                            break
                        proc_seqs[p] = seqs
                    if not feasible:
                        continue

                    for combo_tuple in iproduct(*[proc_seqs[p] for p in range(n)]):
                        combo = {p: combo_tuple[p] for p in range(n)}
                        configs = build_configs(w, n, combo, fc)
                        if configs is None:
                            continue

                        total_cycles += 1
                        fc3_procs = [q for q in range(n) if fc[q] >= 3]

                        for q in fc3_procs:
                            total_fc3_instances += 1
                            phases = analyze_phases(w, n, q)
                            left_q = (q - 1) % n
                            right_q = (q + 1) % n

                            ls = any(J == 0 for J, K in phases)
                            rs = any(K == 0 for J, K in phases)
                            ls_k2 = any(J == 0 and K >= 2 for J, K in phases)
                            rs_j2 = any(K == 0 and J >= 2 for J, K in phases)
                            os2 = ls_k2 or rs_j2
                            ee = any(J % 2 == 0 and K % 2 == 0 for J, K in phases)
                            ee_nz = any(J % 2 == 0 and K % 2 == 0
                                       and (J > 0 or K > 0) for J, K in phases)

                            if ls: has_left_silent += 1
                            if rs: has_right_silent += 1
                            if ls_k2: has_left_silent_k_ge2 += 1
                            if rs_j2: has_right_silent_j_ge2 += 1
                            if os2: has_one_sided_ge2 += 1
                            if ee: has_even_even += 1
                            if ee_nz: has_even_even_nonzero += 1

                            for J, K in phases:
                                if J == 0 and K == 0:
                                    phase_type_counter['both_silent'] += 1
                                elif J == 0 and K == 1:
                                    phase_type_counter['left_silent_K1'] += 1
                                elif J == 0 and K >= 2:
                                    phase_type_counter['left_silent_Kge2'] += 1
                                    if ms[right_q] == 2:
                                        onesided_binary_neighbor += 1
                                    else:
                                        onesided_ternary_neighbor += 1
                                elif J == 1 and K == 0:
                                    phase_type_counter['right_silent_J1'] += 1
                                elif J >= 2 and K == 0:
                                    phase_type_counter['right_silent_Jge2'] += 1
                                    if ms[left_q] == 2:
                                        onesided_binary_neighbor += 1
                                    else:
                                        onesided_ternary_neighbor += 1
                                else:
                                    phase_type_counter[f'both_active_J{J}_K{K}'] += 1

                        # Any-proc one-sided check
                        cycle_has_os2 = False
                        for p in range(n):
                            if fc[p] < 2:
                                continue
                            phases = analyze_phases(w, n, p)
                            if any((J == 0 and K >= 2) or (K == 0 and J >= 2)
                                   for J, K in phases):
                                cycle_has_os2 = True
                                break
                        if cycle_has_os2:
                            any_proc_one_sided_ge2 += 1

        elapsed = time.time() - t0
        print(f"  Total cycles: {total_cycles}, elapsed: {elapsed:.1f}s")
        print(f"  FC>=3 proc instances: {total_fc3_instances}")
        print(f"\n  --- FC>=3 proc phase properties ---")
        print(f"  Has J=0 phase:        {has_left_silent}/{total_fc3_instances} "
              f"({100*has_left_silent/max(1,total_fc3_instances):.1f}%)")
        print(f"  Has K=0 phase:        {has_right_silent}/{total_fc3_instances} "
              f"({100*has_right_silent/max(1,total_fc3_instances):.1f}%)")
        print(f"  Has J=0,K>=2 phase:   {has_left_silent_k_ge2}/{total_fc3_instances} "
              f"({100*has_left_silent_k_ge2/max(1,total_fc3_instances):.1f}%)")
        print(f"  Has K=0,J>=2 phase:   {has_right_silent_j_ge2}/{total_fc3_instances} "
              f"({100*has_right_silent_j_ge2/max(1,total_fc3_instances):.1f}%)")
        print(f"  Has one-sided >=2:    {has_one_sided_ge2}/{total_fc3_instances} "
              f"({100*has_one_sided_ge2/max(1,total_fc3_instances):.1f}%)")
        print(f"  Has even-even (any):  {has_even_even}/{total_fc3_instances}")
        print(f"  Has even-even (>0):   {has_even_even_nonzero}/{total_fc3_instances}")

        print(f"\n  --- Phase type distribution ---")
        for ptype, cnt in phase_type_counter.most_common():
            print(f"    {ptype}: {cnt}")

        print(f"\n  --- One-sided K>=2 or J>=2: neighbor state counts ---")
        print(f"    Binary neighbor:  {onesided_binary_neighbor}")
        print(f"    Ternary neighbor: {onesided_ternary_neighbor}")

        print(f"\n  --- Any-proc one-sided >=2 ---")
        print(f"    Cycles with SOME proc one-sided >=2: "
              f"{any_proc_one_sided_ge2}/{total_cycles}")


if __name__ == "__main__":
    main()
