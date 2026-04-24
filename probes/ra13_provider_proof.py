#!/usr/bin/env python3
"""
RA13: Comprehensive provider anatomy for the TernaryPhase theorem.

For every ZW good cycle with cwStepCount > 0, no safe proc, sub-threshold product,
>=3 binary, n >= 5, all fc >= 2, some fc >= 3:

There exists proc t with a TernaryPhase where:
  - One neighbor fires 0 in the phase (silent side)
  - The other neighbor is binary (m=2) with even fire count >= 2 (active side)

This script exhaustively characterizes:
  Q1: Which proc t? Relation to the fc>=3 proc q.
  Q2: Which phase?
  Q3: Why silent neighbor fires 0.
  Q4: Why active neighbor is binary with even fires >= 2.
  Q5: The counting argument.
"""

import time
from itertools import permutations, product as iproduct
from collections import Counter, defaultdict


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
    """Return list of (J, K) = (left_fires, right_fires) for each phase of proc q."""
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


def get_all_ring_placements(sorted_ms, n):
    seen = set()
    results = []
    for perm in set(permutations(sorted_ms)):
        best = perm
        for i in range(n):
            rot = perm[i:] + perm[:i]
            if rot < best:
                best = rot
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best:
                best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def find_all_providers(word, n, ms, fc):
    """Find ALL procs with a qualifying phase (silent=0, active=binary with fires>=2)."""
    providers = []
    for p in range(n):
        if fc[p] < 2:
            continue
        left_p = (p - 1) % n
        right_p = (p + 1) % n
        phases = analyze_phases(word, n, p)
        for phase_idx, (J, K) in enumerate(phases):
            # Silent=left (J=0), active=right (binary, K>=2)
            if J == 0 and K >= 2 and ms[right_p] == 2:
                providers.append({
                    'proc': p,
                    'phase_idx': phase_idx,
                    'silent_proc': left_p,
                    'active_proc': right_p,
                    'silent_fires': J,
                    'active_fires': K,
                    'm_t': ms[p],
                    'm_silent': ms[left_p],
                    'm_active': ms[right_p],
                    'fc_t': fc[p],
                    'fc_silent': fc[left_p],
                    'fc_active': fc[right_p],
                })
            # Silent=right (K=0), active=left (binary, J>=2)
            if K == 0 and J >= 2 and ms[left_p] == 2:
                providers.append({
                    'proc': p,
                    'phase_idx': phase_idx,
                    'silent_proc': right_p,
                    'active_proc': left_p,
                    'silent_fires': K,
                    'active_fires': J,
                    'm_t': ms[p],
                    'm_silent': ms[right_p],
                    'm_active': ms[left_p],
                    'fc_t': fc[p],
                    'fc_silent': fc[right_p],
                    'fc_active': fc[left_p],
                })
    return providers


def main():
    print("RA13: Provider Proof Anatomy")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)
        print(f"  Threshold: {threshold}")
        print(f"  Sorted multisets: {len(sorted_multisets)}")

        total_words = 0
        words_with_provider = 0

        # Q1: relationship of t to fc>=3 proc
        t_is_q = 0  # t is the fc>=3 proc itself
        t_is_neighbor_of_q = 0  # t is neighbor of an fc>=3 proc
        t_other = 0

        # Q1b: what IS t?
        t_role = Counter()  # (m_t, fc_t, relation_to_q)

        # Q2: provider architecture
        arch_counter = Counter()  # (m_t, m_silent, m_active, fc_t, fc_silent, fc_active, active_fires)

        # Q3: why silent fires 0 — counting
        silent_zero_reason = Counter()  # classification

        # Q4: why active is binary with even fires
        active_fires_dist = Counter()  # active_fires values

        # Q5: counting argument
        # For the pigeonhole: t has fc(t) phases, silent has fc(silent) fires
        # => phases with 0 silent fires >= fc(t) - fc(silent)
        # Among those: active fires are distributed.
        pigeonhole_data = []

        # Track: is the provider always at a binary-ternary boundary?
        boundary_type = Counter()  # (m_left, m_t, m_right)

        # When multiple providers exist, what's the pattern?
        num_providers_dist = Counter()

        # Check: is t always binary?
        t_modulus = Counter()

        no_provider_examples = []

        for sorted_ms in sorted_multisets:
            if time.time() - t0 > 300 and n == 9:
                print(f"  TIME LIMIT at {time.time()-t0:.0f}s")
                break

            placements = get_all_ring_placements(sorted_ms, n)
            for ms in placements:
                max_len = min(sum(ms), 4 * n)
                min_len = 2 * n + 1

                for cycle_len in range(min_len, max_len + 1):
                    walks = _enumerate_walks_dfs(n, cycle_len, ms)
                    for w in walks:
                        fc = [0] * n
                        for p in w:
                            fc[p] += 1

                        total_words += 1
                        providers = find_all_providers(w, n, ms, fc)
                        num_providers_dist[len(providers)] += 1

                        if not providers:
                            if len(no_provider_examples) < 3:
                                no_provider_examples.append({
                                    'ms': list(ms), 'word': list(w), 'fc': list(fc)
                                })
                            continue

                        words_with_provider += 1

                        # Analyze FIRST provider (canonical choice)
                        prov = providers[0]
                        t = prov['proc']

                        # Q1: relation to fc>=3 procs
                        fc3_procs = [p for p in range(n) if fc[p] >= 3]
                        if t in fc3_procs:
                            t_is_q += 1
                            rel = "IS_Q"
                        elif any(abs((t - q) % n) <= 1 or abs((q - t) % n) <= 1
                                 for q in fc3_procs):
                            # Check actual adjacency
                            adj_qs = [q for q in fc3_procs
                                      if (t - q) % n == 1 or (q - t) % n == 1]
                            if adj_qs:
                                t_is_neighbor_of_q += 1
                                rel = "NEIGHBOR_Q"
                            else:
                                t_other += 1
                                rel = "OTHER"
                        else:
                            t_other += 1
                            rel = "OTHER"

                        t_role[(prov['m_t'], prov['fc_t'], rel)] += 1
                        t_modulus[prov['m_t']] += 1
                        boundary_type[(ms[(t-1)%n], ms[t], ms[(t+1)%n])] += 1

                        arch_counter[(
                            prov['m_t'], prov['m_silent'], prov['m_active'],
                            prov['fc_t'], prov['fc_silent'], prov['fc_active'],
                            prov['active_fires']
                        )] += 1

                        active_fires_dist[prov['active_fires']] += 1

                        # Q3: silent fires = 0 reason
                        # Pigeonhole: fc(t) phases, fc(silent) fires
                        # Phases with 0 silent fires >= fc(t) - fc(silent)
                        gap = prov['fc_t'] - prov['fc_silent']
                        if gap >= 1:
                            silent_zero_reason[f"pigeonhole: fc_t-fc_silent={gap}>=1"] += 1
                        else:
                            # Even when gap <= 0, can still have a 0-phase
                            # because fires can cluster
                            silent_zero_reason[f"clustering: fc_t={prov['fc_t']},fc_silent={prov['fc_silent']}"] += 1

                        pigeonhole_data.append((
                            prov['fc_t'], prov['fc_silent'], prov['fc_active'],
                            prov['active_fires'], gap
                        ))

        elapsed = time.time() - t0
        print(f"\n  Results ({elapsed:.1f}s):")
        print(f"  Total ZW words: {total_words}")
        print(f"  Words with provider: {words_with_provider}")
        rate = 100 * words_with_provider / total_words if total_words > 0 else 0
        print(f"  Provider rate: {rate:.1f}%")

        if no_provider_examples:
            print(f"\n  NO-PROVIDER EXAMPLES:")
            for ex in no_provider_examples:
                print(f"    ms={ex['ms']}, fc={ex['fc']}, word={ex['word']}")

        print(f"\n  Q1: Relationship of t to fc>=3 proc q:")
        print(f"    t IS q (fc>=3): {t_is_q}")
        print(f"    t is NEIGHBOR of q: {t_is_neighbor_of_q}")
        print(f"    t other: {t_other}")

        print(f"\n  Q1b: Provider proc modulus:")
        for m, cnt in t_modulus.most_common():
            print(f"    m_t={m}: {cnt} ({100*cnt/words_with_provider:.1f}%)")

        print(f"\n  Q1c: Provider role (m_t, fc_t, relation):")
        for role, cnt in t_role.most_common(15):
            print(f"    {role}: {cnt}")

        print(f"\n  Q2: Provider architecture (m_t, m_silent, m_active, fc_t, fc_silent, fc_active, active_fires):")
        for arch, cnt in arch_counter.most_common(15):
            print(f"    {arch}: {cnt}")

        print(f"\n  Q2b: Boundary type (m_left, m_t, m_right):")
        for bt, cnt in boundary_type.most_common(10):
            print(f"    {bt}: {cnt}")

        print(f"\n  Q3: Why silent fires = 0:")
        for reason, cnt in silent_zero_reason.most_common():
            print(f"    {reason}: {cnt}")

        print(f"\n  Q4: Active fires distribution:")
        for af, cnt in active_fires_dist.most_common():
            print(f"    active_fires={af}: {cnt}")

        print(f"\n  Q5: Pigeonhole data (fc_t, fc_silent, fc_active, active_fires, gap):")
        if pigeonhole_data:
            gaps = Counter(d[4] for d in pigeonhole_data)
            print(f"    Gap (fc_t - fc_silent) distribution:")
            for g, cnt in sorted(gaps.items()):
                print(f"      gap={g}: {cnt}")

            # Check: is gap always >= 1?
            neg_gap = [d for d in pigeonhole_data if d[4] < 1]
            print(f"    Gap < 1 cases: {len(neg_gap)}")
            if neg_gap:
                for d in neg_gap[:5]:
                    print(f"      fc_t={d[0]}, fc_silent={d[1]}, fc_active={d[2]}, "
                          f"active_fires={d[3]}, gap={d[4]}")

            # Check: active_fires always = fc_active?
            af_eq_fc = sum(1 for d in pigeonhole_data if d[3] == d[2])
            print(f"    active_fires == fc_active: {af_eq_fc}/{len(pigeonhole_data)}")

        print(f"\n  Number of providers per word:")
        for np_val, cnt in sorted(num_providers_dist.items()):
            print(f"    {np_val} providers: {cnt}")

    print("\n\n" + "=" * 70)
    print("ANALYSIS COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
