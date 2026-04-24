#!/usr/bin/env python3
"""
RA12 Part 3: WHY does EC always hold? Direct mechanism analysis.

Key finding: (0,0) phase NEVER exists. So both-silent is dead.
But 100% of cycles have EC. WHY?

Hypothesis: fc>=3 at a proc with m_q states means it returns to the same
state, creating a repeated context. Specifically:

For binary q (m_q=2, fc(q)>=3): q fires 3+ times through only 2 states.
  State seq must be 0->1->0->1->... ending at 0. So fires 2k times.
  Wait - fc(q)>=3 at binary means fc(q) is even (must return to 0).
  Actually: state_seq for binary with fc=3 would be [0, ?, ?, 0] with 3
  transitions: 0->a->b->0. With m=2: 0->1->0->1, but that's fc=3 ending at 1, not 0.
  Actually enumerate_state_sequences(2, 3) = [0, 1, 0, 1] -> ends at 1, not 0!
  So fc=3 is IMPOSSIBLE for binary procs! Binary can only fire even times.

For ternary q (m_q=3, fc(q)>=3): 3 fires through 3 states.
  State seq: [0, a, b, 0] with a!=0, b!=a, 0!=b. So a in {1,2}, b in {1,2}\{a}.
  Two options: [0,1,2,0] and [0,2,1,0].

So fc>=3 only happens at ternary (or higher) procs.

Now: a ternary proc q with fc=3 has 3 phases. Its neighbors fire in these phases.
For the phase pattern [(2,0), (0,2), (0,1)]:
  Phase 1: both neighbors fire (left fires 2, right fires 0)
  Phase 2: right fires 2, left silent
  Phase 3: right fires 1, left silent

The (0,2) phase = left-silent, K=2 phase. If left is binary, this means
left fires 2 (= all its fires) in this one phase of q. Since left is binary
with fc=2, and it fires both times in one phase of q, the two fires of left
happen between two consecutive fires of q.

This is EXACTLY what gives the one-sided EC (phase_dispatch_ec).

Let's verify: does EVERY fc>=3 ternary proc have a one-sided phase where
the active neighbor fires >= 2 AND that active neighbor is binary?
"""

from itertools import product as iproduct
from collections import Counter
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
    print("RA12 Part 3: EC Mechanism Analysis")
    print("=" * 70)

    # First: verify that fc>=3 is impossible at binary procs
    print("\n--- State sequence feasibility ---")
    for m in [2, 3, 4]:
        for k in range(1, 7):
            seqs = enumerate_state_sequences(m, k)
            if seqs:
                print(f"  m={m}, fc={k}: {len(seqs)} sequences")
            else:
                print(f"  m={m}, fc={k}: IMPOSSIBLE")

    print("\n--- Main analysis ---")

    for n in [5, 7]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        multisets = generate_subthreshold_multisets(n, threshold)

        total_cycles = 0
        total_fc3_instances = 0

        # Key questions:
        # Q1: Does every fc>=3 proc have a one-sided phase with active side >=2?
        q1_yes = 0
        q1_no = 0
        q1_no_examples = []

        # Q2: In that one-sided phase, is the active-side neighbor binary?
        q2_binary = 0
        q2_nonbinary = 0

        # Q3: Does every fc>=3 proc q have a phase where ONE neighbor fires ALL its fires?
        q3_yes = 0
        q3_no = 0

        # Q4: For the (J=0, K>=2) or (K=0, J>=2) phases, what is the max of K or J?
        max_active_fires = Counter()

        # Q5: Does every cycle have a proc with a one-sided >=2 phase where
        #     the active neighbor is binary?
        q5_yes = 0
        q5_no = 0
        q5_no_examples = []

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

                        cycle_has_binary_onesided = False

                        for q in fc3_procs:
                            total_fc3_instances += 1
                            phases = analyze_phases(w, n, q)
                            left_q = (q - 1) % n
                            right_q = (q + 1) % n

                            # Q1: one-sided >=2?
                            has_os2 = False
                            for J, K in phases:
                                if J == 0 and K >= 2:
                                    has_os2 = True
                                    max_active_fires[K] += 1
                                    if ms[right_q] == 2:
                                        q2_binary += 1
                                        cycle_has_binary_onesided = True
                                    else:
                                        q2_nonbinary += 1
                                if K == 0 and J >= 2:
                                    has_os2 = True
                                    max_active_fires[J] += 1
                                    if ms[left_q] == 2:
                                        q2_binary += 1
                                        cycle_has_binary_onesided = True
                                    else:
                                        q2_nonbinary += 1

                            if has_os2:
                                q1_yes += 1
                            else:
                                q1_no += 1
                                if len(q1_no_examples) < 5:
                                    q1_no_examples.append({
                                        'ms': list(ms), 'word': list(w), 'q': q,
                                        'fc': list(fc), 'phases': phases,
                                        'm_left': ms[left_q], 'm_right': ms[right_q]
                                    })

                            # Q3: some neighbor fires ALL its fires in one phase?
                            has_all = False
                            for J, K in phases:
                                if J == fc[left_q] or K == fc[right_q]:
                                    has_all = True
                            if has_all:
                                q3_yes += 1
                            else:
                                q3_no += 1

                        # Q5: cycle-level
                        if cycle_has_binary_onesided:
                            q5_yes += 1
                        else:
                            # Check ALL procs, not just fc>=3
                            found = False
                            for p in range(n):
                                if fc[p] < 2:
                                    continue
                                phases = analyze_phases(w, n, p)
                                left_p = (p - 1) % n
                                right_p = (p + 1) % n
                                for J, K in phases:
                                    if J == 0 and K >= 2 and ms[right_p] == 2:
                                        found = True
                                        break
                                    if K == 0 and J >= 2 and ms[left_p] == 2:
                                        found = True
                                        break
                                if found:
                                    break
                            if found:
                                q5_yes += 1
                            else:
                                q5_no += 1
                                if len(q5_no_examples) < 5:
                                    q5_no_examples.append({
                                        'ms': list(ms), 'word': list(w), 'fc': list(fc)
                                    })

        elapsed = time.time() - t0
        print(f"  Total cycles: {total_cycles}, elapsed: {elapsed:.1f}s")

        print(f"\n  Q1: fc>=3 proc has one-sided >=2 phase?")
        print(f"    YES: {q1_yes}/{total_fc3_instances}")
        print(f"    NO:  {q1_no}/{total_fc3_instances}")
        if q1_no_examples:
            for ex in q1_no_examples[:3]:
                print(f"      ms={ex['ms']}, q={ex['q']}(fc={ex['fc'][ex['q']]}), "
                      f"phases={ex['phases']}")
                print(f"        m_left={ex['m_left']}, m_right={ex['m_right']}")

        print(f"\n  Q2: In one-sided >=2 phases, active-side neighbor state count?")
        print(f"    Binary (m=2): {q2_binary}")
        print(f"    Non-binary:   {q2_nonbinary}")

        print(f"\n  Q3: fc>=3 proc has phase where some neighbor fires ALL?")
        print(f"    YES: {q3_yes}/{total_fc3_instances}")
        print(f"    NO:  {q3_no}/{total_fc3_instances}")

        print(f"\n  Q4: Active fires in one-sided >=2 phases:")
        for k, cnt in sorted(max_active_fires.items()):
            print(f"    K or J = {k}: {cnt}")

        print(f"\n  Q5: Cycle has SOME proc with binary-neighbor one-sided >=2?")
        print(f"    YES: {q5_yes}/{total_cycles}")
        print(f"    NO:  {q5_no}/{total_cycles}")
        if q5_no_examples:
            for ex in q5_no_examples[:3]:
                print(f"      ms={ex['ms']}, word={ex['word']}, fc={ex['fc']}")


if __name__ == "__main__":
    main()
