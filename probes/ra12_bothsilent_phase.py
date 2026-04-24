#!/usr/bin/env python3
"""
RA12: Both-Silent Phase Analysis for fc>=3 procs in ZW good cycles.

Question: In a zero-winding good cycle with cwStepCount > 0, sub-threshold,
>=3 binary, all fc>=2, some proc q with fc(q)>=3:

Does q always have at least one phase where BOTH neighbors fire 0 times?

A "phase" at q is [a, s) where q fires at step s, previous fire at step a.
J = fires of left(q) in (a, s), K = fires of right(q) in (a, s).
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import time


def enumerate_state_sequences(m, k):
    """State sequences: start 0, each step changes value, end at 0 after k fires."""
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
    """CW and CCW step counts."""
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
    """Analyze phases at proc q. Returns list of (J, K) for each phase."""
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
    """Build configs from word + state seq combo. Return list or None."""
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


def has_entry_conflict(word, n, configs):
    """Check if the cycle has an entry conflict at any proc."""
    L = len(word)
    mover_entries = {}
    nonmover_entries = {}
    for t in range(L):
        c = configs[t]
        cn = configs[(t + 1) % L]
        mover = word[t]
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            key = (j, c[Lp], c[j], c[Rp])
            if j == mover:
                mover_entries[key] = cn[j]
            else:
                if key not in nonmover_entries:
                    nonmover_entries[key] = set()
                nonmover_entries[key].add(c[j])
    for key in mover_entries:
        if key in nonmover_entries:
            mval = mover_entries[key]
            _, _, s, _ = key
            if mval != s:
                return True
    return False


def enumerate_zw_walks_with_fc3(n, ms):
    """Enumerate ZW mover words where all fc>=2 and some fc>=3.

    Use DFS with pruning: track fire counts, cut when impossible to
    reach all-fc>=2 constraint.
    """
    threshold = 4 * (3 ** (n - 2))
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        return []

    # Max cycle length: sum of fire counts. Each proc fires at most m_p times
    # (since state seq must return to 0 and use distinct transitions).
    # Actually fc can be up to m_p * (m_p - 1) or so, but practically small.
    # For binary: fc in {2}, ternary: fc in {2,3,4,...}
    # We need total fires = sum(fc) where fc[p] >= 2, some fc[p] >= 3.
    # Min total: 2n + 1 (all fc=2 except one fc=3)
    # Max total: bounded by state constraints

    min_len = 2 * n + 1
    max_len = sum(ms)  # rough: each proc fires at most m_p times
    # But actually can fire more (e.g., binary fires 2 = m_p times, ternary fires up to 6)
    # Be generous but not too much
    max_len = max(3 * n, min_len + n)

    results = []

    for target_len in range(min_len, max_len + 1):
        # DFS to build words of this length
        found = _enumerate_walks_dfs(n, target_len, ms)
        results.extend(found)

    return results


def _enumerate_walks_dfs(n, length, ms):
    """DFS enumeration of cyclic walks of given length on ring of size n."""
    results = []
    # For efficiency, we track fc and prune
    # adjacency: next mover must be +/-1 from current

    def dfs(path, fc):
        pos = path[-1]
        step = len(path)

        if step == length:
            # Check closure (last->first adjacent)
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1:
                return
            # All fc >= 2?
            if any(f < 2 for f in fc):
                return
            # Some fc >= 3?
            if all(f <= 2 for f in fc):
                return
            # ZW: cw == ccw > 0
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw:
                return
            results.append(tuple(path))
            return

        remaining = length - step
        # Pruning: can we still reach fc>=2 for all procs?
        unfired = sum(1 for f in fc if f < 2)
        # Each remaining step fires one proc, and must be adjacent
        # Very rough: if unfired * 2 > remaining, impossible
        # (each unfired proc needs at least 2 more fires but we need adjacency)
        if unfired > remaining:
            return

        for d in [1, -1]:
            nxt = (pos + d) % n
            # Prune: don't exceed max fires for this proc
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2:
                # Binary proc already fired 2 times
                continue
            if fc[nxt] >= 2 * ms[nxt]:
                # Too many fires even for ternary
                continue

            fc[nxt] += 1
            path.append(nxt)
            dfs(path, fc)
            path.pop()
            fc[nxt] -= 1

    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)

    # Canonicalize
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
    """Generate sorted multisets of length n, product < threshold, >=3 binary."""
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
            # Even with all remaining = 2 (minimum), check bound
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2:
                    break
            gen(pos + 1, m, current + [m], new_prod)

    gen(0, 2, [], 1)
    return results


def run_analysis(n, time_limit=120):
    """Run full analysis for given n."""
    print(f"\n{'='*70}")
    print(f"  n = {n}")
    print(f"{'='*70}")
    t0 = time.time()

    threshold = 4 * (3 ** (n - 2))
    multisets = generate_subthreshold_multisets(n, threshold)
    print(f"  Threshold: {threshold}")
    print(f"  Sub-threshold multisets with >=3 binary: {len(multisets)}")

    # Stats
    total_cycles = 0
    total_fc3_proc_instances = 0
    fc3_has_00 = 0
    fc3_no_00 = 0
    any_proc_00_count = 0
    all_procs_no_00_count = 0

    phase_pattern_counter = Counter()
    no_00_examples = []
    all_no_00_examples = []

    ec_at_cycle = 0
    no_ec_cycles = 0

    for ms in multisets:
        if time.time() - t0 > time_limit:
            print(f"  TIME LIMIT ({time_limit}s) reached, stopping.")
            break

        walks = enumerate_zw_walks_with_fc3(n, ms)
        if not walks:
            continue

        for w in walks:
            fc = [0] * n
            for p in w:
                fc[p] += 1
            L = len(w)

            # Check state sequence feasibility
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

                # Part 1: Check fc>=3 procs for (0,0) phase
                cycle_fc3_has_00 = False
                for q in fc3_procs:
                    total_fc3_proc_instances += 1
                    phases = analyze_phases(w, n, q)
                    has_00 = any(J == 0 and K == 0 for J, K in phases)
                    if has_00:
                        fc3_has_00 += 1
                        cycle_fc3_has_00 = True
                    else:
                        fc3_no_00 += 1
                        phase_pattern_counter[tuple(sorted(phases))] += 1
                        if len(no_00_examples) < 10:
                            no_00_examples.append({
                                'ms': list(ms), 'word': list(w), 'q': q,
                                'fc': list(fc), 'phases': phases
                            })

                # Part 4: Any proc with (0,0) phase
                any_00 = False
                for p in range(n):
                    if fc[p] < 2:
                        continue
                    phases = analyze_phases(w, n, p)
                    if any(J == 0 and K == 0 for J, K in phases):
                        any_00 = True
                        break
                if any_00:
                    any_proc_00_count += 1
                else:
                    all_procs_no_00_count += 1
                    if len(all_no_00_examples) < 10:
                        all_phases = {}
                        for p in range(n):
                            if fc[p] >= 2:
                                all_phases[p] = analyze_phases(w, n, p)
                        all_no_00_examples.append({
                            'ms': list(ms), 'word': list(w), 'fc': list(fc),
                            'phases': all_phases
                        })

                # Part 5: Entry conflict check
                if has_entry_conflict(w, n, configs):
                    ec_at_cycle += 1
                else:
                    no_ec_cycles += 1

    elapsed = time.time() - t0
    print(f"\n  Results (elapsed: {elapsed:.1f}s):")
    print(f"  Total ZW cycles with fc>=3: {total_cycles}")
    print(f"  EC at some proc: {ec_at_cycle}")
    print(f"  No EC: {no_ec_cycles}")
    print(f"\n  --- FC>=3 proc instances ---")
    print(f"  Has (0,0) phase: {fc3_has_00}")
    print(f"  No (0,0) phase:  {fc3_no_00}")
    if total_fc3_proc_instances > 0:
        pct = 100 * fc3_has_00 / total_fc3_proc_instances
        print(f"  Rate: {pct:.1f}%")

    print(f"\n  --- Any-proc (0,0) phase ---")
    print(f"  Cycles with SOME proc having (0,0): {any_proc_00_count}/{total_cycles}")
    print(f"  Cycles with NO proc having (0,0):   {all_procs_no_00_count}/{total_cycles}")

    if no_00_examples:
        print(f"\n  Examples of fc>=3 proc WITHOUT (0,0) phase:")
        for ex in no_00_examples[:5]:
            q = ex['q']
            left_q = (q - 1) % n
            right_q = (q + 1) % n
            print(f"    ms={ex['ms']}, q={q}(fc={ex['fc'][q]}), "
                  f"L={left_q}(fc={ex['fc'][left_q]}), R={right_q}(fc={ex['fc'][right_q]})")
            print(f"      word={ex['word']}")
            print(f"      phases(J,K) = {ex['phases']}")

    if all_no_00_examples:
        print(f"\n  Cycles with NO proc having (0,0) phase:")
        for ex in all_no_00_examples[:3]:
            print(f"    ms={ex['ms']}, word={ex['word']}")
            print(f"    fc={ex['fc']}")
            for p, ph in sorted(ex['phases'].items()):
                print(f"      proc {p} (fc={ex['fc'][p]}): phases={ph}")

    if phase_pattern_counter:
        print(f"\n  Phase pattern distribution (fc>=3 procs without (0,0)):")
        for pat, cnt in phase_pattern_counter.most_common(10):
            print(f"    {pat}: {cnt}")

    return {
        'total': total_cycles, 'fc3_has_00': fc3_has_00, 'fc3_no_00': fc3_no_00,
        'any_00': any_proc_00_count, 'all_no_00': all_procs_no_00_count,
        'ec': ec_at_cycle, 'no_ec': no_ec_cycles
    }


def main():
    print("RA12: Both-Silent Phase Analysis")
    print("=" * 70)

    # Part 2: Pigeonhole (analytical)
    print("\n=== PART 2: Pigeonhole Bound ===")
    print("For q with fc(q)>=3:")
    print("  #phases with J=0 >= fc(q) - fc(left)")
    print("  #phases with K=0 >= fc(q) - fc(right)")
    print("  #both-silent >= fc(q) - fc(left) - fc(right)")
    print("  With fc=3, fc_L=2, fc_R=2: bound = -1. FAILS.")
    print("  Need fc(q) > fc(L) + fc(R). Requires fc(q)>=5 with binary neighbors.")

    # Part 1: Exhaustive
    print("\n=== PARTS 1,3,4,5: Exhaustive Analysis ===")
    for n_val in [5, 7]:
        run_analysis(n_val, time_limit=120)

    print("\n\nDONE.")


if __name__ == "__main__":
    main()
