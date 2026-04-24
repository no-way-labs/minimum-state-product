#!/usr/bin/env python3
"""
RA12 Part 5: Final synthesis.

KEY FINDINGS so far:
1. Both-silent (0,0) phase: NEVER exists. J+K >= 1 always (adjacency).
   When interval = 1 step, J+K = 1 exactly.

2. At FC>=3 ternary proc: has one-sided >=2 only 44% of time.
   The binary-silent phases often have other-side = 1 (interval length 1).

3. BUT: at CYCLE level, 100% have SOME proc with binary-neighbor one-sided >=2.
   Providers are often fc=2 binary procs or different ternary procs.

Now: what's the CLEAN analytical path for EC?

Option A: phase_dispatch_ec at the provider proc
  - Find proc p with phase (J=0, K>=2) or (K=0, J>=2) where active neighbor is binary
  - This gives EC via one-sided dispatch
  - Problem: need to prove such proc ALWAYS exists (hard)

Option B: Direct EC from fc>=3 (no phase extraction needed)
  - fc>=3 at ternary: 3 fires, 2 state sequences [0,1,2,0] or [0,2,1,0]
  - 3 mover contexts (L, S, R) and 3 post-move (L, S', R)
  - Since walk is adjacent, between fires the walk traverses through neighbors
  - State of q changes: 0->1->2->0 or 0->2->1->0
  - Left context at each fire = state of q-1
  - Right context at each fire = state of q+1
  - If q-1 or q+1 is binary (m=2): their state is 0 or 1
  - The 3 fires of q see 3 contexts. At least 2 have same left_val (pigeonhole on binary)
  - Actually binary has 2 values, 3 fires => 2 fires have same L (if left is binary)
  - If same (L, S, R): mover repeat => MNU violation => but MNU might not hold
  - If same L but different S: different mover contexts, no direct EC
  - If same L and same S but different R: impossible since S determines S' and same L,S,R
    implies same mover context

Let me check: for fc>=3 ternary proc, does it always have a mover-context
collision? And does that collision match a non-mover context?

Option C: EC from the (0,1) normalForm phase
  - 100% of fc>=3 ternary procs have at least one (0,1) or (1,0) phase
  - palindromic_phase_ec handles this IF we can avoid callbacks
  - But the user says this needs callbacks for ZW => circular

Option D: Use a DIFFERENT lemma for ZW
  - Not phase-based at all
  - Direct context analysis using fc>=3 constraint

Let me computationally check Option B.
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
    print("RA12 Part 5: EC Mechanism — Binary-Boundary Phase Theorem")
    print("=" * 70)

    # THEOREM (to verify): In any ZW good cycle with >=3 binary, all fc>=2,
    # some fc>=3, sub-threshold product:
    # There exists a ternary proc q adjacent to a binary proc b such that
    # q has a phase where b fires 0 times and the other neighbor fires >= 2.

    # Actually from the data: 100% is "some proc (any fc) has binary-neighbor one-sided >=2"
    # But the PROVIDER might be fc=2, and the one-sided neighbor might be ternary.

    # Let me reframe: we need to find ANY proc p and ANY phase of p
    # where one neighbor fires 0 and the other fires >= 2,
    # AND the firing neighbor is binary.

    # The firing neighbor being binary AND firing >= 2 means it fires
    # ALL its fires (since binary fc = 2 exactly) in this one phase.
    # The binary proc has state seq [0, 1, 0], so it goes 0->1->0.
    # Both fires happen between two consecutive fires of p.
    # And on the OTHER side of p, the neighbor fires 0 times.
    # So both of p's neighbor states (on the silent side) are unchanged.

    # This means: p sees the SAME context on the silent side for both
    # fires of the binary neighbor? No — p is not the one firing.
    # The binary neighbor b fires twice in this phase. p doesn't fire.

    # Wait: the phase is defined relative to p (p is the one with the phases).
    # In a phase of p, p fires at the END. So between two p-fires,
    # b fires 2 times and the other neighbor fires 0 times.

    # For EC at p: p sees context (L, S, R) at its fire step s.
    # The non-mover context at step s includes all non-mover procs.
    # For EC we need a MOVER context at some step to match a NON-MOVER context
    # at some other step.

    # Actually, the one-sided K>=2 phase gives EC at p DIRECTLY:
    # Between two p-fires, b fires >= 2. b's two fires create mover contexts.
    # The non-mover context at b includes p's state.
    # Actually this is phase_dispatch_ec — the existing Lean mechanism.

    # Let me check a different angle: WHICH proc gets the EC?
    # At the cycle level, we just need EC at SOME proc.

    print("\n=== Check: Does EC always occur at SOME ternary-binary boundary? ===")

    for n in [5, 7]:
        print(f"\n  n = {n}")
        threshold = 4 * (3 ** (n - 2))
        multisets = generate_subthreshold_multisets(n, threshold)
        t0 = time.time()

        total_cycles = 0
        ec_at_boundary = 0  # EC at a ternary proc adjacent to binary
        ec_elsewhere = 0

        for ms in multisets:
            if time.time() - t0 > 60:
                print("  TIME LIMIT")
                break
            max_len = min(sum(ms), 4 * n)
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
                        L = len(w)

                        # Find boundary procs (ternary adjacent to binary)
                        boundary = set()
                        for p in range(n):
                            if ms[p] >= 3:
                                lp = (p - 1) % n
                                rp = (p + 1) % n
                                if ms[lp] == 2 or ms[rp] == 2:
                                    boundary.add(p)
                            if ms[p] == 2:
                                lp = (p - 1) % n
                                rp = (p + 1) % n
                                if ms[lp] >= 3 or ms[rp] >= 3:
                                    boundary.add(p)

                        # Check EC at boundary vs elsewhere
                        mover_entries = {}
                        nonmover_entries = {}
                        for t in range(L):
                            c = configs[t]
                            cn = configs[(t + 1) % L]
                            mover = w[t]
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

                        ec_procs = set()
                        for key in mover_entries:
                            if key in nonmover_entries:
                                mval = mover_entries[key]
                                _, _, s, _ = key
                                if mval != s:
                                    ec_procs.add(key[0])

                        if ec_procs & boundary:
                            ec_at_boundary += 1
                        else:
                            ec_elsewhere += 1

        print(f"    Total cycles: {total_cycles}")
        print(f"    EC at ternary-binary boundary: {ec_at_boundary}")
        print(f"    EC only elsewhere: {ec_elsewhere}")

    # MAIN THEOREM CHECK: for the proc with one-sided >=2 binary-neighbor phase,
    # does EC happen at THAT proc via that phase?
    print("\n\n=== MAIN: Does one-sided >=2 binary phase DIRECTLY cause EC? ===")

    n = 5
    threshold = 4 * (3 ** (n - 2))
    multisets = generate_subthreshold_multisets(n, threshold)

    total = 0
    direct_ec = 0
    indirect_ec = 0
    details = []

    for ms in multisets:
        max_len = min(sum(ms), 4 * n)
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

                    total += 1
                    L = len(w)

                    # Find the proc with one-sided >=2 binary-neighbor phase
                    for p in range(n):
                        if fc[p] < 2:
                            continue
                        left_p = (p - 1) % n
                        right_p = (p + 1) % n
                        phases = analyze_phases(w, n, p)
                        found_phase = False
                        for J, K in phases:
                            if J == 0 and K >= 2 and ms[right_p] == 2:
                                found_phase = True
                                break
                            if K == 0 and J >= 2 and ms[left_p] == 2:
                                found_phase = True
                                break
                        if not found_phase:
                            continue

                        # Check EC at this proc p
                        mover_ctx = {}
                        nonmover_ctx = {}
                        for t in range(L):
                            c = configs[t]
                            cn = configs[(t + 1) % L]
                            Lp = (p - 1) % n
                            Rp = (p + 1) % n
                            key = (c[Lp], c[p], c[Rp])
                            if w[t] == p:
                                mover_ctx[key] = cn[p]
                            else:
                                if key not in nonmover_ctx:
                                    nonmover_ctx[key] = set()
                                nonmover_ctx[key].add(c[p])

                        has_ec = False
                        for key in mover_ctx:
                            if key in nonmover_ctx:
                                mval = mover_ctx[key]
                                _, s, _ = key
                                if mval != s:
                                    has_ec = True
                                    break

                        if has_ec:
                            direct_ec += 1
                        else:
                            indirect_ec += 1
                            if len(details) < 5:
                                details.append({
                                    'ms': list(ms), 'word': list(w),
                                    'p': p, 'fc': list(fc), 'phases': phases,
                                    'mover': dict(mover_ctx),
                                    'nonmover': {k: v for k, v in nonmover_ctx.items()}
                                })
                        break  # only check first provider

    print(f"  n={n}: {total} cycles")
    print(f"  EC at provider proc: {direct_ec}")
    print(f"  No EC at provider:   {indirect_ec}")
    if details:
        print(f"\n  Examples without EC at provider:")
        for d in details[:3]:
            print(f"    ms={d['ms']}, p={d['p']}, fc={d['fc']}, phases={d['phases']}")
            print(f"    mover_ctx: {d['mover']}")
            print(f"    nonmover_ctx: {d['nonmover']}")


if __name__ == "__main__":
    main()
