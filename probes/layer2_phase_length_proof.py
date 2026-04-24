#!/usr/bin/env python3
"""
LAYER 2 PROOF: Phase-length argument for normalForm EC.

THEOREM: For a sandwiched ternary t (both neighbors binary) with m(t)=3,
if ALL phases are normalForm, then entry conflict exists.

THE ARGUMENT:
  NormalForm => J+K <= 1 per phase (tight).
  But fc(bL) + fc(bR) >= fc(t) (sparse_phase_sum_ge).
  And fc(bL) + fc(bR) <= fc(t) (from the tight/chaining argument).
  So fc(bL) + fc(bR) = fc(t) and each phase has J+K = 1.

  Now: each phase (a, s) has exactly 1 binary neighbor firing at step a+1 (tight).
  Phase length = s - a (mod L). The phase "content" is:
    step a: previous t-fire (or wrap)
    step a+1: the single binary fire (L or R)
    steps a+2 .. s-1: other procs fire (not t, bL, bR, LL, RR if free)
    step s: this t-fire

  EC arises when a phase has length > 2, i.e., there's a step between
  the binary fire and the t-fire.

  At such a step a+2 (if it exists), the boundary triple at t is:
    (c[bL](a+2), c[t](a+2), c[bR](a+2))
  This is the same as the triple at step s (the t-fire), because
  between a+1 and s, neither bL nor bR fires. So the nonmover triple
  at step a+2 matches the mover triple at step s => EC at t.

  WAIT: the mover at step s fires t, changing c[t]. The triple
  (c[bL], t_value, c[bR]) at step a+2 has t_value = c[t](a+2) = phase value v.
  At step s: c[t](s) = v (same, because t doesn't fire between a and s).
  So the L,S,R triple at s is (c[bL](s), v, c[bR](s)).
  And at a+2: (c[bL](a+2), v, c[bR](a+2)).
  Since bL fires at a+1 but not after: c[bL](a+2) = c[bL](s).
  Since bR doesn't fire: c[bR](a+2) = c[bR](s).
  So the triples MATCH. Step s is a mover (fires t), step a+2 is a nonmover.
  => EC at t. DONE.

  So: if ANY phase has length > 2 => EC.

  CAN ALL PHASES HAVE LENGTH EXACTLY 2?
  Phase length 2 means s = a + 2. Sum of phase lengths = cycle length L.
  Number of phases = fc(t) / 1 = fc(t) (since m(t)=3, fc(t) = 3k).
  So L = 2 * fc(t) = 2 * 3k = 6k.
  But L = sum of all fire counts. With J+K=1 per phase:
    fc(bL) + fc(bR) = fc(t) = 3k.
  The only procs that fire in the phase are bL/bR (once each phase) and
  t (once each phase, at step s). So L = fc(t) + fc(bL) + fc(bR) + fc(others).
  L = 3k + 3k + fc(others) = 6k + fc(others).
  But L = 6k, so fc(others) = 0.
  With n >= 7 and >= 3 non-consecutive binary, there are other procs that
  MUST fire (hfull). Contradiction.

  Actually, does hfull always hold? Let me check.
  In the allNormalForm_false2 theorem: hfull is given as hypothesis.
  So yes, fc(others) > 0 implies L > 6k, and SOME phase has length > 2.

  FINAL PROOF:
  1. NormalForm at all phases => each phase has J+K <= 1 and is tight.
  2. sparse_phase_sum_ge + tight argument => J+K = 1 per phase.
  3. With hfull (all procs fire): L > 2*fc(t), so some phase has length > 2.
  4. Phase with length > 2 => nonmover step a+2 shares boundary triple
     with mover step s => EC at t.

COMPUTATIONAL VERIFICATION:
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
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
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


def is_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True


def get_phases_sandwiched(word, cycle, ms, n, t):
    """Get phase data for sandwiched ternary t."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    t_fires = [i for i in range(ell) if word[i] == t]
    if not t_fires:
        return []

    phases = []
    fc_t = len(t_fires)
    for idx in range(fc_t):
        s = t_fires[idx]
        a = t_fires[(idx - 1) % fc_t]

        # Phase interval (a, s]
        if s > a:
            interior = list(range(a + 1, s))
        else:
            interior = list(range(a + 1, ell)) + list(range(0, s))

        J = sum(1 for st in interior if word[st] == bL)
        K = sum(1 for st in interior if word[st] == bR)
        phase_len = len(interior) + 1  # +1 for step s

        phases.append({
            'a': a, 's': s, 'J': J, 'K': K,
            'len': phase_len, 'interior': interior
        })
    return phases


def check_phase_ec_argument(word, cycle, ms, n, t):
    """Verify the phase-length EC argument at sandwiched ternary t.

    Returns (has_ec, reason) where reason explains what happened.
    """
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n

    phases = get_phases_sandwiched(word, cycle, ms, n, t)
    if not phases:
        return False, "t doesn't fire"

    # Check all normalForm
    for ph in phases:
        if not is_normal_form(ph['J'], ph['K']):
            return None, "not all normalForm"

    # Check J+K per phase
    jk_sum = [ph['J'] + ph['K'] for ph in phases]

    # Find a phase with length > 2 (interior has > 0 steps besides the binary fire)
    for ph in phases:
        if ph['len'] > 2:
            # Phase has steps: a, a+1 (binary fire), a+2, ..., s
            # step a+2 exists and has same boundary triple as step s
            a = ph['a']
            s = ph['s']

            # Step a+1 is the first step in the phase
            a1 = (a + 1) % ell
            a2 = (a + 2) % ell if ph['len'] > 2 else None

            if a2 is not None:
                # Verify: boundary triple at t matches between a2 and s
                triple_a2 = (cycle[a2][bL], cycle[a2][t], cycle[a2][bR])
                triple_s = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if triple_a2 == triple_s:
                    # step s is t-mover, step a2 is not t-mover
                    assert word[s] == t
                    assert word[a2] != t  # interior step
                    return True, f"phase_len={ph['len']}, triple match at a2={a2} and s={s}"

    return False, f"all phases have length <= 2, phase_lens={[ph['len'] for ph in phases]}"


def check_actual_ec(word, cycle, ms, n, t):
    """Brute force EC check at t."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    for sv in range(ms[t]):
        mover = set()
        nonmover = set()
        for i in range(ell):
            if cycle[i][t] == sv:
                lr = (cycle[i][bL], cycle[i][bR])
                if word[i] == t:
                    mover.add(lr)
                else:
                    nonmover.add(lr)
        if mover & nonmover:
            return True
    return False


print("=" * 70)
print("PHASE-LENGTH EC PROOF VERIFICATION")
print("=" * 70)

test_cases = [
    (7, [2, 3, 2, 3, 2, 3, 3], "n=7 alt+extra", 24),
    (7, [3, 2, 3, 2, 3, 2, 3], "n=7 alternating", 24),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], "n=8 alternating", 24),
    (9, [2, 3, 2, 3, 2, 3, 3, 3, 3], "n=9 non-consec", 30),
]

for n, ms, label, max_len in test_cases:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        print(f"\n{label}: no sandwiched ternary, skipping")
        continue

    words = enumerate_mover_words(ms, n, max_len)

    total = 0
    all_normal_count = 0
    phase_ec_count = 0
    actual_ec_count = 0
    failures = []
    len_stats = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        for t in sandwiched:
            phases = get_phases_sandwiched(word, cycle, ms, n, t)
            if not phases:
                continue
            all_nf = all(is_normal_form(ph['J'], ph['K']) for ph in phases)
            if not all_nf:
                continue
            all_normal_count += 1

            result, reason = check_phase_ec_argument(word, cycle, ms, n, t)
            if result:
                phase_ec_count += 1
            elif result is False:
                # check actual EC
                if check_actual_ec(word, cycle, ms, n, t):
                    actual_ec_count += 1
                else:
                    failures.append((word, t, reason))

            for ph in phases:
                len_stats[ph['len']] += 1

    print(f"\n{label}")
    print(f"  Sandwiched: {sandwiched}")
    print(f"  Total valid cycles: {total}")
    print(f"  All-normalForm instances (cycle x sandwiched t): {all_normal_count}")
    print(f"  Phase-length EC proven: {phase_ec_count}")
    print(f"  Actual EC (brute force): {actual_ec_count}")
    print(f"  Failures (no EC): {len(failures)}")
    print(f"  Phase length distribution: {dict(sorted(len_stats.items()))}")
    if failures:
        print(f"  FAILURES:")
        for w, t, r in failures[:5]:
            print(f"    word={w}, t={t}: {r}")
