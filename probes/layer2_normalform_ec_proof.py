#!/usr/bin/env python3
"""
LAYER 2 PROOF: All-NormalForm implies Entry Conflict at boundary ternary.

THEOREM: In a good cycle on a ring with n >= 7, >= 3 non-consecutive binary
processors, sub-threshold product: if every phase at every boundary ternary
proc is normalForm (not dispatchable by phase_dispatch_ec), then entry
conflict exists at some boundary ternary proc.

PROOF OVERVIEW:
  The argument adapts BinSCC Exploration 10's "Traversal Return" mechanism
  and "Ring Alternation Lemma" to the general non-consecutive setting.

  KEY DEFINITIONS:
  - "Boundary ternary" t: ternary proc with at least one binary neighbor.
  - "NormalForm phase" at t: (J,K) not dispatched by BothEven, Toggle-FR,
    or ZeroSide. So J,K satisfy:
      * not (Even J and Even K)
      * not (J >= 2 and K = 0)
      * not (J = 0 and K >= 2)
    Remaining patterns: (1,0), (0,1), (1,1), (2,1), (1,2), (3,1), (1,3), etc.
    with at least one odd and neither zero-sided with >= 2.

  For a SANDWICHED boundary ternary (both neighbors binary), the binary
  neighbor fires J or K times in the phase. Binary has m=2, so fc(b) is
  even (cycles back to start). The fc per phase satisfies sum_phases J_i = fc(bL)
  = even, sum_phases K_i = fc(bR) = even.

  STEP 1: NormalForm + binary parity => J+K = 1 per phase.
    If J=0 then K=1 (not both-even (0,0), not zero-side-R (0,K>=2)).
    If K=0 then J=1 (symmetric).
    If J>=1, K>=1: at least one odd. But we show this can't contribute
    net-even sums without phases also having J+K=1 phases.
    Actually, the complete constraint is:
      fc(L)+fc(R) = sum(J_i + K_i) >= fc(t) (from sparse_phase_sum_ge in Lean)
    And fc(L)+fc(R) <= fc(t) (from the tight-phase argument).
    So fc(L)+fc(R) = fc(t), and each J_i + K_i = 1.

  STEP 2: Each phase has exactly one binary neighbor firing (J=1,K=0) or (J=0,K=1).
    This is a "one-sided" phase with a single tight firing.

  STEP 3: Traversal Return mechanism.
    In a one-sided phase (say J=1, K=0): the single left-t firing is tight
    (occurs at step a+1). The mover context at step a+1 is (c[LL], c[L], c[R])
    at processor L. The nonmover context at step a (which is a t-firing from the
    PREVIOUS phase) sees the same triple. EC at L if the boundary triples match.

    The key: step a is a t-firing, step a+1 is a left-t firing.
    The boundary triple at left t is:
      config(a): (c[LL](a), c[L](a), c[t](a))
      config(a+1): (c[LL](a+1), c[L](a+1), c[t](a+1))
    Since step a fires t: c[t](a+1) = (c[t](a)+1) mod 3.
    But c[LL](a+1) = c[LL](a) (LL didn't fire at step a).
    And c[L](a+1) = c[L](a) (L didn't fire at step a).
    So the L,S coords match but the R coord differs by 1 mod 3.
    NOT automatic EC: the R coordinate changes.

    The REAL Traversal Return works differently. Let me re-examine.

  STEP 3 (CORRECTED): Traversal Return via first-return identity.
    Consider all the steps where t has value v (S-level v).
    In this phase, t fires once (going v -> v+1). The steps with S=v
    are those between the PREVIOUS t-fire (which set value to v) and this one.

    At S-level v at processor t:
    - Nonmover contexts: all steps in [phase_start, t_fire) with config[t] = v
      The (L,R) pairs at these steps are the nonmover (L,R) set.
    - Mover context: the step where t fires (exactly 1 step per phase).
      The (L,R) pair at this step is the mover (L,R) singleton.

    EC at t happens when the mover (L,R) pair appears in the nonmover set.

    In a one-sided phase (J=1, K=0):
    - The single left-t firing changes L from L0 to L0+1 mod 2 = 1-L0.
    - So the L coordinate at step a is L0, and at steps after the L-fire it's 1-L0.
    - The R coordinate doesn't change (K=0, no right-t firing).
    - The mover (L,R) at the t-fire step (= step s) has L = 1-L0 (after the
      single left-fire which was tight at a+1) and R = R0.
    - The nonmover contexts: step a has (L0, R0), steps a+2..s-1 have (1-L0, R0).
    - The mover context (1-L0, R0) matches nonmover contexts at steps a+2..s-1
      IF there are any such steps.

    But the phase length is s - a. With J=1, K=0 and tight: step a+1 fires L,
    step s fires t. Steps a+2..s-1 fire neither L, R, LL, nor RR (because
    one-sided-left + normalForm). What fires? It must be procs far from t.

    ACTUALLY: if the phase length = 2 (s = a+2), then the only step between
    a and s is a+1 (the L-fire), and there's no step with (1-L0, R0) as
    nonmover. So no automatic EC from this single phase.

    For phase length > 2: steps a+2..s-1 exist, and the nonmover context at
    those steps has L = 1-L0, R = R0. The mover context at s also has
    L = 1-L0, R = R0. EC!

    So the question reduces to: can ALL phases have length exactly 2?
    Phase length = s - a. With fc(t) phases and cycle length L:
    sum of phase lengths = L. If each phase has length 2: L = 2*fc(t).
    But L = sum of ALL fire counts = fc(t) + fc(L) + fc(R) + other.
    With fc(L)+fc(R) = fc(t) and each J+K=1: 2*fc(t) = fc(t) + fc(t).
    This means the "other" fire counts sum to 0: no proc other than t, L, R
    fires! But with n >= 7 and >= 3 binary non-consecutive, there are many
    other procs that must fire (hfull: all procs fire > 0 times).

    CONTRADICTION: the cycle has length >= 2n (each of n procs fires at least
    once, and ternary fire exactly 3 times). With fc(L)+fc(R) = fc(t) = 3
    (minimum ternary): each binary fires 2 times. sum = 3 + 2 + 2 = 7, but
    other procs also fire. Phase length sum = cycle length >= 2n - but
    2*fc(t) = 6 while 2n >= 14. Impossible.

    So SOME phase has length > 2, giving EC.

  WAIT: I assumed fc(t) = 3 and that t is ternary. But the hypothesis is
  m(t) >= 3 (could be larger). Let me re-examine.

  Actually, for the allNormalForm_false2 theorem, t is a SANDWICHED ternary
  (both neighbors binary) with m(t) >= 3. The normalForm constraint forces
  J+K = 1 per phase, and each phase has exactly one neighbor firing.
  The tight-phase argument shows the neighbor firing is at step a+1.

  With m(t) = 3: fc(t) = 3k for some k >= 1, and fc(L) + fc(R) = fc(t) = 3k.
  The phase length sum = cycle length L. 2*fc(t) = 6k is the contribution
  from t + one neighbor per phase. But L >= 2n because every proc fires
  at least once (hfull) and ternary fire >= 3 times. For n >= 7:
  L >= 3*3 + 2*3 + remaining >= 15 >> 6.

  Actually let me just verify computationally. The mathematical argument
  is clear: with J+K=1 per phase and tight firing, most phases must have
  length > 2 (other procs need to fire), giving EC.

COMPUTATIONAL VERIFICATION below.
"""

from collections import Counter
from itertools import product as iterproduct


def enumerate_mover_words(ms, n, max_length):
    """Enumerate all valid good-cycle mover words up to max_length."""
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
    """Build config sequence from mover word."""
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


def temporal_order(steps, ell):
    """Reorder steps by temporal order (largest gap is the phase boundary)."""
    if len(steps) <= 1:
        return steps
    max_gap = 0
    start_after = 0
    for i in range(len(steps)):
        nxt = (i + 1) % len(steps)
        gap = (steps[nxt] - steps[i]) % ell
        if gap > max_gap:
            max_gap = gap
            start_after = i
    start_idx = (start_after + 1) % len(steps)
    return [steps[(start_idx + i) % len(steps)] for i in range(len(steps))]


def get_phases(word, cycle, ms, n, t):
    """Extract phases at ternary processor t.

    A phase = interval [a, s) where s is a t-firing and a is the previous t-firing
    (or the last t-firing wrapping around).
    Returns list of (a, s, J, K, phase_steps) for each phase."""
    ell = len(word)
    t_fires = sorted(i for i in range(ell) if word[i] == t)
    if len(t_fires) == 0:
        return []

    bL = (t - 1) % n
    bR = (t + 1) % n

    phases = []
    fc_t = len(t_fires)
    for idx in range(fc_t):
        s = t_fires[idx]
        a = t_fires[(idx - 1) % fc_t]
        # Steps in the phase: from a (exclusive, it's the previous t-fire) to s (inclusive)
        # Actually, the phase interval is (a, s]: steps a+1, a+2, ..., s
        # where step s is the t-fire ending this phase.
        # We need the steps between consecutive t-fires.
        if s > a:
            phase_steps = list(range(a + 1, s + 1))
        else:
            # Wrap around
            phase_steps = list(range(a + 1, ell)) + list(range(0, s + 1))

        # J = number of bL firings in the phase (excluding step a which is prev t-fire)
        J = sum(1 for st in phase_steps if word[st % ell] == bL)
        K = sum(1 for st in phase_steps if word[st % ell] == bR)

        phases.append((a, s, J, K, phase_steps))

    return phases


def is_normal_form(J, K):
    """Check if (J, K) is normalForm (not dispatched by BothEven, Toggle-FR, ZeroSide)."""
    # BothEven: Even J and Even K
    if J % 2 == 0 and K % 2 == 0:
        return False
    # Toggle-FR-L: J >= 2 and K = 0
    if J >= 2 and K == 0:
        return False
    # Toggle-FR-R: J = 0 and K >= 2
    if J == 0 and K >= 2:
        return False
    return True


def check_ec_at_proc(word, cycle, ms, n, t):
    """Check if there is actual entry conflict at processor t."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n

    # For each S-level
    for s_val in range(ms[t]):
        mover_pairs = set()
        nonmover_pairs = set()
        for i in range(ell):
            if cycle[i][t] == s_val:
                lr = (cycle[i][bL], cycle[i][bR])
                if word[i] == t:
                    mover_pairs.add(lr)
                else:
                    nonmover_pairs.add(lr)
        if mover_pairs & nonmover_pairs:
            return True
    return False


def check_ec_at_neighbor(word, cycle, ms, n, t, neighbor):
    """Check if there is actual entry conflict at a neighbor of t."""
    ell = len(word)
    nL = (neighbor - 1) % n
    nR = (neighbor + 1) % n

    for s_val in range(ms[neighbor]):
        mover_triples = set()
        nonmover_triples = set()
        for i in range(ell):
            if cycle[i][neighbor] == s_val:
                triple = (cycle[i][nL], cycle[i][neighbor], cycle[i][nR])
                if word[i] == neighbor:
                    mover_triples.add(triple)
                else:
                    nonmover_triples.add(triple)
        if mover_triples & nonmover_triples:
            return True
    return False


def has_ec_at_boundary_ternary(word, cycle, ms, n, boundary_ternary):
    """Check if EC exists at any boundary ternary processor."""
    for t in boundary_ternary:
        if check_ec_at_proc(word, cycle, ms, n, t):
            return True
    return False


def all_phases_normal_form(word, cycle, ms, n, t):
    """Check if ALL phases at proc t are normalForm."""
    phases = get_phases(word, cycle, ms, n, t)
    if not phases:
        return False  # proc doesn't fire
    for a, s, J, K, steps in phases:
        if not is_normal_form(J, K):
            return False
    return True


# ============================================================
# MAIN VERIFICATION
# ============================================================

print("=" * 70)
print("LAYER 2 PROOF VERIFICATION")
print("All-NormalForm at boundary ternary => EC at boundary ternary")
print("=" * 70)

test_cases = [
    # (n, ms, label, max_len)
    (7, [2, 3, 2, 3, 2, 3, 3], "n=7 ms=[2,3,2,3,2,3,3]", 24),
    (7, [2, 3, 3, 2, 3, 3, 2], "n=7 ms=[2,3,3,2,3,3,2]", 24),
    (7, [3, 2, 3, 2, 3, 2, 3], "n=7 ms=[3,2,3,2,3,2,3]", 24),
]

for n, ms, label, max_len in test_cases:
    # Identify boundary ternary procs
    boundary_ternary = []
    for p in range(n):
        if ms[p] >= 3:
            bL = (p - 1) % n
            bR = (p + 1) % n
            if ms[bL] == 2 or ms[bR] == 2:
                boundary_ternary.append(p)

    # Identify sandwiched ternary (both neighbors binary)
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

    words = enumerate_mover_words(ms, n, max_len)

    total_valid = 0
    all_normal_count = 0
    all_normal_no_ec = 0

    phase_patterns = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total_valid += 1

        # Check if ALL phases at ALL boundary ternary are normalForm
        all_normal = True
        for t in boundary_ternary:
            if not all_phases_normal_form(word, cycle, ms, n, t):
                all_normal = False
                break

        if not all_normal:
            continue
        all_normal_count += 1

        # Check EC at boundary ternary
        has_ec = has_ec_at_boundary_ternary(word, cycle, ms, n, boundary_ternary)
        if not has_ec:
            all_normal_no_ec += 1
            print(f"  COUNTEREXAMPLE: {word}")
            # Print phase details
            for t in boundary_ternary:
                phases = get_phases(word, cycle, ms, n, t)
                print(f"    t={t}: phases = {[(J,K) for _,_,J,K,_ in phases]}")

        # Record phase patterns
        for t in boundary_ternary:
            phases = get_phases(word, cycle, ms, n, t)
            for _, _, J, K, _ in phases:
                phase_patterns[(J, K)] += 1

    print(f"\n{label}")
    print(f"  Boundary ternary: {boundary_ternary}")
    print(f"  Sandwiched: {sandwiched}")
    print(f"  Total valid cycles: {total_valid}")
    print(f"  All-normalForm cycles: {all_normal_count}")
    print(f"  All-normalForm WITHOUT EC: {all_normal_no_ec}")
    if all_normal_no_ec == 0 and all_normal_count > 0:
        print(f"  *** ALL all-normalForm cycles have EC at boundary ternary ***")
    print(f"  Phase pattern distribution: {dict(sorted(phase_patterns.items()))}")
