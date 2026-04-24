#!/usr/bin/env python3
"""RA12: Does normalForm (1,1) at a sandwiched ternary universally force entry conflict?

For self-stabilizing token ring systems with sub-threshold state products
and >=3 binary processors: when a good cycle has a "normalForm (1,1)" phase
at a sandwiched ternary t, does entry conflict ALWAYS exist?

A "sandwiched ternary" t has binary (m=2) neighbors on both sides.
A "(1,1) phase" at t: between consecutive firings of t, each binary neighbor
fires exactly once.

Entry conflict at t: some (L,t,R) triple appears both when t is mover
(must change state) and when t is non-mover (must keep state).

Approach:
1. Enumerate all sub-threshold state vectors with >=3 binary and >=1 sandwiched ternary.
2. Enumerate all mover words (good cycles with incrementing transitions).
3. For each cycle, identify phases at each sandwiched ternary.
4. Filter to cycles with at least one (1,1) phase.
5. Check if entry conflict exists at that sandwiched ternary.
6. Report: fraction with EC, any exceptions.

Note: Entry conflict is transition-independent. If (L,S,R) appears at both mover
and non-mover steps for processor t, then for ANY transition function f_t,
either f_t(L,S,R)=S (non-mover correct, mover broken) or f_t(L,S,R)!=S
(mover correct, non-mover broken). So checking overlap on incrementing-transition
cycles is SUFFICIENT to detect structural EC.
"""

from collections import Counter, defaultdict
from itertools import product as iproduct
import time


def enumerate_mover_words(ms, n, max_length):
    """Enumerate all good-cycle mover words with incrementing transitions."""
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
    """Build configuration sequence from mover word with incrementing transitions."""
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
    """Check if first and last movers are ring-adjacent (valid cyclic walk)."""
    return abs(word[-1] - word[0]) % n in (1, n-1)


def get_phases(word, cycle, t, n):
    """Get all phases at ternary processor t.

    A phase = the interval between consecutive firings of t.
    Returns list of phases, each phase is a dict with:
      - t_fire_step: step index where t fires (start of next phase)
      - steps: list of step indices in the phase (between two t-firings)
      - J: number of times left binary fires
      - K: number of times right binary fires
      - mover_seq: sequence of movers in this phase
    """
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n

    # Find all steps where t fires
    t_steps = [s for s in range(ell) if word[s] == t]
    if len(t_steps) == 0:
        return []

    phases = []
    for idx in range(len(t_steps)):
        start = t_steps[idx]
        end = t_steps[(idx + 1) % len(t_steps)]

        # Collect steps in this phase (after t fires, before t fires again)
        phase_steps = []
        s = (start + 1) % ell
        while s != end:
            phase_steps.append(s)
            s = (s + 1) % ell

        J = sum(1 for s in phase_steps if word[s] == bL)
        K = sum(1 for s in phase_steps if word[s] == bR)
        mover_seq = [word[s] for s in phase_steps]

        phases.append({
            't_fire_step': start,
            't_fire_end': end,
            'steps': phase_steps,
            'J': J,
            'K': K,
            'mover_seq': mover_seq,
            'length': len(phase_steps),
        })

    return phases


def check_ec_at_proc(word, cycle, p, ms, n):
    """Check if entry conflict exists at processor p.

    EC at p: exists (L,S,R) that appears both when p is mover and when p is non-mover.
    """
    ell = len(word)
    bL = (p - 1) % n
    bR = (p + 1) % n

    mover_contexts = set()
    nonmover_contexts = set()

    for s in range(ell):
        ctx = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p:
            mover_contexts.add(ctx)
        else:
            nonmover_contexts.add(ctx)

    overlap = mover_contexts & nonmover_contexts
    return len(overlap) > 0, overlap, mover_contexts, nonmover_contexts


def check_ec_at_proc_in_phase(word, cycle, t, phase, ms, n):
    """Check if entry conflict exists at ternary t specifically due to a (1,1) phase.

    In a (1,1) phase: between t-firing at step 'start' and t-firing at step 'end',
    left binary fires once, right binary fires once.

    The t-firing step gives a mover context at t.
    The steps in the phase give non-mover contexts at t.

    We check overlap between:
    - mover context at t when t fires (at t_fire_step)
    - non-mover contexts at t during the phase steps
    """
    bL = (t - 1) % n
    bR = (t + 1) % n

    t_step = phase['t_fire_step']
    mover_ctx = (cycle[t_step][bL], cycle[t_step][t], cycle[t_step][bR])

    nonmover_ctxs = set()
    for s in phase['steps']:
        ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
        nonmover_ctxs.add(ctx)

    has_overlap = mover_ctx in nonmover_ctxs
    return has_overlap, mover_ctx, nonmover_ctxs


def get_sub_threshold_systems(n, max_product=None):
    """Get all sub-threshold state vectors with >=3 binary and >=1 sandwiched ternary."""
    threshold = 4 * (3 ** (n - 2))
    if max_product is not None:
        threshold = min(threshold, max_product)

    # For n=5: threshold = 4*27 = 108
    # For n=7: threshold = 4*243 = 972
    # State sizes: binary (2) or ternary (3) [and possibly quaternary, but sub-threshold limits this]

    # Enumerate all state vectors with entries in {2, 3} that have product < threshold
    results = []
    for ms_tuple in iproduct(*[range(2, 4) for _ in range(n)]):
        ms = list(ms_tuple)
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        num_binary = sum(1 for m in ms if m == 2)
        if num_binary < 3:
            continue

        # Check for sandwiched ternary
        sandwiched = []
        for p in range(n):
            if ms[p] == 3 and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2:
                sandwiched.append(p)

        if len(sandwiched) == 0:
            continue

        results.append((ms, sandwiched))

    return results


def analyze_system(ms, n, sandwiched, max_len, label=""):
    """Analyze all good cycles for one system."""
    words = enumerate_mover_words(ms, n, max_len)

    total_cycles = 0
    cycles_with_11_phase = 0
    cycles_with_11_and_ec = 0
    cycles_with_11_no_ec = []  # counterexamples

    phase_stats = Counter()  # (J,K) -> count of phases

    # Also track: per-phase EC (does the specific phase cause EC, vs global EC)
    phase_ec_count = 0
    phase_no_ec_count = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        if not is_wrap_adjacent(word, n):
            continue

        total_cycles += 1
        ell = len(word)

        has_11_phase = False
        has_ec_global = False
        has_ec_from_11 = False

        for t in sandwiched:
            phases = get_phases(word, cycle, t, n)

            for phase in phases:
                phase_stats[(phase['J'], phase['K'])] += 1

                if phase['J'] == 1 and phase['K'] == 1:
                    has_11_phase = True

                    # Check phase-specific EC
                    has_phase_ec, mover_ctx, nonmover_ctxs = check_ec_at_proc_in_phase(
                        word, cycle, t, phase, ms, n)
                    if has_phase_ec:
                        phase_ec_count += 1
                        has_ec_from_11 = True
                    else:
                        phase_no_ec_count += 1

            # Check global EC at t
            has_ec, overlap, mctx, nmctx = check_ec_at_proc(word, cycle, t, ms, n)
            if has_ec:
                has_ec_global = True

        if has_11_phase:
            cycles_with_11_phase += 1
            if has_ec_global:
                cycles_with_11_and_ec += 1
            else:
                cycles_with_11_no_ec.append((word, cycle))

    return {
        'total_cycles': total_cycles,
        'cycles_with_11_phase': cycles_with_11_phase,
        'cycles_with_11_and_ec': cycles_with_11_and_ec,
        'cycles_with_11_no_ec': cycles_with_11_no_ec,
        'phase_stats': phase_stats,
        'phase_ec_count': phase_ec_count,
        'phase_no_ec_count': phase_no_ec_count,
    }


# =============================================================================
# MAIN INVESTIGATION
# =============================================================================

print("=" * 70)
print("RA12: NormalForm (1,1) at sandwiched ternary → entry conflict?")
print("=" * 70)

# --- n=5 ---
print("\n" + "=" * 70)
print("n=5: Sub-threshold systems with >=3 binary, sandwiched ternary")
print("=" * 70)

n = 5
threshold = 4 * (3 ** (n - 2))
print(f"Threshold: 4 * 3^{n-2} = {threshold}")

systems = get_sub_threshold_systems(n)
print(f"Systems found: {len(systems)}")

for ms, sandwiched in systems:
    prod = 1
    for m in ms:
        prod *= m
    label = f"ms={ms}, prod={prod}, sandwiched={sandwiched}"
    print(f"\n--- {label} ---")

    t0 = time.time()
    result = analyze_system(ms, n, sandwiched, max_len=20, label=label)
    elapsed = time.time() - t0

    print(f"  Total valid cycles: {result['total_cycles']}")
    print(f"  Cycles with (1,1) phase: {result['cycles_with_11_phase']}")
    print(f"  Of those with EC (global): {result['cycles_with_11_and_ec']}")
    print(f"  Exceptions (no EC): {len(result['cycles_with_11_no_ec'])}")
    print(f"  Phase (J,K) distribution:")
    for (j, k), cnt in sorted(result['phase_stats'].items()):
        print(f"    ({j},{k}): {cnt}")
    print(f"  Phase-specific EC: {result['phase_ec_count']}/{result['phase_ec_count'] + result['phase_no_ec_count']}")
    print(f"  Time: {elapsed:.1f}s")

    if result['cycles_with_11_no_ec']:
        print(f"\n  *** COUNTEREXAMPLES ***")
        for word, cycle in result['cycles_with_11_no_ec'][:3]:
            print(f"    Word: {word}")
            print(f"    Cycle length: {len(cycle)}")
            # Show the phases
            for t in sandwiched:
                phases = get_phases(word, cycle, t, n)
                for i, phase in enumerate(phases):
                    if phase['J'] == 1 and phase['K'] == 1:
                        print(f"    Proc {t} phase {i}: J={phase['J']}, K={phase['K']}, "
                              f"mover_seq={phase['mover_seq']}")
                        has_ph_ec, mctx, nmctxs = check_ec_at_proc_in_phase(
                            word, cycle, t, phase, ms, n)
                        print(f"      Mover ctx: {mctx}")
                        print(f"      Non-mover ctxs: {nmctxs}")
                        print(f"      Phase EC: {has_ph_ec}")
                # Show global EC check
                has_ec, overlap, mctx, nmctx = check_ec_at_proc(word, cycle, t, ms, n)
                print(f"    Proc {t} global: mover_ctxs={mctx}, nonmover_ctxs={nmctx}")
                print(f"      Overlap: {overlap}")

# --- Summary ---
print("\n" + "=" * 70)
print("SUMMARY: n=5")
print("=" * 70)

total_11 = 0
total_ec = 0
total_exceptions = 0
for ms, sandwiched in systems:
    result = analyze_system(ms, n, sandwiched, max_len=20)
    total_11 += result['cycles_with_11_phase']
    total_ec += result['cycles_with_11_and_ec']
    total_exceptions += len(result['cycles_with_11_no_ec'])

print(f"Total cycles with (1,1) phase: {total_11}")
print(f"Of those with EC: {total_ec}")
print(f"Exceptions: {total_exceptions}")
if total_exceptions == 0 and total_11 > 0:
    print("*** UNIVERSAL: (1,1) at sandwiched ternary ALWAYS implies EC at n=5 ***")


# --- n=7 ---
print("\n" + "=" * 70)
print("n=7: Sub-threshold systems with >=3 binary, sandwiched ternary")
print("=" * 70)

n = 7
threshold = 4 * (3 ** (n - 2))
print(f"Threshold: 4 * 3^{n-2} = {threshold}")

systems7 = get_sub_threshold_systems(n)
print(f"Systems found: {len(systems7)}")

# n=7 may have more cycles, be careful with max_len
for ms, sandwiched in systems7:
    prod = 1
    for m in ms:
        prod *= m
    label = f"ms={ms}, prod={prod}, sandwiched={sandwiched}"
    print(f"\n--- {label} ---")

    t0 = time.time()
    # Start with smaller max_len for n=7
    result = analyze_system(ms, n, sandwiched, max_len=22, label=label)
    elapsed = time.time() - t0

    print(f"  Total valid cycles: {result['total_cycles']}")
    print(f"  Cycles with (1,1) phase: {result['cycles_with_11_phase']}")
    print(f"  Of those with EC (global): {result['cycles_with_11_and_ec']}")
    print(f"  Exceptions (no EC): {len(result['cycles_with_11_no_ec'])}")
    if result['phase_stats']:
        print(f"  Phase (J,K) distribution:")
        for (j, k), cnt in sorted(result['phase_stats'].items()):
            print(f"    ({j},{k}): {cnt}")
    print(f"  Phase-specific EC: {result['phase_ec_count']}/{result['phase_ec_count'] + result['phase_no_ec_count']}")
    print(f"  Time: {elapsed:.1f}s")

    if result['cycles_with_11_no_ec']:
        print(f"\n  *** COUNTEREXAMPLES ***")
        for word, cycle in result['cycles_with_11_no_ec'][:2]:
            print(f"    Word: {word}")
            for t in sandwiched:
                phases = get_phases(word, cycle, t, n)
                for i, phase in enumerate(phases):
                    if phase['J'] == 1 and phase['K'] == 1:
                        has_ph_ec, mctx, nmctxs = check_ec_at_proc_in_phase(
                            word, cycle, t, phase, ms, n)
                        print(f"    Proc {t} phase {i}: mover_ctx={mctx}, "
                              f"non-mover_ctxs={nmctxs}, phase_ec={has_ph_ec}")

    if elapsed > 60:
        print(f"  (skipping remaining n=7 systems due to time)")
        break

print("\n" + "=" * 70)
print("n=7 SUMMARY")
print("=" * 70)
total_11_7 = 0
total_ec_7 = 0
total_exc_7 = 0
for ms, sandwiched in systems7:
    # Re-use cached results would be better but just re-run for summary
    result = analyze_system(ms, n, sandwiched, max_len=22)
    total_11_7 += result['cycles_with_11_phase']
    total_ec_7 += result['cycles_with_11_and_ec']
    total_exc_7 += len(result['cycles_with_11_no_ec'])

print(f"Total cycles with (1,1) phase: {total_11_7}")
print(f"Of those with EC: {total_ec_7}")
print(f"Exceptions: {total_exc_7}")
if total_exc_7 == 0 and total_11_7 > 0:
    print("*** UNIVERSAL: (1,1) at sandwiched ternary ALWAYS implies EC at n=7 ***")
elif total_exc_7 > 0:
    print(f"*** NOT UNIVERSAL: {total_exc_7} exceptions found at n=7 ***")


# --- MECHANISM ANALYSIS ---
# If universal, explain WHY (1,1) forces EC

print("\n" + "=" * 70)
print("MECHANISM ANALYSIS: Why does (1,1) force EC?")
print("=" * 70)

print("""
In a (1,1) phase at sandwiched ternary t (binary L on left, binary R on right):
  Step 0: t fires. Config has (L=a, t=v, R=b). t changes: v -> v'.
  Step 1..k: other procs fire. At some point L fires once, R fires once.
  Step k+1: t fires again. Config has (L=a', t=v', R=b').

Since L is binary: a' = 1-a (L toggled once).
Since R is binary: b' = 1-b (R toggled once).

The mover context at t's first firing: (a, v, b).
The non-mover contexts at t during the phase include states before/after L,R fire.

Key: between t's two firings, t doesn't fire, so t stays at v' throughout the phase.
So all non-mover contexts at t have middle value v'.

The mover context has middle value v.
If v != v': no overlap possible (different middle values).
If v == v': then t fires with (a, v, b) and transitions to v' = v. But that means
  t is NOT privileged (f(a,v,b) = v), contradiction — t must be the mover (privileged).

Wait, this isn't right. Let me think again...

Actually: t fires 3 times per full cycle (it's ternary with incrementing transition,
so it fires m_t = 3 times). Each firing changes t's state. The phase is between
two CONSECUTIVE firings of t. So:
  - At t's firing (step s): context is (L_s, t_s, R_s), t changes t_s -> t_s'.
  - During phase steps: t has state t_s' (doesn't change until next t-firing).
  - At t's next firing (step s'): context is (L_s', t_s', R_s').

For mover step s: context = (L_s, t_s, R_s).
For non-mover steps in phase: context at t = (L_?, t_s', R_?).

Since t_s != t_s' (t actually changed state when it fired):
  mover context has middle = t_s
  non-mover contexts in THIS phase have middle = t_s'
  These are different → no overlap from THIS phase alone.

BUT: other phases have different t-values. The question is whether a mover context
from one phase matches a non-mover context from another phase.
""")

# Let's verify this reasoning computationally
print("\nVerifying: do (1,1) phases create CROSS-PHASE EC?")

n = 5
for ms, sandwiched in get_sub_threshold_systems(n):
    prod = 1
    for m in ms:
        prod *= m

    words = enumerate_mover_words(ms, n, max_len=20)

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)

        for t in sandwiched:
            phases = get_phases(word, cycle, t, n)
            bL = (t - 1) % n
            bR = (t + 1) % n

            has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
            if not has_11:
                continue

            # Collect per-phase mover and non-mover contexts
            all_mover = []
            all_nonmover = []

            for i, phase in enumerate(phases):
                s = phase['t_fire_step']
                mctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])

                nm_ctxs = set()
                for step in phase['steps']:
                    ctx = (cycle[step][bL], cycle[step][t], cycle[step][bR])
                    nm_ctxs.add(ctx)

                all_mover.append((i, mctx, phase['J'], phase['K']))
                all_nonmover.append((i, nm_ctxs, phase['J'], phase['K']))

            # Check: does same-phase overlap happen?
            same_phase_ec = False
            cross_phase_ec = False

            for i, mctx, mJ, mK in all_mover:
                _, nm_ctxs_same, _, _ = all_nonmover[i]
                if mctx in nm_ctxs_same:
                    same_phase_ec = True

                for j, nm_ctxs, _, _ in all_nonmover:
                    if j != i and mctx in nm_ctxs:
                        cross_phase_ec = True

            if same_phase_ec or cross_phase_ec:
                # Just track the first example
                pass
    break  # Just first system for now

# More detailed trace for one example
print("\nDetailed trace for ms=[2,2,2,3,3], n=5:")
ms = [2, 2, 2, 3, 3]
n = 5
sandwiched = [p for p in range(n) if ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
print(f"  Sandwiched ternary: {sandwiched}")

words = enumerate_mover_words(ms, n, max_len=20)
count_shown = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in sandwiched:
        phases = get_phases(word, cycle, t, n)
        bL = (t - 1) % n
        bR = (t + 1) % n

        has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
        if not has_11:
            continue

        if count_shown >= 3:
            continue
        count_shown += 1

        print(f"\n  Word: {word}")
        print(f"  Cycle length: {ell}")
        print(f"  Sandwiched ternary t={t}, bL={bL}, bR={bR}")

        for i, phase in enumerate(phases):
            s = phase['t_fire_step']
            mctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])

            print(f"  Phase {i}: J={phase['J']}, K={phase['K']}, "
                  f"t fires at step {s}, mover_ctx={mctx}")

            for step in phase['steps']:
                ctx = (cycle[step][bL], cycle[step][t], cycle[step][bR])
                mover = word[step]
                print(f"    Step {step}: mover={mover}, config={cycle[step]}, "
                      f"ctx@t={ctx}")

        # Show overlap
        all_mover_ctxs = set()
        all_nonmover_ctxs = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                all_mover_ctxs.add(ctx)
            else:
                all_nonmover_ctxs.add(ctx)

        overlap = all_mover_ctxs & all_nonmover_ctxs
        print(f"  Global: mover_ctxs={all_mover_ctxs}, nonmover_ctxs={all_nonmover_ctxs}")
        print(f"  Overlap: {overlap}")
        print(f"  EC: {'YES' if overlap else 'NO'}")
