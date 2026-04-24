#!/usr/bin/env python3
"""Why can't 2 single-round ternary be simultaneously non-OSB?

Key facts established:
1. Non-OSB requires asymmetric binary neighbors: one "heavy" (fc>=4), one "light" (fc=2)
2. On n=6 alternating, exactly 2 ternary are single-round (parity: ternary sum = 12)
3. The 2 single-round ternary SHARE a binary neighbor
4. Never both non-OSB simultaneously (0/91,872)

This script investigates the coupling through shared binary P2.

Hypothesis: dur-4 phases are always OSB (proved by walk tracing on bipartite ring).
When one ternary is non-OSB (no dur-4 phases), does the shared binary coupling
FORCE the other ternary to have a dur-4 phase?
"""
import sys, time
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

def get_phase_info(ms, n, word, cycle, t):
    """Get per-phase firing info for ternary t."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    phases = []
    for k in range(ms[t]):
        ps = [s for s in range(ell) if cycle[s][t] == k]
        bLf = sum(1 for s in ps if word[s] == bL)
        bRf = sum(1 for s in ps if word[s] == bR)
        dur = len(ps)
        phases.append({'k': k, 'dur': dur, 'bLf': bLf, 'bRf': bRf,
                       'steps': ps})
    return phases

def is_osb_phase(bLf, bRf):
    return min(bLf, bRf) == 0 and max(bLf, bRf) >= 2

def has_osb(phases):
    return any(is_osb_phase(p['bLf'], p['bRf']) for p in phases)

print("=" * 70)
print("SHARED BINARY COUPLING ANALYSIS")
print("=" * 70)

n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]

t0 = time.time()
words = enumerate_mover_words(ms, n, 24)
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

# PART 1: When P1 is non-OSB, analyze P3's phase structure
print(f"\n{'='*60}")
print("PART 1: P1 NON-OSB → P3 PHASE ANALYSIS")

p1_nonOSB = 0
p3_has_dur4_when_p1_nonOSB = 0
p3_dur_dist = Counter()
p3_osb_mechanism = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    # Check all pairs of adjacent single-round ternary
    for t1, t2 in [(1,3), (3,5), (5,1)]:
        if fc[t1] != ms[t1] or fc[t2] != ms[t2]:
            continue  # both must be single-round

        phases1 = get_phase_info(ms, n, word, cycle, t1)
        if has_osb(phases1):
            continue  # t1 has OSB, not interesting

        # t1 is non-OSB. Check t2.
        p1_nonOSB += 1
        phases2 = get_phase_info(ms, n, word, cycle, t2)

        has_dur4 = any(p['dur'] == 4 for p in phases2)
        if has_dur4:
            p3_has_dur4_when_p1_nonOSB += 1

        for p in phases2:
            p3_dur_dist[p['dur']] += 1
            if is_osb_phase(p['bLf'], p['bRf']):
                p3_osb_mechanism[(p['dur'], p['bLf'], p['bRf'])] += 1

print(f"  Cases where one SR ternary is non-OSB: {p1_nonOSB}")
print(f"  Partner has dur-4 phase: {p3_has_dur4_when_p1_nonOSB}/{p1_nonOSB} "
      f"({100*p3_has_dur4_when_p1_nonOSB/p1_nonOSB:.1f}%)" if p1_nonOSB else "  N/A")

print(f"\n  Partner phase duration distribution:")
for dur, cnt in sorted(p3_dur_dist.items()):
    print(f"    dur={dur}: {cnt}")

print(f"\n  Partner OSB mechanisms (dur, bLf, bRf):")
for mech, cnt in sorted(p3_osb_mechanism.items(), key=lambda x: -x[1])[:15]:
    print(f"    dur={mech[0]}, bL={mech[1]}, bR={mech[2]}: {cnt}")

# PART 2: Trace dur-4 walk structure
print(f"\n{'='*60}")
print("PART 2: DUR-4 WALK STRUCTURE (PROOF THAT DUR-4 = OSB)")

dur4_binary_pattern = Counter()  # which binaries fire in dur-4 phases

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in tern:
        for k in range(ms[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            if len(ps) != 4:
                continue  # only dur-4
            bL = (t - 1) % n
            bR = (t + 1) % n
            bLf = sum(1 for s in ps if word[s] == bL)
            bRf = sum(1 for s in ps if word[s] == bR)
            dur4_binary_pattern[(bLf, bRf)] += 1

print(f"  Dur-4 phase (bLf, bRf) patterns:")
for (bLf, bRf), cnt in sorted(dur4_binary_pattern.items(), key=lambda x: -x[1]):
    is_osb = is_osb_phase(bLf, bRf)
    print(f"    bL={bLf}, bR={bRf}: {cnt}  {'OSB ✓' if is_osb else 'NOT OSB ✗'}")

# PART 3: Shared binary phase coupling
# When P1 is non-OSB, how are P2's firings distributed
# across P1-phases vs P3-phases?
print(f"\n{'='*60}")
print("PART 3: SHARED BINARY P2 PHASE COUPLING (P1 non-OSB)")

p2_joint_dist = Counter()  # (P1-phase, P3-phase) of each P2 firing

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    # Only look at cycles where P1 is single-round non-OSB
    if fc[1] != 3 or fc[3] != 3:
        continue

    phases1 = get_phase_info(ms, n, word, cycle, 1)
    if has_osb(phases1):
        continue

    # P2's firings: each has (P1-phase, P3-phase)
    for s in range(ell):
        if word[s] == 2:
            p1_phase = cycle[s][1]
            p3_phase = cycle[s][3]
            p2_joint_dist[(p1_phase, p3_phase)] += 1

print(f"  P2 firing joint distribution (P1-phase, P3-phase) when P1 is non-OSB:")
for (p1, p3), cnt in sorted(p2_joint_dist.items()):
    print(f"    P1-phase={p1}, P3-phase={p3}: {cnt}")

# PART 4: For each P1-nonOSB cycle, check P3's dur-4 phase details
print(f"\n{'='*60}")
print("PART 4: P3 DUR-4 PHASE IN P1-NONOSB CYCLES")

p3_dur4_detail = Counter()
p3_dur4_binary_shared = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    if fc[1] != 3 or fc[3] != 3:
        continue

    phases1 = get_phase_info(ms, n, word, cycle, 1)
    if has_osb(phases1):
        continue

    phases3 = get_phase_info(ms, n, word, cycle, 3)

    # Find dur-4 phases at P3
    for p in phases3:
        if p['dur'] == 4:
            # Which binary fires? P2 (shared with P1) or P4?
            p3_dur4_detail[(p['bLf'], p['bRf'])] += 1
            if p['bLf'] > 0:  # P2 fires
                p3_dur4_binary_shared['P2'] += 1
            if p['bRf'] > 0:  # P4 fires
                p3_dur4_binary_shared['P4'] += 1

print(f"  P3 dur-4 phases (bL=P2, bR=P4) when P1 is non-OSB:")
for (bLf, bRf), cnt in sorted(p3_dur4_detail.items(), key=lambda x: -x[1]):
    print(f"    P2={bLf}, P4={bRf}: {cnt}")
print(f"  Binary involvement: {dict(p3_dur4_binary_shared)}")

# PART 5: CRITICAL - Check if dur-4 is the ONLY OSB mechanism at P3
# when P1 is non-OSB
print(f"\n{'='*60}")
print("PART 5: OSB MECHANISM AT P3 WHEN P1 IS NON-OSB")

p3_osb_all_dur = Counter()
p3_osb_dur4_only = 0
p3_osb_non_dur4 = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    if fc[1] != 3 or fc[3] != 3:
        continue

    phases1 = get_phase_info(ms, n, word, cycle, 1)
    if has_osb(phases1):
        continue

    phases3 = get_phase_info(ms, n, word, cycle, 3)
    osb_durs = [p['dur'] for p in phases3 if is_osb_phase(p['bLf'], p['bRf'])]

    if osb_durs:
        if all(d == 4 for d in osb_durs):
            p3_osb_dur4_only += 1
        else:
            p3_osb_non_dur4 += 1
        for d in osb_durs:
            p3_osb_all_dur[d] += 1

print(f"  P3 OSB from dur-4 only: {p3_osb_dur4_only}")
print(f"  P3 OSB from non-dur-4: {p3_osb_non_dur4}")
print(f"  P3 OSB phase durations: {dict(sorted(p3_osb_all_dur.items()))}")

# PART 6: Walk trace - WHY does non-OSB at P1 force dur-4 at P3?
# Non-OSB at P1 means: P1 avoids dur-4. This means P1's phases are
# dur-2, dur-6, dur-8, etc. P1's binary neighbors alternate.
# What does this imply about P3?
print(f"\n{'='*60}")
print("PART 6: P1 PHASE DURATIONS WHEN P1 IS NON-OSB")

p1_nonOSB_dur = Counter()
p1_nonOSB_dur_tuple = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    if fc[1] != 3 or fc[3] != 3:
        continue

    phases1 = get_phase_info(ms, n, word, cycle, 1)
    if has_osb(phases1):
        continue

    durs = tuple(sorted(p['dur'] for p in phases1))
    p1_nonOSB_dur_tuple[durs] += 1
    for p in phases1:
        p1_nonOSB_dur[p['dur']] += 1

print(f"  P1 phase duration tuples (sorted) when P1 is non-OSB:")
for durs, cnt in sorted(p1_nonOSB_dur_tuple.items(), key=lambda x: -x[1]):
    print(f"    {durs}: {cnt}")

print(f"\n  P1 phase durations: {dict(sorted(p1_nonOSB_dur.items()))}")

# PART 7: GENERAL - Is dur-4 always OSB for any n?
# On bipartite ring, dur-4 phase: B-T-B-T (from mover perspective).
# First B can be bL or bR. Second B must be same (return to t in 4 steps).
# Proof: on bipartite ring of size n, from ternary t, the only 4-step
# return path is t→bX→t'→bX→t (where t' = t±2 and bX = t±1).
# Both B steps fire the SAME binary → bXf=2, other=0 → OSB.
print(f"\n{'='*60}")
print("PART 7: DUR-4 = OSB ON BIPARTITE RING (ANALYTICAL)")
print("")
print("Claim: On bipartite ring (even n), every dur-4 phase is one-sided bounce.")
print("")
print("Proof: Phase of ternary t has dur=4: B₁-T₁-B₂-T₂(=mover t).")
print("  B₁ fires neighbor of prev t-firing: bL or bR.")
print("  T₁ fires neighbor of B₁, not t (would end phase). So T₁ = t±2.")
print("  B₂ fires neighbor of T₁. Must lead to T₂=t, so B₂ = neighbor of t.")
print("  B₂ must also be neighbor of T₁ = t±2.")
print("  On ring: neighbor(t±2) ∩ neighbor(t) = {t±1} = {bL or bR, same as B₁}.")
print("  Therefore B₁ = B₂ (same binary fires twice). bLf=2,bRf=0 or vice versa.")
print("  This is one-sided bounce (OSB). ∎")
print("")
print("Formalized: neighbor(t-2) = {t-3, t-1}. neighbor(t) = {t-1, t+1}.")
print("  intersection = {t-1} = bL. So if T₁=t-2, both B steps fire bL.")
print("  Similarly if T₁=t+2, both fire bR. Always one-sided. ∎")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
sys.stdout.flush()
