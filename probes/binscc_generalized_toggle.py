#!/usr/bin/env python3
"""GENERALIZED TOGGLE-FR: Does (J,K) = (≥2, 0) or (0, ≥2) force entry conflict?

Theorem attempt: In a phase k of sandwiched ternary T (m_T=3, neighbors binary m=2)
with M_k = 1 mover step:
  If K_k = 0 and J_k ≥ 2: entry conflict at T in phase k.
  If J_k = 0 and K_k ≥ 2: entry conflict at T in phase k.

Proof sketch:
  K_k = 0 → R fixed at R₀ throughout phase.
  J_k ≥ 2 → bL fires ≥ 2 times. Nonmover entries include
    (L₀, k, R₀) and (1-L₀, k, R₀) — both L values.
  Mover step (last step of phase): sees (L_m, k, R₀).
  L_m ∈ {L₀, 1-L₀} → matches one nonmover entry. EC! ∎

Verify computationally: does (J_k ≥ 2, K_k = 0) ALWAYS have EC?
"""
import time
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

# Test the generalized Toggle-FR
print("=" * 70)
print("GENERALIZED TOGGLE-FR VERIFICATION")
print("=" * 70)

for n, ms, label, max_len in [
    (4, [2,3,2,3], "n=4 alt", 14),
    (5, [2,3,2,3,2], "n=5 alt", 16),
    (6, [2,3,2,3,2,3], "n=6 alt", 24),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    print(f"\n{label}: {len(words)} words ({time.time()-t0:.1f}s)")

    sandwiched = [p for p in range(n) if ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    total = 0
    # (J_k condition, K_k condition, has_ec at that phase)
    phase_ec_test = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)

        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                M = sum(1 for s in steps if word[s] == t)

                # Check entry conflict at this specific phase
                mover_lsr = set()
                nonmover_lsr = set()
                for s in steps:
                    lsr = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                    if word[s] == t:
                        mover_lsr.add(lsr)
                    else:
                        nonmover_lsr.add(lsr)
                has_ec = bool(mover_lsr & nonmover_lsr)

                # Classify
                if K == 0 and J >= 2:
                    phase_ec_test[("J≥2,K=0", J, K, has_ec)] += 1
                elif J == 0 and K >= 2:
                    phase_ec_test[("J=0,K≥2", J, K, has_ec)] += 1
                elif K == 0 and J == 1:
                    phase_ec_test[("J=1,K=0", J, K, has_ec)] += 1
                elif J == 0 and K == 1:
                    phase_ec_test[("J=0,K=1", J, K, has_ec)] += 1
                elif J == 0 and K == 0:
                    phase_ec_test[("J=0,K=0", J, K, has_ec)] += 1
                elif J % 2 == 0 and K % 2 == 0:
                    phase_ec_test[("both_even", J, K, has_ec)] += 1
                else:
                    phase_ec_test[("anti_diag", J, K, has_ec)] += 1

    print(f"  Total cycles: {total}")
    print(f"  Phase-level entry conflict analysis:")
    for (cat, J, K, ec), cnt in sorted(phase_ec_test.items()):
        pct = "100%" if ec else "FAIL"
        mark = "✓" if ec else "✗"
        print(f"    {cat:12s} J={J} K={K} ec={ec}: {cnt:>8} {mark}")

    phase_ec_test.clear()

# PART 2: n=4 detailed — WHY does entry conflict always hold?
print(f"\n{'='*70}")
print("n=4 DETAILED: WHAT FORCES ENTRY CONFLICT AT EVERY TERNARY?")
print("=" * 70)

n, ms = 4, [2,3,2,3]
words = enumerate_mover_words(ms, n, 14)
sandwiched = [1, 3]
total = 0
ec_mechanism = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)

    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        phase_jk = []
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            phase_jk.append((J, K))

        # What forces EC?
        has_toggle = any((J >= 2 and K == 0) or (J == 0 and K >= 2) for J, K in phase_jk)
        has_both_even = any(J % 2 == 0 and K % 2 == 0 and J + K > 0 for J, K in phase_jk)
        has_toggle_classic = any((J >= 3 and K == 0) or (J == 0 and K >= 3) for J, K in phase_jk)

        if has_toggle:
            ec_mechanism[('gen_toggle', tuple(phase_jk))] += 1
        elif has_both_even:
            ec_mechanism[('both_even', tuple(phase_jk))] += 1
        else:
            ec_mechanism[('other', tuple(phase_jk))] += 1

print(f"Total: {total}")
print(f"\nEntry conflict mechanisms at n=4:")
mech_totals = Counter()
for (mech, jk), cnt in sorted(ec_mechanism.items()):
    mech_totals[mech] += cnt
for mech, cnt in sorted(mech_totals.items()):
    print(f"  {mech}: {cnt}")

print(f"\nDetailed (J,K) patterns:")
for (mech, jk), cnt in sorted(ec_mechanism.items(), key=lambda x: -x[1])[:20]:
    print(f"  {mech}: {jk} × {cnt}")

# PART 3: For escape, what (J,K) patterns would be needed?
# If all phases anti-diagonal and no (≥2,0)/(0,≥2): what remains?
print(f"\n{'='*70}")
print("ESCAPE-COMPATIBLE (J,K) PATTERNS")
print("=" * 70)

print("\nFor T to escape ALL mechanisms at all 3 phases:")
print("  No phase has J=0,K≥2 or J≥2,K=0 (gen Toggle-FR)")
print("  No phase has J,K both even > 0 (Both-Even FR)")
print("  → All phases anti-diagonal AND no (≥2,0)/(0,≥2)")
print("\nEscape-safe phase types:")
print("  (1,0): J=1, K=0 — safe (only 1 bL firing, 0 bR)")
print("  (0,1): J=0, K=1 — safe")
print("  (1,1): J odd≥1, K odd≥1 — safe")
print("  (odd≥3, even≥2): safe (both nonzero, not both even)")
print("  (even≥2, odd≥3): safe")
print("  (odd≥1, odd≥1): safe")
print("\nMinimum total fire counts for full escape:")
print("  Phase parities = perm of {(1,0),(0,1),(1,1)}")
print("  (1,0) phase: J=1,K=0 OR J odd,K even≥2 → min J+K = 1")
print("  (0,1) phase: J=0,K=1 OR J even≥2,K odd → min J+K = 1")
print("  (1,1) phase: J odd≥1,K odd≥1 → min J+K = 2")
print("  Total min J+K = 4. But J,K must each be even≥2:")
print("  J = J_A + J_B + J_C ≥ 2, K = K_A + K_B + K_C ≥ 2")
print("  Minimum: (1,0),(0,1),(1,1) → J=1+0+1=2, K=0+1+1=2 ✓")
