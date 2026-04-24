"""
The REAL proof approach.

After careful analysis, here's what I know:

1. At n=5, the CE walks exist as ABSTRACT walks but NO valid system realizes them.
2. The CE walks have oscillation patterns (binary-ternary back-and-forth).
3. The provider (binary active, even >= 2, silent other side) fails for these walks.

The question: does the provider always exist in ACTUAL good cycles at n >= 9?

Key insight: the existing proof in CaseObstructionsCore.lean ALREADY handles this!
The proof flow is:

  a) zeroWinding_no_fireCount_ge3: assumes fc >= 3 at some proc q
  b) This calls exists_zw_oneSided_provider which calls passthrough_excursion_oneSided
  c) passthrough_excursion_oneSided first proves: ∃ binary b with fc(b) = 2
     This is the "exists_passthrough" sorry.
  d) Then from fc(b) = 2, constructs the provider.

The fc(b) = 2 claim uses: if all binary have fc >= 4, pigeonhole gives EC.

THIS is actually correct and SUFFICIENT. The issue was that the user asked me
to prove the provider exists WITHOUT assuming fc(b) = 2. But actually, proving
fc(b) = 2 is the RIGHT approach — it just needs the pigeonhole argument.

BUT: the user explicitly said "Previous attempts assumed: ∃ binary b with fc(b) = 2.
This was used for the passthrough argument (fc=2 → 2 firings → one-sided excursion).
But proving fc=2 exists is hard when all binary could have fc≥4."

So the user wants an approach that DOESN'T rely on proving fc(b) = 2.

My analysis shows: without fc(b) = 2, the binary provider can fail (at the abstract
walk level). But the generalized provider (ternary active with multiple-of-3 fires)
always exists.

The question is: can we use the generalized provider to get entry conflict?

For the generalized provider:
  t fires at s, nonmover at a, doesn't fire in [a, s)
  One neighbor silent (fires 0 in [a, s))
  Other neighbor p fires k * m_p times in [a, s) (k >= 1)

For entry conflict, we need:
  config(s)[left(t)] = config(a)[left(t)]
  config(s)[t] = config(a)[t]           (automatic: t doesn't fire)
  config(s)[right(t)] = config(a)[right(t)]

For the silent side: automatic (neighbor doesn't fire, value preserved).
For the active side: value returns iff the proc cycles through all states k times.
  Binary (m=2): fires 2k times. Value toggles 2k times → returns. TRUE always.
  Ternary (m=3): fires 3k times. Value MAY cycle 0→1→2→0 (k times) → returns.
    But it could also do 0→1→0→1→0→1 (6 fires but value = 1 after 5 fires, then 0).
    Wait, that's 6 = 2*3 fires. If the transition alternates: 0→1, 1→0, 0→1, ...,
    after 6 fires: 0→1→0→1→0→1→0. Returns! Hmm, always returns?

    Actually: a proc with m states that fires m*k times. Each firing is a
    permutation of Z_m (since the new value ≠ old value in a good cycle — actually
    no, in a good cycle the transition CHANGES the state, so f(L,S,R) ≠ S, meaning
    each firing changes the state). But the transition depends on context (L, S, R),
    so different firings can apply different permutations.

    After m*k firings, the composition of permutations may or may not be the identity.

    HOWEVER: in a good cycle, each firing changes S to some other value in Z_m.
    This is a sequence of values: v_0, v_1, ..., v_{mk}. Each v_i ≠ v_{i+1}.
    The walk through Z_m visits m*k+1 values (with v_0 = v_{mk} if return).

    For binary (m=2): values alternate 0,1,0,1,... After 2k firings (even),
    v_{2k} = v_0. ALWAYS returns.

    For ternary (m=3): not guaranteed. Example:
    0 → 1 → 0 → 2 → 1 → 2 → ? After 6 fires: 0,1,0,2,1,2,? We need v_6.
    Each step changes, so: 0→1→0→2→1→2→0 (returns) or 0→1→0→2→1→2→1 (doesn't).
    But wait, each firing must change: v_5 = 2, v_6 ≠ 2, so v_6 ∈ {0, 1}.
    If v_6 = 0: returns.
    If v_6 = 1: doesn't return.

    So for ternary, returning is NOT guaranteed after 3k firings.

Therefore, the GENERALIZED provider with ternary active side does NOT guarantee
entry conflict. The binary provider is needed.

NEW APPROACH: Prove fc(b) = 2 for some binary b via a DIFFERENT argument.

Observation: At the walk level, ALL binary procs have fc = 2 in the CE walks.
(The fc > 2 always occurs at ternary procs.) Is this true in general?

Claim: In a ZW walk on Z_n with cw > 0 and >= 3 non-consecutive binary,
if some proc has fc >= 3, then some BINARY proc has fc = 2.

This would be enough! If this is true, we don't need the pigeonhole argument.
The fc=2 binary automatically provides the passthrough and the provider.

Let me check computationally.
"""
import sys
sys.path.insert(0, './claude')


def check_binary_fc2_always_exists():
    """Check: in valid walks with some fc >= 3, does some binary always have fc = 2?"""
    n = 5
    ms = [2, 3, 2, 3, 2]
    binary_procs = [i for i in range(n) if ms[i] == 2]

    total = 0
    has_binary_fc2 = 0
    no_binary_fc2 = []

    for L in range(11, 17):
        count = 0
        count_yes = 0

        def gen(word):
            nonlocal count, count_yes
            if len(word) == L:
                disp = 0
                cw = 0
                for i in range(L):
                    nxt = word[(i + 1) % L]
                    diff = (nxt - word[i]) % n
                    if diff == 1:
                        cw += 1
                        disp += 1
                    elif diff == n - 1:
                        disp -= 1
                if disp != 0 or cw == 0:
                    return
                fc = [0] * n
                for m in word:
                    fc[m] += 1
                if any(f < 2 for f in fc):
                    return
                if max(fc) < 3:
                    return
                touched = set()
                for m in word:
                    touched.add(m)
                    touched.add((m-1)%n)
                    touched.add((m+1)%n)
                if len(touched) < n:
                    return

                count += 1
                binary_fcs = [fc[b] for b in binary_procs]
                if 2 in binary_fcs:
                    count_yes += 1
                else:
                    if len(no_binary_fc2) < 5:
                        no_binary_fc2.append((L, list(word), list(fc)))
                return

            last = word[-1]
            for nxt in [(last - 1) % n, last, (last + 1) % n]:
                word.append(nxt)
                gen(word)
                word.pop()

        for start in range(n):
            gen([start])

        total += count
        has_binary_fc2 += count_yes
        if count > 0:
            print(f"  L={L}: {count} valid, {count_yes} with binary fc=2 ({count - count_yes} without)")

    print(f"\nTOTAL: {total} valid, {has_binary_fc2} with binary fc=2")
    if no_binary_fc2:
        print(f"\nCounter-examples (no binary fc=2):")
        for L, w, fc in no_binary_fc2:
            print(f"  L={L}: {w}, fc={fc}")
            bfc = [fc[b] for b in binary_procs]
            print(f"    Binary fcs: {bfc}")
    else:
        print(f"ALL have some binary with fc=2!")

    return len(no_binary_fc2) == 0


def check_binary_fc2_extended():
    """Check at n=6,7 too."""
    configs = [
        (6, [2, 3, 2, 3, 2, 3]),
        (6, [2, 3, 3, 2, 3, 2]),
        (7, [2, 3, 2, 3, 2, 3, 3]),
    ]

    for n, ms in configs:
        binary_procs = [i for i in range(n) if ms[i] == 2]
        has3 = len(binary_procs) >= 3
        non_consec = True
        for i in range(n):
            if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
                non_consec = False
        if not has3 or not non_consec:
            continue

        print(f"\nn={n}, ms={ms}, binary={binary_procs}")
        total = 0
        has_fc2 = 0

        for L in range(2*n+1, 2*n+4):
            def gen(word):
                nonlocal total, has_fc2
                if len(word) == L:
                    disp = 0
                    cw = 0
                    for i in range(L):
                        nxt = word[(i+1)%L]
                        diff = (nxt - word[i]) % n
                        if diff == 1:
                            cw += 1
                            disp += 1
                        elif diff == n - 1:
                            disp -= 1
                    if disp != 0 or cw == 0:
                        return
                    fc = [0] * n
                    for m in word:
                        fc[m] += 1
                    if any(f < 2 for f in fc):
                        return
                    if max(fc) < 3:
                        return
                    touched = set()
                    for m in word:
                        touched.add(m)
                        touched.add((m-1)%n)
                        touched.add((m+1)%n)
                    if len(touched) < n:
                        return
                    total += 1
                    if any(fc[b] == 2 for b in binary_procs):
                        has_fc2 += 1
                    return
                last = word[-1]
                for nxt in [(last-1)%n, last, (last+1)%n]:
                    word.append(nxt)
                    gen(word)
                    word.pop()

            for start in range(n):
                gen([start])

        print(f"  Total: {total}, with binary fc=2: {has_fc2}, without: {total - has_fc2}")
        if has_fc2 < total:
            print(f"  COUNTER-EXAMPLES EXIST")
        else:
            print(f"  ALL have binary fc=2")


if __name__ == "__main__":
    print("=== Check: some binary always has fc=2 in ZW walks ===\n")
    print("n=5:")
    result = check_binary_fc2_always_exists()

    if result:
        print("\n\nExtending to n=6,7:")
        check_binary_fc2_extended()
