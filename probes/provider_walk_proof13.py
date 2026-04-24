"""
Fast check: does some binary always have fc=2 in ZW walks with some fc >= 3?

Only check L = 2n+1 (minimum L with some fc >= 3).
At L = 2n+1 with all fc >= 2 and sum = 2n+1, exactly one proc has fc = 3.
"""
import sys
sys.path.insert(0, './claude')


def fast_check_n5():
    n = 5
    ms = [2, 3, 2, 3, 2]
    binary = {0, 2, 4}
    L = 2 * n + 1  # = 11

    total = 0
    all_binary_fc2 = 0
    some_binary_fc_ge4 = 0

    def gen(word):
        nonlocal total, all_binary_fc2, some_binary_fc_ge4
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

            total += 1
            bfc = [fc[b] for b in binary]
            if all(f == 2 for f in bfc):
                all_binary_fc2 += 1
            if any(f >= 4 for f in bfc):
                some_binary_fc_ge4 += 1
            return

        last = word[-1]
        for nxt in [(last-1)%n, last, (last+1)%n]:
            word.append(nxt)
            gen(word)
            word.pop()

    for start in range(n):
        gen([start])

    print(f"n={n}, L={L}: {total} valid walks")
    print(f"  All binary fc=2: {all_binary_fc2}")
    print(f"  Some binary fc>=4: {some_binary_fc_ge4}")
    print(f"  Some binary fc=3 (odd): {total - all_binary_fc2 - some_binary_fc_ge4}")

    # At L = 2n+1 = 11: sum fc = 11, all fc >= 2, exactly one fc = 3.
    # Binary fc is always even (binary parity). So binary fc in {2, 4, 6, ...}.
    # If fc(b) = 3 for a binary b, that contradicts binary parity.
    # Therefore the fc = 3 proc must be TERNARY.
    # And all binary procs have fc = 2.
    print(f"\n  At L=2n+1: fc=3 proc must be TERNARY (binary fc is even).")
    print(f"  Therefore ALL binary have fc=2.")

    # Now check: does the binary provider exist for these walks?
    total2 = 0
    provider_count = 0

    def gen2(word):
        nonlocal total2, provider_count
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

            total2 += 1

            # Check provider
            fire_steps = {}
            for p in range(n):
                fire_steps[p] = []
            for i, m in enumerate(word):
                fire_steps[m].append(i)

            found = False
            for t in range(n):
                if found:
                    break
                fsteps = fire_steps[t]
                for s in fsteps:
                    if found:
                        break
                    prev_fire = -1
                    for k in range(s - 1, -1, -1):
                        if word[k] == t:
                            prev_fire = k
                            break

                    left_t = (t - 1) % n
                    right_t = (t + 1) % n
                    left_acc = 0
                    right_acc = 0

                    for a in range(s - 1, prev_fire, -1):
                        if word[a] == t:
                            continue
                        if word[a] == left_t:
                            left_acc += 1
                        elif word[a] == right_t:
                            right_acc += 1
                        lf = left_acc
                        rf = right_acc

                        if lf == 0 and ms[right_t] == 2 and rf >= 2 and rf % 2 == 0:
                            found = True
                            break
                        if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                            found = True
                            break

            if found:
                provider_count += 1
            return

        last = word[-1]
        for nxt in [(last-1)%n, last, (last+1)%n]:
            word.append(nxt)
            gen2(word)
            word.pop()

    for start in range(n):
        gen2([start])

    print(f"\n  Provider check at L={L}: {total2} valid, {provider_count} with provider")


def analysis():
    """Key insight: binary fire count is ALWAYS EVEN.

    In a good cycle, a binary proc (m=2) fires. Each firing changes its state
    (0->1 or 1->0). After an even number of firings, the value returns to the
    original. Since the cycle is CLOSED (returns to starting config), the total
    fire count of each binary proc is even.

    Therefore: with sum fc = L and all binary fc even and >= 2:
    - L = 2n+1 (odd) → at least one ternary proc has odd fc
    - L = 2n+2 (even) → all fc could be 2 (sum = 2n, contradiction with L=2n+2)
      So some fc >= 3, and if all binary have fc = 2, the excess goes to ternary.

    Actually, sum fc = L. With all binary fc >= 2 (even) and all ternary fc >= 2:
    sum = (sum binary fc) + (sum ternary fc) = L.

    If ALL binary have fc = 2: sum binary fc = 2B (B = number of binary procs).
    Then sum ternary fc = L - 2B.
    With (n - B) ternary procs each having fc >= 2: sum ternary fc >= 2(n-B).
    So L - 2B >= 2(n-B), giving L >= 2n. Since L >= 2n+1 (some fc >= 3), we need
    at least one ternary with fc >= 3.

    If SOME binary b has fc >= 4: sum binary fc >= 2(B-1) + 4 = 2B + 2.
    Then sum ternary fc = L - sum binary fc <= L - 2B - 2.
    But sum ternary fc >= 2(n-B), so L - 2B - 2 >= 2(n-B), giving L >= 2n+2.
    At L = 2n+1, this is impossible! So at L = 2n+1, ALL binary have fc = 2.

    GENERAL: At ANY L with L < 2n + 2B (where B = binary count),
    some binary must have fc = 2. Since B >= 3, this gives L < 2n+6.

    Wait, that's not quite right. Let me redo:
    If NO binary has fc = 2: all binary fc >= 4 (since binary fc is even and >= 2).
    Sum binary fc >= 4B.
    Sum ternary fc = L - sum binary fc <= L - 4B.
    Also sum ternary fc >= 2(n - B).
    So L - 4B >= 2(n - B), giving L >= 2n + 2B.
    With B >= 3: L >= 2n + 6.

    So: if L < 2n + 6, some binary has fc = 2 (WHEN all fc >= 2 and some >= 3).
    At n >= 9: 2n + 6 = 24 for n=9.

    For general L: we need L < 2n + 6 to guarantee binary fc = 2.
    But L could be larger. In a good cycle, L = product of state counts?
    No, L is the cycle LENGTH (number of good configs in the cycle).
    L <= total configs = product. But L could be much larger than 2n.

    HOWEVER: the ZW constraint limits L. In a ZW cycle, CL = 2*cw.
    With all fc >= 2: CL >= 2n. If CL = 2n: all fc = 2 (no fc >= 3).
    If some fc >= 3: CL >= 2n + 1.

    But there's no upper bound on CL from just ZW + fc >= 2. CL could be
    much larger than 2n + 6 if some procs fire many times.

    So the counting argument gives: if CL < 2n + 2B (B >= 3), then some binary
    has fc = 2. For CL >= 2n + 2B, we need a different argument.

    QUESTION: Can CL >= 2n + 6 occur in a ZW good cycle with sub-threshold
    product and >= 3 non-consecutive binary at n >= 9?

    The answer depends on the specific system. But the THEOREM we're proving
    says some fc >= 3. From the LEAN code, the assumption is:
    - fc >= 2 for all
    - some fc >= 3
    - ZW, cw > 0, no safe proc, sub-threshold, >= 3 binary non-consec, n >= 9

    CL = sum fc = 2n + (extra firings). With fc >= 3 at one proc: CL >= 2n+1.
    With multiple procs having fc >= 3: CL could be much larger.

    BUT: looking at the LEAN code again, the theorem zeroWinding_no_fireCount_ge3
    PROVES False from the assumption that some fc >= 3. So it's a proof by
    contradiction. In the contradiction branch, CL >= 2n+1. And the claim is:
    this situation is IMPOSSIBLE (leads to entry conflict).

    The approach in CaseObstructionsCore.lean:
    1. If some binary has fc = 2 → passthrough → provider → EC → False ✓
    2. If all binary have fc >= 4 → pigeonhole at the binary → EC → False ✓

    So the proof SPLITS into two cases. Case 1 doesn't need any new argument.
    Case 2 (all binary fc >= 4) needs the pigeonhole argument.

    The pigeonhole for case 2: binary b fires >= 4 times. Each firing changes
    b's state (0 ↔ 1). After >= 4 firings, b has been in state 0 at least twice
    as mover. At those two mover steps, b's context is (L, 0, R). With the same
    L and R, we'd have entry conflict.

    The number of distinct (L, R) pairs = m_{left(b)} * m_{right(b)}.
    With non-consecutive binary: left(b) and right(b) are both ternary (m >= 3).
    So (L, R) pairs >= 3 * 3 = 9.

    With fc(b) = 4: b fires 4 times, 2 with val=0, 2 with val=1.
    Among the 2 mover steps with val=0: (L, R) can differ. With 9+ possibilities,
    2 mover steps can have different (L, R). So pigeonhole doesn't work directly.

    BUT: we also have NONMOVER steps at b. At every step where b is nonmover,
    b has some context (L, val, R). If any nonmover context matches a mover context,
    we get entry conflict.

    Total mover steps at b: 4 (fc = 4).
    Total nonmover steps at b: CL - 4.
    Total contexts at mover steps: 4, each is (L, val, R).
    Total contexts at nonmover steps: CL - 4, each is (L, val, R).

    For entry conflict: need (L, val, R) match between mover and nonmover.

    With val ∈ {0, 1}, L ∈ Z_{m_L}, R ∈ Z_{m_R}: total triples = 2 * m_L * m_R.
    In a good cycle, all configs are distinct, so all CL triples are distinct.
    Mover triples: 4 distinct values. Nonmover triples: CL - 4 distinct values.
    Both sets ⊂ {0,...,2*m_L*m_R - 1}.

    If 4 + (CL - 4) > 2 * m_L * m_R: pigeonhole gives a match!
    I.e., CL > 2 * m_L * m_R.

    With m_L, m_R >= 3 (ternary neighbors): 2 * m_L * m_R >= 18.
    CL = sum fc >= 2n + 2 (all binary fc >= 4 adds 2 per binary above fc=2;
    with B >= 3 binary: sum binary fc >= 12, sum ternary fc >= 2(n-3),
    CL >= 12 + 2(n-3) = 2n + 6).

    For n >= 9: CL >= 24. And 2 * m_L * m_R depends on neighbors of b.
    With m_L = m_R = 3: 2*9 = 18. CL >= 24 > 18 → pigeonhole!

    WAIT. The pigeonhole here is on the (L, val, R) context at proc b.
    If CL > 2 * m_L * m_R, the total number of steps (CL) exceeds the total
    number of distinct contexts (2 * m_L * m_R). Since all CL contexts are
    distinct (good cycle), this is a contradiction unless CL <= 2 * m_L * m_R.

    But I said CL >= 24 and 2*m_L*m_R = 18. 24 > 18, but this is NOT about
    the contexts at a SINGLE proc. In a good cycle, the CONFIGS are distinct
    (globally, all n values together), not the local triples.

    Two configs can agree on (L, b, R) but differ elsewhere. So CL can exceed
    2 * m_L * m_R without contradiction.

    Hmm, so the pigeonhole on local contexts doesn't directly work.

    BUT: entry conflict requires matching (L, b, R) at a mover and nonmover step.
    If the 4 mover triples and (CL-4) nonmover triples are all DISTINCT from each
    other, then we need 4 + (CL-4) = CL distinct triples, and there are
    2 * m_L * m_R available. So CL <= 2 * m_L * m_R if no entry conflict.

    With all binary fc >= 4 and n >= 9: CL >= 2n + 6 = 24 (for n=9).
    2 * m_L * m_R for the binary b: if m_L = m_R = 3, then 18. CL >= 24 > 18.
    Contradiction! So CL > 2 * m_L * m_R → entry conflict at b.

    Wait, is this right? In a good cycle, all GLOBAL configs are distinct.
    At proc b, the local triple (L, b, R) changes each step. But two different
    global configs could have the same (L, b, R) triple. The total number of
    distinct (L, b, R) triples is at most CL (each step has a unique global config,
    hence a unique local triple? NO - different global configs can have the same
    local triple at b).

    Actually, in a good cycle, configs are globally distinct. But the local
    triple at b can repeat. The entry conflict condition is: same local triple
    at b, one step where b is mover, one where b is nonmover.

    So the question is: among CL steps, how many distinct (L, b_val, R) triples?
    At most 2 * m_L * m_R. If CL > 2 * m_L * m_R, some triple appears at >= 2 steps.
    By pigeonhole, if the repeat involves one mover and one nonmover step, we're done.
    But all repeats could be mover-mover or nonmover-nonmover.

    With 4 mover steps and CL - 4 nonmover steps, and 2*m_L*m_R total triples:
    If CL > 2*m_L*m_R, then by inclusion-exclusion... hmm, this needs care.

    Actually, let me think more carefully. There are 4 mover triples (from b's
    4 firing steps) and CL-4 nonmover triples (from b's nonmover steps). If these
    4 + (CL-4) = CL values are all within {0,...,2*m_L*m_R - 1}, and some triple
    appears in BOTH the mover set and nonmover set → entry conflict.

    If no entry conflict: the mover triples and nonmover triples are DISJOINT sets.
    So |mover set| + |nonmover set| <= 2*m_L*m_R.
    |mover set| <= 4 (could be less if duplicates among movers).
    |nonmover set| <= CL - 4 (could be less if duplicates among nonmovers).

    This gives at most 4 + (CL-4) = CL values in a set of size 2*m_L*m_R.
    If CL > 2*m_L*m_R, the sets can't be disjoint (since the union has > 2*m_L*m_R
    entries, but there are only 2*m_L*m_R possible triples).

    No wait: the mover set has <= 4 DISTINCT triples (since there are 4 mover steps
    but some could coincide). Actually, in a good cycle, all configs are globally
    distinct, but local triples can repeat. However, two mover steps at b with
    the same local triple (L, b_val, R) IS an entry conflict... wait no. Entry
    conflict needs one mover and one nonmover. Two mover steps with same triple
    is a different thing.

    Two MOVER steps at b with same (L, b_val, R): both steps have b privileged,
    same context → same transition → same config after firing. But the configs
    BEFORE firing differ (globally distinct). After firing b, only b's value
    changes. So configs differ in some non-b position, but agree on (L, b, R)
    and on the new b value. This is fine, no contradiction.

    So mover triples CAN repeat (up to 4 mover steps could all have different
    contexts, or some could match).

    For the disjoint argument:
    - # distinct mover triples <= min(4, 2*m_L*m_R)
    - # distinct nonmover triples <= min(CL-4, 2*m_L*m_R)
    - If sets disjoint: # distinct mover + # distinct nonmover <= 2*m_L*m_R

    The issue: # distinct nonmover triples could be much less than CL-4.
    Many nonmover steps could share the same local triple.

    So the argument doesn't simply follow from CL > 2*m_L*m_R.

    Hmm. Let me think again.

    ALTERNATIVE: use the fact that binary fire count is even to get fc=2.
    """
    print("Binary fire count is always even (binary parity).")
    print("If all binary fc >= 4: sum binary fc >= 4 * B >= 12.")
    print("CL = sum fc >= 12 + 2(n-B) = 2n + 2B - 2*(n-B) = ... wait let me redo.")
    print()
    print("CL = sum binary fc + sum ternary fc")
    print("  >= 4B + 2(n-B) = 2n + 2B")
    print("With B >= 3: CL >= 2n + 6")
    print("For n >= 9: CL >= 24")
    print()
    print("But we need CL <= product < 4*3^(n-2) (sub-threshold).")
    print("At n=9: CL < 4*3^7 = 8748. So CL is bounded but can be large.")
    print()
    print("The direct pigeonhole on local triples doesn't work because")
    print("nonmover triples can repeat.")
    print()
    print("BUT: we can use a DIFFERENT pigeonhole based on binary parity.")
    print()
    print("With fc(b) >= 4 for binary b: b fires >= 4 times.")
    print("Since binary, val alternates: 0,1,0,1,...or 1,0,1,0,...")
    print("After 4 fires: val sequence is v,1-v,v,1-v. Two fires with val=v.")
    print("At these two fires, b is mover with same val=v.")
    print()
    print("Now: the two mover steps with same b_val=v have contexts (L1,v,R1) and (L2,v,R2).")
    print("If (L1,R1) = (L2,R2): entry conflict with any nonmover step with same triple.")
    print("Actually, that's a duplicate MOVER context, not mover-nonmover match.")
    print()
    print("For entry conflict: need mover context = nonmover context.")
    print("Mover: (L, v, R) with f(L,v,R) ≠ v (privileged).")
    print("Nonmover: (L, v, R) with f(L,v,R) = v (not privileged).")
    print("Same triple can't be both privileged and not → CONTRADICTION!")
    print("Wait, that means a local triple is EITHER mover or nonmover, not both!")
    print()
    print("THIS IS THE KEY: at proc b, a local triple (L, v, R) determines")
    print("whether b is privileged or not (based on f_b). So the same triple")
    print("always gives the same privilege status. Therefore:")
    print("  Mover set ∩ Nonmover set = ∅ (automatically!)")
    print()
    print("So: entry conflict at b requires same (L,v,R) appearing at both a mover")
    print("step and a nonmover step. But the transition function makes this impossible!")
    print("A given (L,v,R) either has f(L,v,R) ≠ v (always mover) or = v (always nonmover).")
    print()
    print("So the pigeonhole argument CANNOT produce entry conflict at a single proc.")
    print()
    print("CORRECTION: entry conflict is at proc t, where:")
    print("  Step k1: t is mover (f_t(L,S,R) ≠ S)")
    print("  Step k2: t is nonmover (f_t(L,S,R) = S)")
    print("  Same (L, S, R) at both steps → f_t(L,S,R) ≠ S AND f_t(L,S,R) = S → CONTRADICTION!")
    print()
    print("So entry conflict at ANY proc is impossible by definition?!")
    print("No, that can't be right. Let me re-read the definition.")


if __name__ == "__main__":
    fast_check_n5()
    print("\n\n=== Analysis ===")
    analysis()
