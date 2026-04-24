"""
Investigation part 10: Final analysis and closability assessment.

KEY QUESTION: Can zw_provider_ec be proved using existing Lean infrastructure?

The mechanism:
1. Under ZW + cw > 0 + fc >= 2 + some fc >= 3:
   Find binary b with fc = 2.
2. b has two consecutive fires at a1, a2.
3. Find non-mover step k where (L,S,R) matches a2.
4. The matching comes from: left(b) even fires (binary parity), right(b) even/zero fires,
   b zero fires — all in interval [k, a2).

The proof needs:
(A) Existence of binary b with fc = 2
(B) Finding the right k between b's consecutive fires

For (A): If all binary have fc >= 3, then sum_binary_fc >= 9 (3 binary × 3).
Sum_ternary_fc >= 2*(n-3). Total >= 9 + 2n - 6 = 2n + 3.
Since CL is even (ZW), CL >= 2n + 4.
But we need to show this leads to contradiction or just find one binary with fc=2.

Actually, we don't need ALL binary to have fc=2. We need at least ONE.
Can we prove this? At n=5, computationally no valid cycle has all binary fc >= 3.
But that might be specific to n=5.

Actually, let me re-read the sorry more carefully. The sorry says:
"Under ZW with cw > 0, fc >= 2 for all, some proc q with fc >= 3: show EC."

It does NOT say "find binary b with fc=2". That's the file comment's suggested
approach, but the actual theorem just needs to produce EC from these hypotheses.

So the real question: can we produce EC under these hypotheses using ANY method?

The hypotheses include hconv, hno_safe, hsub, h3bin — the full machinery is available.

APPROACH: Use the existing phase extraction + dispatch machinery.
1. Since fc >= 2 for all and some fc >= 3, total CL > 2n.
2. Find a ternary proc t with fc >= 2 (guaranteed).
3. Extract TernaryPhase at t.
4. If t has binary neighbors on both sides: use phase_dispatch_ec or palindromic_phase_ec_residual.
5. If not: need alternative.

For case 5, the question is: can we always find a ternary proc with B-T-B sandwich?
We showed earlier: NO, not always.

BUT: the hypotheses include hconv (converges), which implies the good cycle
comes from a converging system. This might impose additional constraints.

Actually, hconv is not relevant to the walk structure. The walk is determined
by the good cycle alone.

Alternative for case 5 (no B-T-B sandwich):
- Use the "passthrough" argument from the file comment
- The walk structure under ZW with excursion guarantees a binary proc b
  whose neighborhood has the right fire pattern
- This is a new argument, not directly available in existing infrastructure

VERDICT: zw_provider_ec likely needs NEW WORK. It cannot be trivially
routed through existing archive infrastructure because:
1. No B-T-B sandwich is guaranteed
2. The mechanism involves binary parity + walk excursion structure
3. The palindromic_step_pair_caseA helper is already in the file
   but the sorry is about EXISTENCE of the right b and k.

The proof sketch:
- Under ZW + cw > 0 + fc >= 3 at q:
  CL > 2n, so CL >= 2n + 2 (even).
- Each binary proc fires at least twice (fc >= 2).
- If binary b has fc = 2: b fires once CW, once CCW.
  The walk goes CW through b, continues, then returns CCW through b.
  Between b's two fires: there's an excursion of length CL - 2 > 2n - 2.
  In this excursion, left(b) and right(b) both participate.
  Since the walk must return to b, left(b) fires an equal number of CW and
  CCW steps near b...

Actually, let me try to verify: for every valid cycle, can we always use
palindromic_step_pair_caseA? That requires finding k2 with:
  - a1 < k2 < a2
  - left(b) doesn't fire in [k2, a2)
  - right(b) fires even times in [k2, a2)

Let me check this computationally for all valid cycles.
"""

import itertools

def fire_counts(word, n):
    fc = [0] * n
    for p in word: fc[p] += 1
    return fc

def winding_number(word, n):
    cw = 0; ccw = 0; L = len(word)
    for i in range(L):
        curr = word[i]; nxt = word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
        elif nxt == (curr - 1) % n: ccw += 1
        else: return None
    if (cw - ccw) % n != 0: return None
    return (cw - ccw) // n

def cw_count(word, n):
    cw = 0; L = len(word)
    for i in range(L):
        curr = word[i]; nxt = word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
    return cw

def enumerate_zw_words(n, cl):
    def dfs(word, pos):
        if len(word) == cl:
            last = word[-1]; first = word[0]
            if (first - last) % n == 1 or (last - first) % n == 1:
                w = winding_number(word, n)
                if w == 0 and cw_count(word, n) > 0:
                    yield tuple(word)
            return
        for nxt in [(pos + 1) % n, (pos - 1) % n]:
            word.append(nxt)
            yield from dfs(word, nxt)
            word.pop()
    seen = set()
    for start in range(n):
        for word in dfs([start], start):
            rotations = [word[i:] + word[:i] for i in range(cl)]
            canonical = min(rotations)
            if canonical not in seen:
                seen.add(canonical)
                yield canonical

n = 5
ms = (2, 2, 2, 3, 3)

print("Checking palindromic_step_pair_caseA applicability")
print("="*60)

total_cycles = 0
caseA_works = 0
caseA_fails = 0

for cl in [12, 14]:
    for word in enumerate_zw_words(n, cl):
        fc = fire_counts(word, n)
        if any(f < 2 for f in fc): continue
        if max(fc) < 3: continue

        L = len(word)

        # Find all valid cycles
        def check_cycles(step, configs, transitions):
            global total_cycles, caseA_works, caseA_fails

            if step == L:
                if configs[0] != configs[L]: return
                config_tuples = [tuple(c) for c in configs[:L]]
                if len(set(config_tuples)) != L: return

                total_cycles += 1

                # For each binary b with fc=2, check if caseA works
                found_caseA = False
                for b in range(n):
                    if ms[b] != 2 or fc[b] != 2: continue

                    fire_steps_b = [k for k in range(L) if word[k] == b]
                    a1, a2 = fire_steps_b[0], fire_steps_b[1]
                    left_b = (b - 1) % n
                    right_b = (b + 1) % n

                    # Check both pairs: (a1, a2) and (a2, a1 wrapping)
                    for start_fire, end_fire in [(a1, a2)]:
                        # Look for k2 in (start_fire, end_fire) where:
                        # - mover(k2) != b
                        # - left(b) doesn't fire in [k2, end_fire)
                        # - right(b) fires even times in [k2, end_fire)
                        for k2 in range(start_fire + 1, end_fire):
                            if word[k2] == b: continue  # shouldn't happen

                            # Count left(b) fires in [k2, end_fire)
                            left_fires = sum(1 for j in range(k2, end_fire) if word[j] == left_b)
                            # Count right(b) fires in [k2, end_fire)
                            right_fires = sum(1 for j in range(k2, end_fire) if word[j] == right_b)

                            if left_fires == 0 and right_fires % 2 == 0:
                                # Also need right(b) to be binary for parity argument
                                if ms[right_b] == 2:
                                    found_caseA = True
                                    break
                        if found_caseA: break

                    # Also check the wrapped interval
                    if not found_caseA:
                        # Wrapped: from a2 to a1 (going through 0)
                        for k2_raw in range(1, L - (a2 - a1)):
                            k2 = (a2 + k2_raw) % L
                            if word[k2] == b: continue

                            # Count fires in [k2, a1) wrapping
                            # This is trickier for wrapping intervals
                            left_fires = 0
                            right_fires = 0
                            j = k2
                            while j != a1:
                                if word[j] == left_b: left_fires += 1
                                if word[j] == right_b: right_fires += 1
                                j = (j + 1) % L

                            if left_fires == 0 and right_fires % 2 == 0 and ms[right_b] == 2:
                                found_caseA = True
                                break

                    if found_caseA: break

                if found_caseA:
                    caseA_works += 1
                else:
                    caseA_fails += 1
                    if caseA_fails <= 5:
                        print(f"  CaseA FAILS: word={word}, fc={fc}")
                        print(f"    start={tuple(configs[0])}")
                return

            p = word[step]
            c = configs[step]
            ctx = (c[(p-1) % n], c[p], c[(p+1) % n])
            key = (p, ctx[0], ctx[1], ctx[2])

            if key in transitions:
                new_val = transitions[key]
                if new_val == ctx[1]: return
                new_c = c[:]; new_c[p] = new_val
                configs.append(new_c)
                check_cycles(step + 1, configs, transitions)
                configs.pop()
            else:
                for new_val in range(ms[p]):
                    if new_val == ctx[1]: continue
                    new_c = c[:]; new_c[p] = new_val
                    configs.append(new_c)
                    new_trans = dict(transitions)
                    new_trans[key] = new_val
                    check_cycles(step + 1, configs, new_trans)
                    configs.pop()

        for start in itertools.product(*[range(m) for m in ms]):
            check_cycles(0, [list(start)], {})

print(f"\nTotal valid cycles: {total_cycles}")
print(f"CaseA works: {caseA_works}")
print(f"CaseA fails: {caseA_fails}")

if caseA_fails > 0:
    print("\nCaseA doesn't always work! Need alternative mechanism.")
else:
    print("\nCaseA works for ALL cycles! The proof can use palindromic_step_pair_caseA.")
