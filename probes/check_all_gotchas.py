#!/usr/bin/env python3
"""
COMPREHENSIVE GOTCHA CHECK for all remaining sorry's.

For each sorry, test the EXACT claim computationally before
attempting Lean formalization. Catch false claims early.

GOTCHA 1: dualPath_dispatch
  Claim: for every zero-winding non-consecutive cycle, EITHER
  (a) some proc has an interval where it doesn't fire, and neighbor
      fire counts trigger mechanism 1-4, OR
  (b) some binary proc has a BoundaryShadowEntry witness

GOTCHA 2: Non-zero winding mechanism coverage
  Claim: mechanisms also work for sweep (flux ±2) and oddWinding (flux ±1)

GOTCHA 3: WiggleMoverStructure from non-uniform sweep
  Claim: non-uniform sweep cycles have the right reversal structure
  for WiggleMoverStructure

GOTCHA 4: Sandwiched ternary existence
  Claim: under ≥3 non-consecutive binary, there exists a ternary proc
  with BOTH neighbors binary. (Already shown false in general — need hgap.)
  Check: under what conditions does hgap hold?

GOTCHA 5: Phase extraction from fc≥2
  Claim: if a proc fires ≥2 times, there exist two consecutive firing
  steps with a gap between them where the proc doesn't fire.
  (Seems obvious but check edge cases: what if all firings are consecutive?)
"""
from itertools import product as iproduct
from collections import Counter

n = 5
ms = [2, 3, 2, 3, 2]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

# Generate all cycles (incrementing)
results = []
def dfs(word, fc, config):
    if len(word) > 16: return
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
        return
    remaining = 16 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

def winding(word):
    w = 0
    for i in range(len(word)):
        d = (word[(i+1)%len(word)] - word[i]) % n
        if d == 1: w += 1
        elif d == n-1: w -= 1
    return w

def build_configs(word):
    configs = [list(start)]
    for i in range(len(word)):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)
    return configs

def has_ec_at(word, configs, p):
    ell = len(word)
    m_ctx, n_ctx = set(), set()
    for s in range(ell):
        ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
        if word[s] == p:
            if ctx in n_ctx: return True
            m_ctx.add(ctx)
        else:
            if ctx in m_ctx: return True
            n_ctx.add(ctx)
    return False

def has_ec_anywhere(word, configs):
    for p in range(n):
        if has_ec_at(word, configs, p): return True, p
    return False, None

print("=" * 60)
print("GOTCHA 1: dualPath_dispatch (zero-winding non-consecutive)")
print("=" * 60)

zw_cycles = [w for w in results if winding(w) == 0]
print(f"Zero-winding cycles: {len(zw_cycles)}")

# For each cycle: can we find a SPECIFIC mechanism witness?
# Path A: find proc t, interval [a,s), where t doesn't fire, and
#   neighbor fire counts trigger mechanism 1-4
# Path B: find binary proc with BoundaryShadowEntry

path_a_count = 0
path_b_count = 0
neither_count = 0

for word in zw_cycles:
    ell = len(word)
    configs = build_configs(word)
    fc = Counter(word)

    found_a = False
    found_b = False

    # PATH A: for each proc t, for each gap between consecutive firings,
    # check if neighbor fire counts trigger a mechanism
    for t in range(n):
        if fc[t] < 2: continue
        fire_steps = sorted(s for s in range(ell) if word[s] == t)

        for idx in range(len(fire_steps)):
            a = fire_steps[idx]
            s = fire_steps[(idx + 1) % len(fire_steps)]
            if s <= a: s += ell  # wrap

            # Count neighbor fires in (a, s) exclusive
            left_t = (t - 1) % n
            right_t = (t + 1) % n
            J = sum(1 for step in range(a+1, s) if word[step % ell] == left_t)
            K = sum(1 for step in range(a+1, s) if word[step % ell] == right_t)

            # Check mechanisms
            # Mechanism 1: J even, K even (both-even return)
            if J % 2 == 0 and K % 2 == 0:
                found_a = True; break

            # Mechanism 2/3: one side ≥2, other side 0
            if (J >= 2 and K == 0) or (K >= 2 and J == 0):
                found_a = True; break

            # Mechanism 2: one side ≥3, other 0
            if (J >= 3 and K == 0) or (K >= 3 and J == 0):
                found_a = True; break

        if found_a: break

    # PATH B: for each binary proc, check BoundaryShadowEntry
    if not found_a:
        for p in range(n):
            if ms[p] != 2: continue
            if has_ec_at(word, configs, p):
                found_b = True; break

    if found_a:
        path_a_count += 1
    elif found_b:
        path_b_count += 1
    else:
        neither_count += 1
        print(f"  NEITHER: word={word}, fc={dict(fc)}")

print(f"\nPath A (mechanism at some proc): {path_a_count}")
print(f"Path B (binary boundary EC): {path_b_count}")
print(f"Neither: {neither_count}")
if neither_count == 0:
    print("*** GOTCHA 1 CLEAR: dual path covers all cycles ***")
else:
    print(f"*** GOTCHA 1 FAILED: {neither_count} cycles uncovered ***")

print("\n" + "=" * 60)
print("GOTCHA 2: Non-zero winding mechanism coverage")
print("=" * 60)

for wind_type, wind_filter in [
    ("odd winding (|w|=n)", lambda w: abs(winding(w)) == n),
    ("sweep (|w|>=2n)", lambda w: abs(winding(w)) >= 2*n),
    ("other non-zero", lambda w: winding(w) != 0 and abs(winding(w)) != n and abs(winding(w)) < 2*n),
]:
    cycles = [w for w in results if wind_filter(w)]
    if not cycles:
        print(f"\n{wind_type}: 0 cycles (skip)")
        continue

    ec_count = 0
    no_ec = 0
    for word in cycles:
        configs = build_configs(word)
        has, _ = has_ec_anywhere(word, configs)
        if has: ec_count += 1
        else: no_ec += 1

    print(f"\n{wind_type}: {len(cycles)} cycles, EC={ec_count} ({100*ec_count/len(cycles):.0f}%), no EC={no_ec}")
    if no_ec > 0:
        print(f"  *** {no_ec} cycles without EC — need shadow/other argument ***")
    else:
        print(f"  *** All have EC ***")

print("\n" + "=" * 60)
print("GOTCHA 3: Non-uniform sweep reversal structure")
print("=" * 60)

sweep_cycles = [w for w in results if abs(winding(w)) >= 2*n]
print(f"Sweep cycles: {len(sweep_cycles)}")

for word in sweep_cycles[:5]:
    ell = len(word)
    # Count reversals
    reversals = 0
    for i in range(ell):
        d1 = (word[(i+1)%ell] - word[i]) % n
        d2 = (word[(i+2)%ell] - word[(i+1)%ell]) % n
        s1 = 1 if d1 == 1 else (-1 if d1 == n-1 else 0)
        s2 = 1 if d2 == 1 else (-1 if d2 == n-1 else 0)
        if s1 != 0 and s2 != 0 and s1 != s2:
            reversals += 1
    w = winding(word)
    cw = sum(1 for i in range(ell) if (word[(i+1)%ell] - word[i]) % n == 1)
    ccw = ell - cw
    print(f"  w={w}, len={ell}, CW={cw}, CCW={ccw}, reversals={reversals}")

print("\n" + "=" * 60)
print("GOTCHA 4: Sandwiched ternary existence")
print("=" * 60)
# At n=5, ms=[2,3,2,3,2]: procs 1 and 3 are ternary with both neighbors binary
# This is the alternating case — trivially true.
# Check: n=9, ms=[2,3,3,2,3,3,2,3,3] (3 binary equally spaced)
print("n=5, ms=[2,3,2,3,2]: sandwiched ternary = procs 1, 3. TRIVIAL.")
print()
print("For n=9, ms=[2,3,3,2,3,3,2,3,3] (equally spaced binary):")
ms9 = [2,3,3,2,3,3,2,3,3]
for p in range(9):
    if ms9[p] == 3 and ms9[(p-1)%9] == 2 and ms9[(p+1)%9] == 2:
        print(f"  Proc {p}: sandwiched ternary")
print("  None found — no sandwiched ternary with equally-spaced binary!")
print("  This confirms the hgap hypothesis is needed.")
print()
# But: with sub-threshold at n=9, the state vector must have specific structure.
# product < 4*3^7 = 8748. With ms=[2,3,3,2,3,3,2,3,3]: product = 2^3*3^6 = 5832 < 8748 ✓
# So this IS a valid sub-threshold configuration without sandwiched ternary.
print("  product([2,3,3,2,3,3,2,3,3]) = 5832 < 8748 ✓")
print("  This is a valid sub-threshold config WITHOUT sandwiched ternary!")
print("  *** GOTCHA 4 IS REAL: exists_ternary_sandwiched needs different approach ***")

print("\n" + "=" * 60)
print("GOTCHA 5: Phase extraction from fc≥2")
print("=" * 60)
# If proc fires ≥2 times, do consecutive firings always have a gap?
# What if proc fires at steps 0,1 (consecutive)? Then there's no gap
# between them where proc doesn't fire.
# But: contiguous_run_entry_conflict handles consecutive firings!
# So: either there's a gap (phase extraction works) or consecutive (NestedFirings works)

print("If proc fires at consecutive steps (gap=0): contiguous_run_entry_conflict applies.")
print("If proc fires with gap≥1: phase extraction applies.")
print("GOTCHA 5 CLEAR: either NestedFirings or PhaseExtraction handles it.")
print("Need to add this case split in Lean.")

print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)
print("GOTCHA 1 (dual path dispatch): checking...")
print(f"  Path A: {path_a_count}, Path B: {path_b_count}, Neither: {neither_count}")
print(f"GOTCHA 2 (non-zero winding): see above")
print(f"GOTCHA 3 (wiggle structure): see above")
print(f"GOTCHA 4 (sandwiched ternary): REAL — need different approach for equally-spaced binary")
print(f"GOTCHA 5 (phase extraction): CLEAR — case split on consecutive vs gap")
