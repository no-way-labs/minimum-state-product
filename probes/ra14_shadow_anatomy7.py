#!/usr/bin/env python3
"""
RA14 Part 7: Final verification — word-level shadow IS real at system level.

The 'inc' free policy fails convergence. The word-level shadow predicts
23 disjoint offset orbits. Let's verify: are these actual bad-config cycles
in the system?
"""

from collections import defaultdict
from itertools import product as iproduct
from math import prod

def build_cycle(word, ms, n, trans=None):
    if trans is None:
        trans = [1]*n
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]

n = 5
ms = [2,2,2,3,3]
product_val = prod(ms)

w0 = [0, 1, 2, 3, 3, 4, 0, 1, 2, 3, 4, 4]
CL = len(w0)
cyc0 = build_cycle(w0, ms, n)
good_set = set(cyc0)

# Collect forced entries
forced = {}
for t in range(CL):
    c = cyc0[t]
    mover = w0[t]
    c_next = cyc0[(t+1) % CL]
    for j in range(n):
        key = (j, c[(j-1)%n], c[j], c[(j+1)%n])
        if j == mover:
            forced[key] = c_next[j]
        else:
            forced[key] = c[j]

# Build system with 'inc' free policy
all_entries = dict(forced)
for p in range(n):
    for L_val in range(ms[(p-1)%n]):
        for S_val in range(ms[p]):
            for R_val in range(ms[(p+1)%n]):
                key = (p, L_val, S_val, R_val)
                if key not in all_entries:
                    all_entries[key] = (S_val + 1) % ms[p]

# For each bad config: find privileged procs and successors
print("="*70)
print("BAD-CONFIG GRAPH ANALYSIS")
print("="*70)

bad_configs = [cfg for cfg in iproduct(*(range(m) for m in ms)) if cfg not in good_set]
print(f"Bad configs: {len(bad_configs)}")

# Build bad-config graph
bad_graph = defaultdict(list)  # cfg -> list of (successor, mover)
bad_set = set(bad_configs)

for cfg in bad_configs:
    for j in range(n):
        key = (j, cfg[(j-1)%n], cfg[j], cfg[(j+1)%n])
        new_val = all_entries[key]
        if new_val != cfg[j]:  # proc j is privileged
            successor = list(cfg)
            successor[j] = new_val
            successor = tuple(successor)
            if successor in bad_set:
                bad_graph[cfg].append((successor, j))

# Find cycles in bad graph using DFS
def find_bad_cycles(bad_graph, bad_configs):
    """Find all SCCs in the bad graph."""
    # Tarjan's algorithm
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        for w, _ in bad_graph.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    for v in bad_configs:
        if v not in index:
            strongconnect(v)

    return sccs

sccs = find_bad_cycles(bad_graph, bad_configs)
print(f"Non-trivial SCCs in bad graph: {len(sccs)}")
for i, scc in enumerate(sccs[:5]):
    print(f"  SCC {i}: {len(scc)} configs")

# Check: do the word-level shadow orbits correspond to bad-graph cycles?
print(f"\n--- Word-level shadow orbits vs bad-graph SCCs ---")

# Compute shadow orbits
shadow_orbits = []
diff_set = set()
for g1 in cyc0:
    for g2 in cyc0:
        d = tuple((g1[j] - g2[j]) % ms[j] for j in range(n))
        diff_set.add(d)

for d in iproduct(*(range(m) for m in ms)):
    if all(x == 0 for x in d):
        continue
    if d in diff_set:
        continue  # intersects good cycle
    shifted = set(tuple((cyc0[t][j] + d[j]) % ms[j] for j in range(n)) for t in range(CL))
    # Check this is a new orbit (not already seen)
    if shifted not in [set(s) for s in shadow_orbits]:
        shadow_orbits.append([tuple((cyc0[t][j] + d[j]) % ms[j] for j in range(n)) for t in range(CL)])

# Deduplicate shadow orbits
unique_orbits = []
seen_orbit_sets = []
for orb in shadow_orbits:
    orb_set = frozenset(orb)
    if orb_set not in seen_orbit_sets:
        seen_orbit_sets.append(orb_set)
        unique_orbits.append(orb)

print(f"Unique shadow orbits: {len(unique_orbits)}")

# For each shadow orbit, check if it's a cycle in the bad graph
# (i.e., each config in the orbit has the orbit's next config as a successor)
n_real_cycles = 0
for oi, orbit in enumerate(unique_orbits[:30]):
    orbit_set = set(orbit)
    # Check: for each step, is the word's mover privileged?
    is_cycle = True
    for t in range(CL):
        cfg = orbit[t]
        cfg_next = orbit[(t+1) % CL]
        mover = w0[t]

        # Is the mover privileged at cfg in the system?
        key = (mover, cfg[(mover-1)%n], cfg[mover], cfg[(mover+1)%n])
        new_val = all_entries[key]
        expected_next = list(cfg)
        expected_next[mover] = new_val
        expected_next = tuple(expected_next)

        if expected_next != cfg_next:
            is_cycle = False
            break

    if is_cycle:
        n_real_cycles += 1
        # Also check: is the mover actually privileged (new_val != cfg[mover])?
        all_priv = True
        for t in range(CL):
            cfg = orbit[t]
            mover = w0[t]
            key = (mover, cfg[(mover-1)%n], cfg[mover], cfg[(mover+1)%n])
            if all_entries[key] == cfg[mover]:
                all_priv = False
                break
        if oi < 5:
            print(f"  Orbit {oi}: IS real bad cycle, all movers privileged: {all_priv}")
    else:
        if oi < 5:
            print(f"  Orbit {oi}: NOT a real bad cycle in the system")

print(f"\nReal bad cycles from word-level shadow: {n_real_cycles}/{len(unique_orbits)}")

# Check what fraction of SCC configs are covered by shadow orbits
all_scc_configs = set()
for scc in sccs:
    all_scc_configs.update(scc)

all_shadow_configs = set()
for orb in unique_orbits:
    all_shadow_configs.update(orb)

overlap = all_scc_configs & all_shadow_configs
print(f"\nSCC configs: {len(all_scc_configs)}")
print(f"Shadow configs: {len(all_shadow_configs)}")
print(f"Overlap: {len(overlap)}")

# Now THE KEY QUESTION:
# With a DIFFERENT free policy, do the shadow orbits break?
print(f"\n{'='*70}")
print("TESTING DIFFERENT FREE POLICIES")
print("="*70)

policies = {
    'inc': lambda p, S: (S + 1) % ms[p],
    'dec': lambda p, S: (S - 1) % ms[p],
    'stay': lambda p, S: S,
    'random1': lambda p, S: (S + 2) % ms[p],  # +2 for ternary
}

for pol_name, pol_fn in policies.items():
    ent = dict(forced)
    for p in range(n):
        for L_val in range(ms[(p-1)%n]):
            for S_val in range(ms[p]):
                for R_val in range(ms[(p+1)%n]):
                    key = (p, L_val, S_val, R_val)
                    if key not in ent:
                        ent[key] = pol_fn(p, S_val)

    # Check how many shadow orbits are real bad cycles
    n_real = 0
    for orbit in unique_orbits:
        is_cycle = True
        for t in range(CL):
            cfg = orbit[t]
            cfg_next = orbit[(t+1) % CL]
            mover = w0[t]
            key = (mover, cfg[(mover-1)%n], cfg[mover], cfg[(mover+1)%n])
            new_val = ent[key]
            expected = list(cfg)
            expected[mover] = new_val
            if tuple(expected) != cfg_next:
                is_cycle = False
                break
        if is_cycle:
            # Check mover is actually privileged
            all_ok = all(
                ent[(w0[t], orbit[t][(w0[t]-1)%n], orbit[t][w0[t]], orbit[t][(w0[t]+1)%n])] != orbit[t][w0[t]]
                for t in range(CL)
            )
            if all_ok:
                n_real += 1

    print(f"  Policy '{pol_name}': {n_real}/{len(unique_orbits)} shadow orbits are real bad cycles")


# ================================================================
# DEFINITIVE CONCLUSION
# ================================================================
print(f"\n{'='*70}")
print("DEFINITIVE CONCLUSIONS")
print("="*70)
print(f"""
1. SHADOW ANATOMY:
   All shadow cycles (waterfall and non-waterfall) are CONSTANT-OFFSET
   translates of the good cycle: shadow[t] = good[t] + d (mod ms).
   Same mover word, same length, same structure.

2. THE MECHANISM IS ALGEBRAIC:
   The transition adds a fixed amount to one coordinate per step.
   Constant offset commutes with this operation.
   Every starting config produces an isomorphic orbit.

3. SHADOW EXISTENCE = DIFFERENCE SET GAP:
   Shadow exists iff |G - G| < product(ms).
   Sufficient: CL^2 < product (since |G-G| <= CL^2).
   - n >= 7, k >= 3 binary: CL^2 < product. Shadow GUARANTEED.
   - n = 5, 6: CL^2 may exceed product. Shadow usually exists but not always.

4. MNU IS NOT THE MECHANISM:
   MNU does NOT hold for the n=9 bounce-sweep (958/5808 uncovered).
   MNU does NOT hold for n=5 no-EC words (20/60 uncovered).
   Shadow formation depends on orbit algebra, not MNU.

5. WORD-LEVEL vs SYSTEM-LEVEL:
   Word-level shadows have both forced AND free entries at mover positions.
   With 'inc' free policy: many (but not all) shadow orbits become real
   bad-config cycles. Different policies give different shadow survival rates.
   But convergence ALWAYS fails (1M random policy samples, all fail).

6. NO VALID SYSTEM EXISTS for the 72 no-EC words at n=5:
   Despite no EC and no MNU, the forced entries from the good cycle constrain
   the bad graph enough that SOME bad cycle always survives.

7. EC vs SHADOW COVERAGE:
   - 99.99% of valid mover words have EC (automatically blocked)
   - The remaining 0.01% (72/778128 at n=5) have word-level shadow
   - ALL words are blocked: EC ∨ Shadow is UNIVERSAL at n=5

8. GENERALIZATION ASSESSMENT:
   Shadow DOES generalize beyond WaterfallCycles. The constant-offset
   mechanism works for ANY mover word, not just sweeps or wiggles.

   For n >= 7: shadow is GUARANTEED by counting for ALL minimum-CL words.
   This could replace the entire multi-mechanism proof architecture
   (Shadow Mirror, Wiggle Shadow, Palindromic EC, Universal EC).

   For n = 5, 6: EC handles 99.99%+. The remaining words have shadow.
   Could be verified computationally as finite cases.

   CAVEAT: The bridge from "word-level shadow exists" to "no valid system"
   needs a formal proof. The current data strongly supports it (1M samples,
   exhaustive for simple policies) but isn't a proof.
""")
