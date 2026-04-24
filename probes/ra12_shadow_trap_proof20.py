"""
Shadow Trap Proof — Part 20: Understanding the binary firing pattern.

For n=9, ms=[2,3,3,2,3,3,2,3,3], sweep words have displacement = 2n = 18.
The binary procs at 0,3,6 each fire exactly 2 times.
These firings are NOT isolated because in a sweep the mover moves adjacently.

The "isolated firing" condition from the problem statement may actually
refer to something different, or it might be automatically satisfied for
the specific sweep structures we care about.

Let me re-read the problem: "isolated firings at some binary proc."
Maybe "isolated" just means the two firings of q are separated by
other procs' firings (they're not consecutive in the word). In a sweep,
this is ALWAYS true for binary procs in the interior of the sweep
(their two firings happen during opposite passes).

Actually, let me just verify the core claim more directly.
The problem says:
  "Following forced transitions from a shifted good config creates a
   cycle of length CL among non-good configs."

This is EXACTLY what I verified: 512/512 instances have CL-length cycles.
The proof should explain WHY this happens for ALL sweep words with this ms.

KEY STRUCTURAL PROPERTY:
In a sweep with displacement 2n, the mover visits every proc exactly
in order: 0->1->2->...->n-1->n-1->...->2->1->0 (right then left),
possibly with repeated visits for procs with m_p > 2.

At each binary proc q (m_q = 2):
- First firing (during forward pass): q changes 0 -> 1
- Second firing (during backward pass): q changes 1 -> 0
- Between these, the mover has moved away from q and returned.

The mover context at q's first firing: (L1, 0, R1)
The mover context at q's second firing: (L2, 1, R2)

For the shadow cycle to close, we need the "error" introduced at q
to propagate around and cancel. This happens because the sweep
structure ensures a specific relationship between the mover contexts.

Let me now write the ACTUAL proof based on what I've verified.
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

# Use the verified n=9 setup
n = 9
ms = [2,3,3,2,3,3,2,3,3]
CL = sum(ms)

# Build one specific instance
word = None
# Get first sweep word
def compute_displacement(w, n):
    total = 0; ell = len(w)
    for i in range(ell):
        diff = (w[(i+1)%ell] - w[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def enumerate_sweep_words(ms, n):
    CL = sum(ms)
    target_fc = {p: ms[p] for p in range(n)}
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    results = []
    def dfs(word, fc):
        if len(word) == CL:
            if abs(word[-1] - word[0]) % n in (1, n-1):
                config = [0]*n
                for p in word: config[p] = (config[p]+1) % ms[p]
                if all(c == 0 for c in config):
                    if abs(compute_displacement(word, n)) == 2*n:
                        results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1; word.append(nxt)
                if sum(target_fc[p] - fc[p] for p in range(n)) <= CL - len(word):
                    dfs(word, fc)
                word.pop(); fc[nxt] -= 1
    for p in range(n):
        if target_fc[p] > 0:
            fc = {q: 0 for q in range(n)}; fc[p] = 1
            dfs([p], fc)
    return results

words = enumerate_sweep_words(ms, n)
word = words[0]
print(f"Word: {word}")
print(f"Displacement: {compute_displacement(word, n)}")

# Use first valid combo
def enumerate_value_sequences(m, k):
    seqs = []
    def dfs(seq, rem):
        if rem == 0:
            if seq[-1] == 0: seqs.append(tuple(seq))
            return
        for v in range(m):
            if v != seq[-1]:
                if rem == 1 and v != 0: continue
                seq.append(v); dfs(seq, rem-1); seq.pop()
    dfs([0], k)
    return seqs

all_combos = {p: enumerate_value_sequences(ms[p], ms[p]) for p in range(n)}
combo = tuple(all_combos[p][0] for p in range(n))
print(f"Combo: {combo}")

# Build cycle
fc = [0]*n
state = [combo[p][0] for p in range(n)]
configs = []
for s in range(CL):
    configs.append(tuple(state))
    p = word[s]; fc[p] += 1; state[p] = combo[p][fc[p]]
assert tuple(state) == configs[0]

good_set = set(configs)
me = {}
for s in range(CL):
    p = word[s]; c = configs[s]
    L, S, R = get_context(c, p, n)
    Sp = configs[(s+1)%CL][p]
    me[(p, L, S, R)] = Sp

print(f"\nGood cycle ({CL} configs, {len(good_set)} distinct):")
for k in range(CL):
    p = word[k]; c = configs[k]
    L, S, R = get_context(c, p, n)
    Sp = configs[(k+1)%CL][p]
    print(f"  Step {k:2d}: mover={p}, ctx=({L},{S},{R})->{Sp}, cfg={c}")

# Find the shadow cycle
g0 = configs[0]
for q in range(n):
    for d in range(1, ms[q]):
        c0 = list(g0); c0[q] = (c0[q]+d)%ms[q]; c0 = tuple(c0)
        if c0 in good_set: continue

        # Follow forced orbit
        orbit = [c0]; oset = {c0}; cur = c0
        for step in range(CL*3):
            nxt = None
            for p in range(n):
                L, S, R = get_context(cur, p, n)
                key = (p, L, S, R)
                if key in me and me[key] != S:
                    new = list(cur); new[p] = me[key]; nxt = tuple(new)
                    break
            if nxt is None: break
            if nxt in oset:
                idx = orbit.index(nxt)
                cyc = orbit[idx:]
                if len(cyc) == CL and not any(cc in good_set for cc in cyc):
                    print(f"\n=== SHADOW CYCLE found from shifting proc {q} by {d} ===")
                    print(f"Tail length: {idx}, Cycle length: {len(cyc)}")

                    # Analyze: at each step, which proc fires and what good-cycle step matches?
                    print(f"\nShadow cycle step-by-step:")
                    matched_steps = []
                    for i in range(len(cyc)):
                        sc = cyc[i]
                        # Find forced proc
                        for p in range(n):
                            L, S, R = get_context(sc, p, n)
                            key = (p, L, S, R)
                            if key in me and me[key] != S:
                                # Find which good-cycle step this matches
                                for k in range(CL):
                                    if word[k] == p:
                                        gc = configs[k]
                                        if get_context(gc, p, n) == (L, S, R):
                                            matched_steps.append(k)
                                            break
                                break

                    print(f"Matched good-cycle steps: {matched_steps}")
                    if sorted(matched_steps) == list(range(CL)):
                        print("*** PERMUTATION of all CL steps! ***")
                        # Compute the permutation
                        perm = matched_steps
                        print(f"Permutation σ: shadow step i -> good step σ(i)")
                        for i in range(CL):
                            print(f"  σ({i:2d}) = {perm[i]:2d}")

                    # Also show the shadow configs and their difference from good configs
                    print(f"\nShadow vs good configs:")
                    for i in range(min(CL, 10)):
                        sc = cyc[i]
                        min_dist = min(sum(1 for a,b in zip(sc,g) if a!=b) for g in configs)
                        closest = min(range(CL), key=lambda k: sum(1 for a,b in zip(sc,configs[k]) if a!=b))
                        diff = [p for p in range(n) if sc[p] != configs[closest][p]]
                        print(f"  s_{i:2d}={sc}, closest=g_{closest}, Hamming={min_dist}, diff at {diff}")

                    # Stop after first shadow cycle
                    raise SystemExit(0)
            orbit.append(nxt); oset.add(nxt); cur = nxt
