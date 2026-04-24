"""
H-1 Uniqueness — Proof v2

THEOREM: For n >= 3, in a good cycle with fc(p) = m_p for all p,
if fib_p(j) = fib_p(k) with j != k, then |j-k| = 1 mod CL and
moverAt(min(j,k)) = p (or moverAt(max(j,k)-1 mod CL) = p for the wrap case).

PROOF ATTEMPT: Uniqueness of dynamics.

Suppose fib_p(j) = fib_p(k) = F, with g_j[p] = v, g_k[p] = w, v != w.
g_j and g_k are distinct good configs with the same fiber.

The dynamics are deterministic: from any good config, the next config
is uniquely determined (fire the unique privileged proc).

So: g_j determines the entire future of the cycle.
And: g_k determines the entire future of the cycle.
These are the SAME cycle (shifted): g_{j+t} and g_{k+t} are both
in the cycle, for all t.

Now: at step j, the privileged proc is moverAt(j).
At step k, the privileged proc is moverAt(k).

For proc q not adjacent to p and q != p:
  q's context (L_q, S_q, R_q) is the same in g_j and g_k.
  So: q is privileged in g_j iff q is privileged in g_k.

For proc p:
  p's context is (g[p-1], v, g[p+1]) vs (g[p-1], w, g[p+1]).
  Different S value. May or may not be privileged.

For proc p-1 (if p-1 != p, which holds for n >= 3):
  p-1's context: (g[p-2], g[p-1], g[p]) = (g[p-2], g[p-1], v)
  vs (g[p-2], g[p-1], w). Different R.

For proc p+1:
  p+1's context: (g[p], g[p+1], g[p+2]) = (v, g[p+1], g[p+2])
  vs (w, g[p+1], g[p+2]). Different L.

So: for procs NOT in {p-1, p, p+1}, privilege is the same.
For procs IN {p-1, p, p+1}, privilege may differ.

CASE ANALYSIS on moverAt(j):

Case 1: moverAt(j) = q, where q not in {p-1, p, p+1}.
  q is privileged in g_j. Since q's context is same in g_k: q is privileged in g_k.
  By uniqueness: moverAt(k) = q.
  Firing q: g_{j+1}[q] = f_q(L,S,R), g_{k+1}[q] = f_q(L,S,R). Same result.
  All other positions stay the same. In particular: fib_p(j+1) = fib_p(k+1).
  AND: g_{j+1}[p] = v, g_{k+1}[p] = w. Still Hamming-1.
  So: the Hamming-1 pair propagates forward!

Case 2: moverAt(j) = p.
  p is privileged in g_j. In g_k: p has different S but same neighbors.
  If p is also privileged in g_k: moverAt(k) = p.
    Fire p: g_{j+1}[p] = f_p(g[p-1], v, g[p+1]) =: v'.
    g_{k+1}[p] = f_p(g[p-1], w, g[p+1]) =: w'.
    v' != v (privileged => changes), w' != w.
    If v' != w': still Hamming-1 at p. fib_p unchanged. Propagates.
    If v' = w': g_{j+1} = g_{k+1}. But configs in good cycle are distinct.
      So j+1 = k+1 mod CL => j = k. Contradiction.
    So: v' != w' and pair propagates.

  If p is NOT privileged in g_k:
    moverAt(k) must be some proc in {p-1, p+1} (since non-neighbors match privilege).
    Also: moverAt(j) = p, so no other proc is privileged in g_j.
    In particular: p-1 and p+1 are NOT privileged in g_j.
    But: could be privileged in g_k (different context at R or L respectively).

    Say moverAt(k) = p+1.
    Then: g_{j+1} differs from g_j at p. g_{k+1} differs from g_k at p+1.
    fib_p(j+1): changes at p's value only (p fires), so fib_p(j+1) = F (unchanged!).
    Wait no: fib_p includes position p+1. Only p changes, so fib_p(j+1) = F. Yes.
    fib_p(k+1): p+1 fires in g_k, so fib_p changes at position p+1.
    fib_p(k+1) != F (since p+1's value changes).

    So: fib_p(j+1) = F but fib_p(k+1) != F.
    And: g_{j+1}[p] = v' (after firing p), g_{k+1}[p] = w (p didn't fire in g_k).

    Now: fib_p(j+1) = F = fib_p(j) but g_{j+1}[p] = v' != v = g_j[p].
    So g_j and g_{j+1} are Hamming-1 at p, which means j and j+1 are adjacent.
    That's fine — this IS the adjacent Hamming-1 pair from p firing at step j.

    But the ORIGINAL pair (j, k) with shared fiber F:
    After one step: j+1 still has fiber F, but k+1 doesn't.
    The pair (j+1, k+1) is NOT Hamming-1 at p.

    KEY: Can this Case 2b actually happen? If it does, the propagation
    breaks, but does it contradict anything?

    At step j+1: fib_p(j+1) = F, g_{j+1}[p] = v'.
    At step k: fib_p(k) = F, g_k[p] = w.
    So there are now THREE indices with fiber F: j, k, and j+1.
    g_j[p] = v, g_{j+1}[p] = v', g_k[p] = w.
    With v != w, v != v', and possibly v' = w or v' != w.

    If v' = w: g_{j+1} = g_k (same fiber AND same p-value).
    But g_{j+1} and g_k are in the cycle, so j+1 = k. Then d = k-j = 1. ✓
    This contradicts our assumption d >= 2!

    If v' != w: three configs (g_j, g_{j+1}, g_k) all have fiber F
    but distinct p-values v, v', w. Since p has m_p states, this is
    possible only if m_p >= 3.

    Continue propagation from j+1: fib_p(j+1) = F = fib_p(k).
    At j+1: moverAt(j+1) could again fall into Cases 1, 2, or 3.

    If Case 2b happens again at j+1 (p fires at j+1 but not at k+1):
    Wait, we already handled p firing at j. At j+1, what happens?

    Actually: after p fires at j, the config changes at p.
    At j+1, moverAt(j+1) is determined by g_{j+1}.
    Meanwhile at k+1, fib_p(k+1) != F, so the k-chain has diverged.

    Hmm, but we said fib_p(j+1) = F = fib_p(k). So we can restart
    the argument with the pair (j+1, k) instead of (j, k).
    The distance is now k - (j+1) = d - 1.

    If d - 1 >= 2: repeat. Eventually d shrinks to 1, giving adjacent pair.

    BUT: this only works if Case 2b always produces v' = w (forcing d=1)
    or always reduces d. What if Case 3 (moverAt(j) = p-1 or p+1) occurs?

Case 3: moverAt(j) = p+1 (symmetric for p-1).
  p+1 is privileged in g_j. p+1's context: (v, g[p+1], g[p+2]).
  In g_k: (w, g[p+1], g[p+2]). Different L.

  If p+1 is also privileged in g_k: moverAt(k) = p+1.
    Fire p+1 in both:
    g_{j+1}[p+1] = f_{p+1}(v, g[p+1], g[p+2]) =: s1
    g_{k+1}[p+1] = f_{p+1}(w, g[p+1], g[p+2]) =: s2
    If s1 = s2: fib_p(j+1) = fib_p(k+1). Same fiber. Distance preserved.
      g_{j+1}[p] = v, g_{k+1}[p] = w. Still Hamming-1. Propagation!
    If s1 != s2: fib_p(j+1) != fib_p(k+1). Fiber diverges!
      Hamming distance becomes 2 (differ at p and p+1). Pair destroyed.

    So: in this sub-case, if s1 != s2, the pair is DESTROYED.
    But was this pair "real" to begin with? Yes — we assumed it exists.
    So: after one step, it's gone. This doesn't give us a contradiction YET.

  If p+1 is NOT privileged in g_k:
    Then moverAt(k) is something else. As before, must be in {p-1, p, p+1}
    (excluding p+1 now). So moverAt(k) in {p-1, p}.

    Sub-sub-case: moverAt(k) = p.
    p fires in g_k: g_{k+1}[p] = w' != w.
    p+1 fires in g_j: g_{j+1}[p+1] = s1 != g_j[p+1].
    fib_p(j+1) differs from F at position p+1.
    fib_p(k+1) = F (only p changed, which is excluded from fiber).

    So fib_p(k+1) = F but fib_p(j+1) != F.
    The j-chain diverged from F.

    We can restart with pair (j, k+1): fib_p(j) = F = fib_p(k+1).
    Distance: (k+1) - j = d + 1. That INCREASES! Bad.

    But: g_j[p] = v, g_{k+1}[p] = w'. If w' = v: g_j = g_{k+1} => j = k+1 mod CL.
    That means d = CL-1, cyclic distance 1. ✓

    If w' != v: pair persists with larger distance...

This case analysis is getting complex. Let me try a GLOBAL argument instead.

Suppose the fiber F appears at indices I = {i_1, i_2, ..., i_r} (sorted).
Each pair of consecutive indices either:
- Has the same mover (both fire p, or both fire q != p with same fib)
- Has different movers

The fiber F appears whenever p fires (since fib doesn't change when p fires),
and may appear at other times.

Actually: the fiber is F at step i and step i+1 iff moverAt(i) = p.
So: the set I consists of "blocks" of consecutive indices, where within
each block, p fires (mover = p) at all steps except the last.

Each block has form [a, a+1, ..., a+t] where moverAt(a) = ... = moverAt(a+t-1) = p
and moverAt(a+t) != p (or it wraps).

Wait: if moverAt(a) = p, then fib_p(a) = fib_p(a+1). And if moverAt(a+1) = p too,
then fib_p(a+1) = fib_p(a+2). So fib_p(a) = fib_p(a+2). Etc.
A "p-block" of consecutive p-firings gives a block with constant fiber.

Between p-blocks, the fiber changes (since a non-p proc fires, changing the fiber).

So: |I| = sum of (block_length + 1) for each p-block, where block_length =
number of consecutive p-firings.

Actually: I = union of intervals [a, a+len] for each maximal run of p-firings
starting at step a with len firings.

Number of such maximal runs: at most m_p (since total p-firings = m_p).

Wait, if p fires consecutively, say steps a, a+1, ..., a+t-1 are all p-firings:
these are t firings. The fiber is constant on {a, a+1, ..., a+t}.
(t+1 indices, t firings.)

After step a+t, the mover changes (to some q != p), and the fiber changes.
If later the fiber returns to F (at some other p-block), we have another cluster.

The question is: can the fiber return to F at a different p-block?

Between two p-blocks: non-p procs fire, changing the fiber. For the fiber to
return to F: all the non-p firings between the blocks must collectively
return every non-p value to its state at F.

This is the same "return" constraint as before. And this IS possible at n=2
(as we've seen). The question is whether it's possible at n >= 3.

I THINK the answer is that it IS possible in principle but may not occur
in practice for token rings. Let me check more carefully with a dedicated test.
"""

# Let me construct a SPECIFIC potential counterexample at n=3 and see if it's valid.
# Idea: ms=[2,3,3], try to build a system where fib_1 repeats.
# Between two p=1 blocks, procs 0 and 2 must return to their values.
# Proc 0 is binary: fires twice total. To return: fires 0 or 2 times in between.
# Proc 2 is ternary: fires 3 times total. To return: fires 0 or 3 times.

# If proc 0 fires 2 times and proc 2 fires 0 times between blocks:
# Between blocks: 2 steps (proc 0 fires twice, returns to start).
# But during these 2 steps, proc 0's transitions depend on neighbors.
# At n=3: proc 0's neighbors are proc 2 (L) and proc 1 (R).
# Proc 1 value = constant within the gap (proc 1 not firing between blocks).
# Wait, "between blocks" means proc 1 is NOT firing. So proc 1's value is
# constant. And proc 2 is not firing either. So proc 0 fires twice with
# fixed neighbors.

# Proc 0 fires step 1: context (g[2], g[0], g[1]) = (c2, v0, c1).
# f_0(c2, v0, c1) = v0' != v0.
# Proc 0 fires step 2: context (g[2], v0', g[1]) = (c2, v0', c1).
# f_0(c2, v0', c1) = v0'' != v0'.
# For return: v0'' = v0. So: f_0(c2, f_0(c2, v0, c1), c1) = v0.
# With m_0 = 2: v0 in {0,1}. v0' = 1-v0. v0'' = f_0(c2, 1-v0, c1).
# Need v0'' = v0. So f_0(c2, 1-v0, c1) = v0 = 1-(1-v0).
# f_0(c2, 0, c1) = 1 and f_0(c2, 1, c1) = 0 for some (c2, c1).
# This means: for context (c2, *, c1), proc 0 always toggles. This IS privileged
# at both values. But that means BOTH configs with these contexts have proc 0
# privileged. For unique privilege: no other proc can be privileged at those configs.

# So: a gap between two p=1 blocks where proc 0 fires twice is possible if:
# 1. Proc 0 toggles at contexts (c2, 0, c1) and (c2, 1, c1).
# 2. Proc 1 is NOT privileged at either config (even though p=1 value is constant c1).
# 3. Proc 2 is NOT privileged at either config.

# For (2): proc 1's context is (g[0], c1, c2). At step 1: (v0, c1, c2).
# At step 2: (v0', c1, c2) = (1-v0, c1, c2).
# For proc 1 not privileged: f_1(v0, c1, c2) = c1 AND f_1(1-v0, c1, c2) = c1.
# Possible if proc 1's transition function gives c1 for both left-neighbor values.

# For (3): proc 2's context is (c1, c2, g[0]). At step 1: (c1, c2, v0).
# At step 2: (c1, c2, 1-v0).
# For proc 2 not privileged: f_2(c1, c2, v0) = c2 AND f_2(c1, c2, 1-v0) = c2.

# So it's POSSIBLE to have a gap where proc 0 returns. But this only gives
# us the return of proc 0. We also need proc 2 to return (it fires 0 times,
# so it's trivially returned since it doesn't fire).

# So: the fiber at proc 1 could repeat if all other procs return between
# two proc-1 blocks. Let me try to construct such a system.

from itertools import product as iprod

def build_and_check(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        privs = []
        for pp in range(n):
            L = config[(pp-1)%n]; S = config[pp]; R = config[(pp+1)%n]
            if tables[pp][(L,S,R)] != S:
                privs.append(pp)
        if len(privs) == 1:
            good[config] = privs[0]
    if not good: return None
    start = next(iter(good))
    cycle = [start]; movers = [good[start]]; cur = start
    for _ in range(100000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None

    CL = len(cycle)
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): return None

    # Check fiber repetition
    for p in range(n):
        fibers = {}
        for i in range(CL):
            fib = tuple(cycle[i][q] for q in range(n) if q != p)
            if fib not in fibers: fibers[fib] = []
            fibers[fib].append(i)
        for fib, idxs in fibers.items():
            if len(idxs) >= 2:
                for a in range(len(idxs)):
                    for b in range(a+1, len(idxs)):
                        j, k = idxs[a], idxs[b]
                        cdist = min(k-j, CL-(k-j))
                        if cdist > 1:
                            return (cycle, movers, p, j, k, fib)
    return True  # no violations

# Try to construct: ms=[2,3,3]
# Target: proc 1 fires at steps {0,1,2} (block 1) and {5,6,7} (block 2)
# Between blocks: steps 3,4 have proc 0 firing (toggles and returns)
# Also need wrap-around.

# Actually, let me just do exhaustive search for small ms at n=3.
# ms=[2,2,3]: total configs = 12, manageable table sizes.

import random
random.seed(0)
ms = [2, 2, 3]
n = 3
print(f"Exhaustive search for ms={ms}")
total_valid = 0
total_violations = 0
# Each proc has mL*mS*mR contexts. Table size:
# proc 0: 3*2*2=12 contexts, each maps to {0,1}. 2^12 = 4096 tables.
# proc 1: 2*2*3=12 contexts, each maps to {0,1}. 2^12 = 4096 tables.
# proc 2: 2*3*2=12 contexts, each maps to {0,1,2}. 3^12 = 531441 tables.
# Total: too many for exhaustive. Use random.

for trial in range(500000):
    tables = []
    for p in range(n):
        t = {}
        mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    t[(L,S,R)] = random.randrange(mS)
        tables.append(t)
    result = build_and_check(ms, tables)
    if result is None: continue
    total_valid += 1
    if result is not True:
        total_violations += 1
        cycle, movers, p, j, k, fib = result
        CL = len(cycle)
        print(f"  VIOLATION: p={p}, j={j}, k={k}, cdist={min(k-j,CL-(k-j))}")
        print(f"  CL={CL}, movers={movers}")
        for i in range(CL):
            marker = " <--" if i in [j,k] else ""
            print(f"  [{i}] {cycle[i]} m={movers[i]}{marker}")
        if total_violations >= 3:
            break

print(f"\nms={ms}: {total_valid} valid, {total_violations} violations (out of 500k trials)")
