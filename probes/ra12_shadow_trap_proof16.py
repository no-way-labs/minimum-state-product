"""
Shadow Trap Proof — Part 16: Verify correlation between entry conflicts,
H-1 failures, and closure violations.

Hypothesis:
  Entry conflicts <==> H-1 failures <==> closure violations
  No entry conflicts ==> H-1 holds ==> closure holds ==> ShadowTrap exists
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

def enumerate_sweep_words(ms, n, max_words=100):
    CL = sum(ms)
    target_fc = {p: ms[p] for p in range(n)}
    results = []
    def dfs(word, fc):
        if len(results) >= max_words:
            return
        if len(word) == CL:
            d = 0
            for i in range(CL):
                diff = (word[(i+1) % CL] - word[i]) % n
                if diff == 1: d += 1
                elif diff == n-1: d -= 1
            if abs(d) >= 2:
                config = [0] * n
                for p in word:
                    config[p] = (config[p] + 1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return
        last = word[-1]
        for nxt in [(last-1) % n, (last+1) % n]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1; word.append(nxt)
                dfs(word, fc)
                word.pop(); fc[nxt] -= 1
    for p in range(n):
        fc = {q: 0 for q in range(n)}; fc[p] = 1
        dfs([p], fc)
        if len(results) >= max_words: break
    return results

def enumerate_value_sequences(m):
    seqs = []
    def dfs(seq, rem):
        if rem == 0:
            if seq[-1] == 0: seqs.append(tuple(seq))
            return
        for v in range(m):
            if v != seq[-1]:
                if rem == 1 and v != 0: continue
                seq.append(v); dfs(seq, rem-1); seq.pop()
    dfs([0], m)
    return seqs

def build_cycle(ms, n, word, combo):
    CL = len(word)
    fc = [0]*n
    state = [combo[p][0] for p in range(n)]
    configs = [tuple(state)]
    for s in range(CL):
        p = word[s]; fc[p] += 1; state[p] = combo[p][fc[p]]
        configs.append(tuple(state))
    if configs[-1] != configs[0]: return None
    configs = configs[:-1]
    if len(set(configs)) != CL: return None
    return configs

def check_entry_conflicts(ms, n, word, configs):
    CL = len(word)
    entries = {}
    has_conflict = False
    for s in range(CL):
        p = word[s]; c = configs[s]
        # Mover
        L,S,R = get_context(c, p, n)
        Sp = configs[(s+1)%CL][p]
        key = (p, L, S, R)
        if key in entries and entries[key] != Sp:
            has_conflict = True
        entries[key] = Sp  # Mover entry overrides
        # Non-movers
        for q in range(n):
            if q == p: continue
            Lq,Sq,Rq = get_context(c, q, n)
            key = (q, Lq, Sq, Rq)
            if key in entries and entries[key] != Sq:
                has_conflict = True
            elif key not in entries:
                entries[key] = Sq
    return has_conflict, entries

def check_h1(configs, n):
    CL = len(configs)
    for k in range(CL):
        gk = configs[k]
        h1 = [j for j in range(CL) if j != k and sum(1 for p in range(n) if gk[p] != configs[j][p]) == 1]
        if sorted(h1) != sorted([(k-1)%CL, (k+1)%CL]):
            return False
    return True

def check_closure(ms, n, configs, entries):
    good_set = set(configs)
    for c in itertools.product(*(range(m) for m in ms)):
        if c in good_set: continue
        for p in range(n):
            L,S,R = get_context(c, p, n)
            key = (p, L, S, R)
            if key in entries and entries[key] != S:
                nxt = list(c); nxt[p] = entries[key]; nxt = tuple(nxt)
                if nxt in good_set:
                    return False
                break
    return True

def find_shadow_cycle(ms, n, configs, entries):
    CL = len(configs)
    good_set = set(configs)
    g0 = configs[0]
    for q in range(n):
        for d in range(1, ms[q]):
            c = list(g0); c[q] = (c[q]+d) % ms[q]; c = tuple(c)
            if c in good_set: continue
            # Check if has forced step
            found = False
            for p in range(n):
                L,S,R = get_context(c, p, n)
                key = (p,L,S,R)
                if key in entries and entries[key] != S:
                    found = True; break
            if not found: continue
            # Follow orbit
            orbit = [c]; oset = {c}; cur = c
            for _ in range(CL*3):
                nxt = None
                for p in range(n):
                    L,S,R = get_context(cur, p, n)
                    key = (p,L,S,R)
                    if key in entries and entries[key] != S:
                        new = list(cur); new[p] = entries[key]; nxt = tuple(new)
                        break
                if nxt is None: break
                if nxt in good_set: break
                if nxt in oset:
                    idx = orbit.index(nxt)
                    return orbit[idx:]
                orbit.append(nxt); oset.add(nxt); cur = nxt
    return None

# ====================================================================
# TEST: Correlate entry conflicts, H-1, closure, ShadowTrap
# ====================================================================

for n, ms, desc in [
    (5, [2, 3, 2, 3, 2], "non-consecutive binary, n=5"),
    (5, [2, 2, 2, 3, 3], "consecutive binary, n=5"),
]:
    print(f"\n{'='*60}")
    print(f"{desc}: n={n}, ms={ms}")
    print(f"{'='*60}")

    words = enumerate_sweep_words(ms, n, max_words=50)
    val_seqs = {p: enumerate_value_sequences(ms[p]) for p in range(n)}

    stats = defaultdict(int)
    for word in words:
        for combo_idx in itertools.product(*[range(len(val_seqs[p])) for p in range(n)]):
            combo = tuple(val_seqs[p][combo_idx[p]] for p in range(n))
            configs = build_cycle(ms, n, word, combo)
            if configs is None: continue

            has_conflict, entries = check_entry_conflicts(ms, n, word, configs)
            h1_ok = check_h1(configs, n)

            if not has_conflict:
                closure_ok = check_closure(ms, n, configs, entries)
                cycle = find_shadow_cycle(ms, n, configs, entries)
                key = (has_conflict, h1_ok, closure_ok, cycle is not None)
            else:
                # Skip expensive checks for conflict cases
                key = (has_conflict, h1_ok, "skip", "skip")

            stats[key] += 1

    print("(conflict, H1, closure, cycle): count")
    for k, v in sorted(stats.items()):
        print(f"  {k}: {v}")

# ====================================================================
# THEOREM: H-1 Uniqueness holds when no entry conflicts
# ====================================================================

print("\n\n" + "="*60)
print("PROVING: No entry conflicts => H-1 Uniqueness")
print("="*60)

print("""
LEMMA (No Conflicts => H-1 Uniqueness).
If the forced entry table has no conflicts (every context (p, L, S, R)
has a unique forced value), then each good config g_k has exactly 2
Hamming-1 good neighbors.

Proof:
Suppose g_k and g_j differ at exactly one position p, with g_k[p] != g_j[p].
All other positions agree: g_k[q] = g_j[q] for q != p.

Consider proc p at config g_j. Its context is:
  (g_j[p-1], g_j[p], g_j[p+1]) = (g_k[p-1], g_j[p], g_k[p+1])

Since g_j is in the good cycle, this context appears in the forced entry
table. The entry maps g_j[p] to some value (either g_j[p] itself for
non-mover steps, or a different value for mover steps).

Similarly, proc p at config g_k sees (g_k[p-1], g_k[p], g_k[p+1]).

Now: g_k and g_j share ALL positions except p. So for any proc q != p:
  q's context in g_k = q's context in g_j IFF q is not adjacent to p.
  If q is adjacent to p: the shared context differs at exactly the
  position where p's value differs.

In particular, proc p's LEFT neighbor (p-1) and RIGHT neighbor (p+1)
have the same values in both configs. So proc p's context differs only
in the S component: (L, g_k[p], R) vs (L, g_j[p], R).

For g_j to be a good config adjacent to g_k at position p, we need
g_j to differ from g_k ONLY at position p. This means g_j must be
reachable from g_k by changing proc p's value.

In the good cycle, g_k is adjacent to g_{k-1} (differ at mover m_{k-1})
and g_{k+1} (differ at mover m_k). These account for 2 Hamming-1 neighbors.

Can there be more? Only if some other good config g_j differs from g_k
at position p (where p != m_k and p != m_{k-1}).

Key observation: if g_j differs from g_k at position p, then the config
c = g_k with c[p] = g_j[p] must equal g_j. This config has proc p's
context (L, g_j[p], R) where L = g_k[p-1] = g_j[p-1], R = g_k[p+1] = g_j[p+1].

In the forced entry table at g_k:
  proc p has context (L, g_k[p], R) -> some value v.
In the forced entry table at g_j:
  proc p has context (L, g_j[p], R) -> some value w.

If g_j[p] = v (the forced successor of g_k[p]), then g_j is one step
from g_k (proc p fires). This means g_j = g_{k+1} or g_j = g_{k-1}
(the two adjacent good configs).

If g_j[p] != v, then changing g_k[p] to g_j[p] does NOT match any
mover entry for proc p with this (L, R) context. BUT if there's a
DIFFERENT mover entry for proc p with the same (L, R), it could
still work.

THIS IS WHERE "NO ENTRY CONFLICTS" MATTERS:
No conflicts means: for each (proc, L, S, R), there is at most one
forced value. If (p, L, g_k[p], R) maps to v, and (p, L, g_j[p], R)
maps to w, these are DIFFERENT entries (different S values). Both can
exist without conflict. The issue would be if BOTH g_k[p] and g_j[p]
appear as mover contexts for proc p.

Actually, let me reconsider. The extra H-1 neighbors appear because
the good cycle visits a region of configuration space multiple times,
creating configs that happen to be Hamming-1. This CAN happen without
entry conflicts.

Let me check computationally: among the non-conflict instances,
does H-1 always hold?
""")

# From the data above, we already know:
# For n=5 non-consecutive: ALL 16 instances have conflicts.
# No conflict-free instances to test!
# Let me check with more words.

print("Checking n=5 non-consecutive for conflict-free instances...")
n = 5
ms = [2, 3, 2, 3, 2]
words = enumerate_sweep_words(ms, n, max_words=200)
val_seqs = {p: enumerate_value_sequences(ms[p]) for p in range(n)}

conflict_free = 0
total = 0
for word in words:
    for combo_idx in itertools.product(*[range(len(val_seqs[p])) for p in range(n)]):
        combo = tuple(val_seqs[p][combo_idx[p]] for p in range(n))
        configs = build_cycle(ms, n, word, combo)
        if configs is None: continue
        total += 1

        has_conflict, entries = check_entry_conflicts(ms, n, word, configs)
        if not has_conflict:
            conflict_free += 1
            h1_ok = check_h1(configs, n)
            closure_ok = check_closure(ms, n, configs, entries)
            cycle = find_shadow_cycle(ms, n, configs, entries)
            print(f"  CONFLICT-FREE: word={word}, H1={h1_ok}, closure={closure_ok}, cycle={cycle is not None}")
            if cycle:
                print(f"    Cycle length: {len(cycle)}")

print(f"\nTotal instances: {total}, conflict-free: {conflict_free}")
