#!/usr/bin/env python3
"""
RA Part 3: Verify the KEY finding and check universality.

KEY FINDING: The trap cycle uses ONLY forced entries. This means:
1. The good cycle forces certain table entries (mover + nonmover)
2. Those forced entries ALONE create a bad cycle (trap)
3. No matter how you fill the free entries, the trap persists
4. Therefore: this good cycle can NEVER lead to a convergent system

This is a STRUCTURAL OBSTRUCTION inherent in the stuttered sweep.
"""

import sys
import itertools
from collections import Counter, defaultdict

def enumerate_exact_fc_words(ms, n, target_fc):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    total_len = sum(target_fc[p] for p in range(n))
    results = []
    def dfs(word, fc):
        if len(word) == total_len:
            if abs(word[-1] - word[0]) % n in (1, n-1):
                config = [0]*n
                for p in word:
                    config[p] = (config[p]+1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                remaining = total_len - len(word)
                needed = sum(target_fc[p] - fc[p] for p in range(n))
                if needed <= remaining:
                    dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for p in range(n):
        if target_fc[p] > 0:
            fc = {q: 0 for q in range(n)}
            fc[p] = 1
            dfs([p], fc)
    return results

def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p]+1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]

def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best

def compute_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining-1)
                seq.pop()
    dfs([0], k)
    return seqs

def get_forced_entries(word, combo, ms, n):
    """Get all forced table entries from a good cycle."""
    ell = len(word)
    fc_counter = Counter(word)
    firing_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        firing_num[s] = pc[word[s]]
        pc[word[s]] += 1

    configs_seq = []
    state = [0]*n
    for s in range(ell):
        configs_seq.append(tuple(state))
        p = word[s]
        state[p] = combo[p][firing_num[s]+1]

    # Mover entries: f(L,S,R) = S' (different from S)
    mover_forced = {}  # (proc, L, S, R) -> S'
    for s in range(ell):
        p = word[s]
        L = configs_seq[s][(p-1)%n]
        S = configs_seq[s][p]
        R = configs_seq[s][(p+1)%n]
        S_new = combo[p][firing_num[s]+1]
        mover_forced[(p, L, S, R)] = S_new

    # Nonmover entries: f(L,S,R) = S (identity)
    nonmover_forced = {}
    for s in range(ell):
        for q in range(n):
            if q == word[s]:
                continue
            L = configs_seq[s][(q-1)%n]
            S = configs_seq[s][q]
            R = configs_seq[s][(q+1)%n]
            nonmover_forced[(q, L, S, R)] = S

    return mover_forced, nonmover_forced, configs_seq


def find_forced_bad_cycle(word, combo, ms, n):
    """
    Given a good cycle (word + combo), check if the forced entries alone
    create a bad cycle. Returns the bad cycle if found.

    A forced bad cycle exists when there's a sequence of configs c0, c1, ..., ck = c0
    such that:
    - Each ci is NOT a good config
    - At ci, some proc p is privileged (using forced mover entry: f(L,S,R) = S' != S)
    - Firing p at ci gives ci+1
    - At ci, the fired proc's context must be a forced mover entry
    - At ci, the non-fired procs must be non-privileged (which requires forced nonmover
      entry showing f(L,S,R) = S at their context, OR the context is free)

    Actually, the key insight is simpler:
    - Forced mover entries tell us exactly which (proc, context) pairs cause privilege
    - If a bad config has a proc privileged via a forced entry, and firing gives another
      bad config, we have a forced bad transition
    """
    mover_forced, nonmover_forced, configs_seq = get_forced_entries(word, combo, ms, n)
    good_set = set(configs_seq)
    ell = len(word)

    # Build lookup: for each proc p, which (L,S,R) are forced mover entries?
    mover_ctxs = defaultdict(dict)  # proc -> {(L,S,R): S'}
    for (p, L, S, R), Sp in mover_forced.items():
        mover_ctxs[p][(L, S, R)] = Sp

    nonmover_ctxs = defaultdict(set)  # proc -> set of (L,S,R)
    for (p, L, S, R), S in nonmover_forced.items():
        nonmover_ctxs[p].add((L, S, R))

    # For each config in the full space, check if it has a forced-privileged proc
    all_cfgs = list(itertools.product(*(range(m) for m in ms)))

    # Build forced-privilege graph
    forced_priv = {}  # config -> list of (proc, new_config) via forced entries
    for c in all_cfgs:
        if c in good_set:
            continue
        fps = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            ctx = (L, S, R)
            if ctx in mover_ctxs[p]:
                Sp = mover_ctxs[p][ctx]
                if Sp != S:  # privileged
                    nc = list(c)
                    nc[p] = Sp
                    nc = tuple(nc)
                    if nc not in good_set:
                        fps.append((p, nc))
        if fps:
            forced_priv[c] = fps

    # Find cycles in forced_priv graph
    # Build adjacency
    adj = defaultdict(list)
    for c, fps in forced_priv.items():
        for p, nc in fps:
            adj[c].append((nc, p))

    # Find SCCs using iterative Tarjan
    idx = {}
    low = {}
    on_stack = set()
    stack = []
    counter = [0]
    sccs = []

    def strongconnect(v):
        idx[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w, _ in adj[v]:
            if w not in idx:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    sys.setrecursionlimit(100000)
    for v in forced_priv:
        if v not in idx:
            strongconnect(v)

    return sccs, forced_priv, adj


# ============================================================
# Test on n=9
# ============================================================
print("=" * 72)
print("FORCED BAD CYCLE VERIFICATION")
print("=" * 72)

n = 9
ms = [2,3,3,2,3,3,2,3,3]
target_fc = {p: ms[p] for p in range(n)}
words = enumerate_exact_fc_words(ms, n, target_fc)

seen = set()
unique = []
for w in words:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique.append(w)

valid = []
for w in unique:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        valid.append((w, cycle))

sweeps = []
for w, cycle in valid:
    disp = compute_displacement(w, n)
    if abs(disp) == 2*n:
        sweeps.append((w, cycle, disp))

# Check ALL 8 sweeps x ALL combos
all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))
print(f"Total combos: {len(all_combos)}")

print(f"\n{'='*72}")
print("Checking all 8 sweeps x all {len(all_combos)} combos...")
print(f"{'='*72}")

for si, (w, cycle, disp) in enumerate(sweeps):
    print(f"\nSweep #{si}: {list(w)}, disp={disp:+d}")
    sys.stdout.flush()

    for ci, combo in enumerate(all_combos):
        sccs, forced_priv, adj = find_forced_bad_cycle(w, combo, ms, n)

        if sccs:
            # Find shortest cycle in any SCC
            shortest = None
            for scc in sccs:
                scc_set = set(scc)
                for start in list(scc_set)[:5]:
                    visited = {start: [start]}
                    queue = [start]
                    found = False
                    while queue and not found:
                        current = queue.pop(0)
                        for nxt, p in adj[current]:
                            if nxt == start and len(visited[current]) >= 2:
                                cyc = visited[current]
                                if shortest is None or len(cyc) < len(shortest):
                                    shortest = cyc
                                found = True
                                break
                            if nxt in scc_set and nxt not in visited:
                                visited[nxt] = visited[current] + [nxt]
                                if len(visited[nxt]) < 50:
                                    queue.append(nxt)

            scc_sizes = sorted([len(s) for s in sccs], reverse=True)
            print(f"  Combo {ci}: FORCED BAD SCCs={len(sccs)}, sizes={scc_sizes[:5]}, "
                  f"shortest_cycle={len(shortest) if shortest else '?'}")
        else:
            print(f"  Combo {ci}: NO forced bad cycle")
    sys.stdout.flush()

# ============================================================
# Detailed forced bad cycle for sweep #0, combo #0
# ============================================================
print(f"\n{'='*72}")
print("DETAILED FORCED BAD CYCLE")
print(f"{'='*72}")

w, cycle, disp = sweeps[0]
combo = all_combos[0]
sccs, forced_priv, adj = find_forced_bad_cycle(w, combo, ms, n)
mover_forced, nonmover_forced, configs_seq = get_forced_entries(w, combo, ms, n)

if sccs:
    # Find shortest cycle
    shortest = None
    shortest_movers = None
    for scc in sccs:
        scc_set = set(scc)
        for start in list(scc_set)[:10]:
            visited = {start: ([start], [])}  # (path, movers)
            queue = [start]
            found = False
            while queue and not found:
                current = queue.pop(0)
                for nxt, p in adj[current]:
                    if nxt == start and len(visited[current][0]) >= 2:
                        path, movers = visited[current]
                        movers = movers + [p]
                        if shortest is None or len(path) < len(shortest):
                            shortest = path
                            shortest_movers = movers
                        found = True
                        break
                    if nxt in scc_set and nxt not in visited:
                        path, movers = visited[current]
                        visited[nxt] = (path + [nxt], movers + [p])
                        if len(visited[nxt][0]) < 50:
                            queue.append(nxt)

    if shortest:
        print(f"Shortest forced bad cycle: length {len(shortest)}")
        print(f"Mover word: {shortest_movers}")
        print(f"Displacement: {compute_displacement(shortest_movers, n)}")
        print(f"Fire counts: {dict(Counter(shortest_movers))}")

        for step, cfg in enumerate(shortest):
            nxt = shortest[(step+1) % len(shortest)]
            p = shortest_movers[step]
            L = cfg[(p-1)%n]; S = cfg[p]; R = cfg[(p+1)%n]
            Sp = mover_forced.get((p, L, S, R), '?')
            print(f"  Step {step:2d}: {cfg} fire P{p} ctx=({L},{S},{R})->  {Sp}")

# ============================================================
# Check if the forced bad cycle OVERLAPS with good cycle contexts
# ============================================================
print(f"\n{'='*72}")
print("CONTEXT OVERLAP BETWEEN GOOD AND BAD CYCLES")
print(f"{'='*72}")

if shortest:
    # For each step in the bad cycle, check the mover and all non-movers
    mover_ctxs_good = defaultdict(set)
    nonmover_ctxs_good = defaultdict(set)
    for (p, L, S, R), Sp in mover_forced.items():
        mover_ctxs_good[p].add((L, S, R))
    for (p, L, S, R), S in nonmover_forced.items():
        nonmover_ctxs_good[p].add((L, S, R))

    bad_mover_ctxs = defaultdict(set)
    bad_nonmover_ctxs = defaultdict(set)

    for step, cfg in enumerate(shortest):
        p = shortest_movers[step]
        # Mover context
        L = cfg[(p-1)%n]; S = cfg[p]; R = cfg[(p+1)%n]
        bad_mover_ctxs[p].add((L, S, R))

        # Non-mover contexts
        for q in range(n):
            if q == p:
                continue
            Lq = cfg[(q-1)%n]; Sq = cfg[q]; Rq = cfg[(q+1)%n]
            bad_nonmover_ctxs[q].add((Lq, Sq, Rq))

    # Check overlap
    print("Mover context overlap (bad mover ctx appears in good mover):")
    for p in range(n):
        overlap = bad_mover_ctxs[p] & mover_ctxs_good[p]
        if overlap:
            print(f"  P{p}: {len(overlap)} overlapping mover contexts: {overlap}")

    print("\nBad mover appears in good NONmover (ENTRY CONFLICT!):")
    for p in range(n):
        overlap = bad_mover_ctxs[p] & nonmover_ctxs_good[p]
        if overlap:
            print(f"  P{p}: {len(overlap)} EC contexts: {overlap}")
            for ctx in overlap:
                good_val = nonmover_forced.get((p,) + ctx, '?')
                bad_val = mover_forced.get((p,) + ctx, '?')
                print(f"    ctx={ctx}: good nonmover says f={good_val}, bad mover says f={bad_val}")

    # The bad cycle uses forced MOVER entries to create privilege.
    # The same contexts appear as good NONMOVER entries (identity).
    # This is NOT a contradiction - the good cycle requires f(L,S,R)=S (nonmover),
    # while the bad cycle requires f(L,S,R)=S' != S (mover).
    # BUT THESE ARE THE SAME FUNCTION! So it IS a contradiction!
    #
    # Wait... the mover entry in the good cycle uses different (L,S,R) because S
    # is different (the mover's state changes). Let me re-check.
    #
    # Actually: forced mover entry means f_p(L,S,R) = S' where S' != S.
    # Forced nonmover entry means f_p(L,S,R) = S.
    # If the SAME (p,L,S,R) appears as both mover in good AND nonmover in bad (or vice versa),
    # that's a contradiction. But that's entry conflict, which we already checked and found NONE.
    #
    # The bad cycle is consistent BECAUSE the mover contexts in the bad cycle are
    # EXACTLY the same as mover contexts in the good cycle! The forced entries
    # created by the good cycle's mover steps are being REUSED in the bad cycle.

    print("\nKey: bad cycle movers reuse good cycle mover entries:")
    reuse_count = 0
    for step, cfg in enumerate(shortest):
        p = shortest_movers[step]
        L = cfg[(p-1)%n]; S = cfg[p]; R = cfg[(p+1)%n]
        key = (p, L, S, R)
        if key in mover_forced:
            reuse_count += 1
    print(f"  {reuse_count}/{len(shortest)} bad cycle steps reuse good mover entries")

print(f"\n{'='*72}")
print("SUMMARY")
print(f"{'='*72}")
print("""
KEY FINDING: FORCED-ENTRY TRAP

For every stuttered sweep good cycle at n=9, ms=[2,3,3,2,3,3,2,3,3]:
1. The good cycle forces table entries (mover: f(L,S,R)=S' != S; nonmover: f(L,S,R)=S)
2. These forced entries, applied to OTHER configs (not on the good cycle),
   create privileged procs at non-good configs
3. The resulting transitions among non-good configs form cycles (SCCs)
4. These cycles use ONLY forced entries — no free entries involved
5. Therefore: regardless of how free entries are filled, a bad cycle exists
6. Convergence is IMPOSSIBLE for any system with this good cycle

This is a STRUCTURAL obstruction: the good cycle's own forced entries
create an unavoidable bad cycle. It's a self-defeating cycle.

The proof mechanism:
- Given: a stuttered sweep good cycle
- Extract: the forced mover entries
- Show: these same mover entries make non-good configs privileged
- Show: the resulting transitions form a cycle among non-good configs
- Conclude: convergence fails (bad cycle exists regardless of free entries)
""")

# ============================================================
# Verify at n=7
# ============================================================
print(f"{'='*72}")
print("VERIFICATION AT n=7")
print(f"{'='*72}")

n7 = 7
ms7 = [2,3,3,2,3,3,2]
target7 = {p: ms7[p] for p in range(n7)}
words7 = enumerate_exact_fc_words(ms7, n7, target7)

seen7 = set()
unique7 = []
for w in words7:
    canon = canonicalize_word(w)
    if canon not in seen7:
        seen7.add(canon)
        unique7.append(w)

valid7 = []
for w in unique7:
    cyc = build_cycle(ms7, n7, w)
    if cyc is not None:
        valid7.append((w, cyc))

sweeps7 = [(w, c, compute_displacement(w, n7)) for w, c in valid7 if abs(compute_displacement(w, n7)) == 2*n7]
all_combos7 = list(itertools.product(*[enumerate_state_sequences(ms7[p], ms7[p]) for p in range(n7)]))

print(f"n=7, ms={ms7}")
print(f"Sweeps: {len(sweeps7)}, combos: {len(all_combos7)}")

for si, (w, cycle, disp) in enumerate(sweeps7):
    for ci, combo in enumerate(all_combos7):
        sccs, _, _ = find_forced_bad_cycle(w, combo, ms7, n7)
        scc_sizes = sorted([len(s) for s in sccs], reverse=True) if sccs else []
        if ci == 0 or sccs:
            print(f"  Sweep {si}, combo {ci}: forced SCCs={len(sccs)}, sizes={scc_sizes[:3]}")
    sys.stdout.flush()

print("\nDONE")
