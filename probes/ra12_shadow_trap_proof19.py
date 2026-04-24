"""
Shadow Trap Proof — Part 19: Testing at n=9 where isolated firings exist.

From MEMORY: ra12_farshift_claims.py verified 512/512 instances at n=9
with ms=[2,3,3,2,3,3,2,3,3]. Let me use similar setup.
"""

import itertools, time
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

def compute_displacement(word, n):
    total = 0; ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
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
    seen = set(); unique = []
    for w in results:
        canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
        if canon not in seen: seen.add(canon); unique.append(w)
    return unique

def enumerate_value_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0: seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0: continue
                seq.append(nv); dfs(seq, remaining-1); seq.pop()
    dfs([0], k)
    return seqs

def build_cycle(ms, n, word, combo):
    ell = len(word); fc = [0]*n
    state = [combo[p][0] for p in range(n)]
    configs = []
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]; fc[p] += 1; state[p] = combo[p][fc[p]]
    if tuple(state) != configs[0]: return None
    if len(set(configs)) != ell: return None
    return configs

def extract_mover_entries(ms, n, word, configs):
    ell = len(word)
    me = {}
    for s in range(ell):
        p = word[s]; c = configs[s]
        L, S, R = get_context(c, p, n)
        Sp = configs[(s+1)%ell][p]
        me[(p, L, S, R)] = Sp
    return me

def forced_step(n, c, me):
    for p in range(n):
        L, S, R = get_context(c, p, n)
        key = (p, L, S, R)
        if key in me and me[key] != S:
            nxt = list(c); nxt[p] = me[key]
            return tuple(nxt), p
    return None, None

def has_isolated_binary_firing(word, ms, n):
    CL = len(word)
    for q in range(n):
        if ms[q] != 2: continue
        fire_steps = [k for k in range(CL) if word[k] == q]
        if len(fire_steps) != 2: continue
        for k in fire_steps:
            kp = (k-1) % CL; kn = (k+1) % CL
            if word[kp] not in [(q-1)%n, (q+1)%n] and word[kn] not in [(q-1)%n, (q+1)%n]:
                return True, q, k
    return False, None, None

# ====================================================================
# Main test at n=9
# ====================================================================

n = 9
ms = [2,3,3,2,3,3,2,3,3]
CL = sum(ms)
print(f"n={n}, ms={ms}, CL={CL}")
print(f"Binary at: {[p for p in range(n) if ms[p]==2]}")

t0 = time.time()
words = enumerate_sweep_words(ms, n)
print(f"Sweep words: {len(words)} (in {time.time()-t0:.1f}s)")

all_combos = {p: enumerate_value_sequences(ms[p], ms[p]) for p in range(n)}
print(f"Combos per proc: {[len(all_combos[p]) for p in range(n)]}")

total_inst = 0
iso_cycle = 0
iso_no_cycle = 0
noiso_cycle = 0
noiso_no_cycle = 0
cycle_lens = defaultdict(int)

t0 = time.time()
for wi, w in enumerate(words):
    has_iso, _, _ = has_isolated_binary_firing(w, ms, n)

    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle(ms, n, w, combo_t)
        if cfgs is None: continue
        total_inst += 1

        gs = set(cfgs)
        me = extract_mover_entries(ms, n, w, cfgs)

        # Try to find shadow cycle
        found = False
        for q in range(n):
            if found: break
            for d in range(1, ms[q]):
                c0 = list(cfgs[0]); c0[q] = (c0[q]+d)%ms[q]; c0 = tuple(c0)
                if c0 in gs: continue
                nxt, p = forced_step(n, c0, me)
                if nxt is None: continue
                orbit = [c0]; oset = {c0}; cur = c0
                for _ in range(CL*3):
                    nxt, p = forced_step(n, cur, me)
                    if nxt is None: break
                    if nxt in oset:
                        idx = orbit.index(nxt)
                        cyc = orbit[idx:]
                        if not any(cc in gs for cc in cyc):
                            found = True
                            cycle_lens[len(cyc)] += 1
                        break
                    orbit.append(nxt); oset.add(nxt); cur = nxt
                if found: break

        if has_iso:
            if found: iso_cycle += 1
            else: iso_no_cycle += 1
        else:
            if found: noiso_cycle += 1
            else: noiso_no_cycle += 1

print(f"\nResults ({total_inst} instances, {time.time()-t0:.1f}s):")
print(f"Isolated + cycle:    {iso_cycle}")
print(f"Isolated + NO cycle: {iso_no_cycle}")
print(f"No iso + cycle:      {noiso_cycle}")
print(f"No iso + NO cycle:   {noiso_no_cycle}")
print(f"Cycle lengths: {dict(cycle_lens)}")
