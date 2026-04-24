"""
Shadow Trap Proof — Part 18: Correlate isolated binary firings with cycle existence.

From Part 17: 84/120 have cycles, 36 don't.
Hypothesis: The 36 failures all lack isolated binary firings.
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

def enumerate_sweep_words(ms, n, max_words=200):
    CL = sum(ms)
    target_fc = {p: ms[p] for p in range(n)}
    results = []
    def dfs(word, fc):
        if len(results) >= max_words: return
        if len(word) == CL:
            d = 0
            for i in range(CL):
                diff = (word[(i+1) % CL] - word[i]) % n
                if diff == 1: d += 1
                elif diff == n-1: d -= 1
            if abs(d) >= 2:
                config = [0] * n
                for p in word: config[p] = (config[p] + 1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return
        last = word[-1]
        for nxt in [(last-1) % n, (last+1) % n]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1; word.append(nxt)
                dfs(word, fc); word.pop(); fc[nxt] -= 1
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

def has_isolated_binary_firing(word, ms, n):
    """Check if any binary proc has isolated firings.
    'Isolated' = the mover before and after q's firing are NOT adjacent to q.
    """
    CL = len(word)
    for q in range(n):
        if ms[q] != 2: continue
        fire_steps = [k for k in range(CL) if word[k] == q]
        if len(fire_steps) != 2: continue

        for k in fire_steps:
            k_prev = (k - 1) % CL
            k_next = (k + 1) % CL
            prev_is_neighbor = (word[k_prev] == (q-1) % n or word[k_prev] == (q+1) % n)
            next_is_neighbor = (word[k_next] == (q-1) % n or word[k_next] == (q+1) % n)
            if not prev_is_neighbor and not next_is_neighbor:
                return True, q, k
    return False, None, None

def extract_mover_entries(ms, n, word, configs):
    CL = len(word)
    me = {}
    for s in range(CL):
        p = word[s]; c = configs[s]
        L, S, R = get_context(c, p, n)
        Sp = configs[(s+1) % CL][p]
        me[(p, L, S, R)] = Sp
    return me

def forced_step_mover_only(n, c, me):
    for p in range(n):
        L, S, R = get_context(c, p, n)
        key = (p, L, S, R)
        if key in me and me[key] != S:
            nxt = list(c); nxt[p] = me[key]
            return tuple(nxt), p
    return None, None

def find_cycle_from_start(start, n, ms, me, good_set, max_steps):
    orbit = [start]; oset = {start}; cur = start
    for _ in range(max_steps):
        nxt, p = forced_step_mover_only(n, cur, me)
        if nxt is None: return None
        # Allow reaching good (it continues from good)
        if nxt in oset:
            idx = orbit.index(nxt)
            return orbit[idx:]
        orbit.append(nxt); oset.add(nxt); cur = nxt
    return None

# ====================================================================
n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)

words = enumerate_sweep_words(ms, n, max_words=200)
val_seqs = {p: enumerate_value_sequences(ms[p]) for p in range(n)}

iso_cycle = 0
iso_no_cycle = 0
noiso_cycle = 0
noiso_no_cycle = 0

fail_examples = []

for word in words:
    for combo_idx in itertools.product(*[range(len(val_seqs[p])) for p in range(n)]):
        combo = tuple(val_seqs[p][combo_idx[p]] for p in range(n))
        configs = build_cycle(ms, n, word, combo)
        if configs is None: continue

        good_set = set(configs)
        me = extract_mover_entries(ms, n, word, configs)
        if len(me) < CL: continue  # Skip dup contexts

        has_iso, iso_q, iso_k = has_isolated_binary_firing(word, ms, n)

        # Try to find a cycle from any shifted good config
        found_cycle = False
        g0 = configs[0]
        for q in range(n):
            if found_cycle: break
            for d in range(1, ms[q]):
                c = list(g0); c[q] = (c[q]+d) % ms[q]; c = tuple(c)
                if c in good_set: continue
                cycle = find_cycle_from_start(tuple(c), n, ms, me, good_set, CL*3)
                if cycle is not None:
                    found_cycle = True
                    break

        if has_iso:
            if found_cycle:
                iso_cycle += 1
            else:
                iso_no_cycle += 1
                fail_examples.append((word, combo))
        else:
            if found_cycle:
                noiso_cycle += 1
            else:
                noiso_no_cycle += 1

print(f"Isolated binary + cycle:    {iso_cycle}")
print(f"Isolated binary + NO cycle: {iso_no_cycle}")
print(f"No isolated + cycle:        {noiso_cycle}")
print(f"No isolated + NO cycle:     {noiso_no_cycle}")

if fail_examples:
    print(f"\nFailing examples (isolated + no cycle):")
    for word, combo in fail_examples[:5]:
        print(f"  Word: {word}")
        print(f"  Combo: {combo}")
        has_iso, q, k = has_isolated_binary_firing(word, ms, n)
        print(f"  Isolated: proc {q} at step {k}")

# Maybe I should try ALL starting configs, not just shifted g_0
print("\n\nRetrying with ALL non-good starting configs...")

iso_cycle2 = 0
iso_no_cycle2 = 0

for word in words:
    for combo_idx in itertools.product(*[range(len(val_seqs[p])) for p in range(n)]):
        combo = tuple(val_seqs[p][combo_idx[p]] for p in range(n))
        configs = build_cycle(ms, n, word, combo)
        if configs is None: continue

        good_set = set(configs)
        me = extract_mover_entries(ms, n, word, configs)
        if len(me) < CL: continue

        has_iso, _, _ = has_isolated_binary_firing(word, ms, n)
        if not has_iso: continue

        # Try ALL non-good configs as starting points
        all_cfgs = list(itertools.product(*(range(m) for m in ms)))
        non_good = [c for c in all_cfgs if c not in good_set]

        found_cycle = False
        for c in non_good:
            nxt, p = forced_step_mover_only(n, c, me)
            if nxt is None: continue
            cycle = find_cycle_from_start(c, n, ms, me, good_set, CL*3)
            if cycle is not None:
                # Check: is it a cycle of non-good configs?
                if not any(cc in good_set for cc in cycle):
                    found_cycle = True
                    break

        if found_cycle:
            iso_cycle2 += 1
        else:
            iso_no_cycle2 += 1

print(f"Isolated + cycle (any start): {iso_cycle2}")
print(f"Isolated + NO cycle:          {iso_no_cycle2}")
