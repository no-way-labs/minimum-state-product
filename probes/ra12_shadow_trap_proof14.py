"""
Shadow Trap Proof — Part 14: Diagnosing H-1 Uniqueness failure.

H-1 fails for non-consecutive binary because multiple good configs
can share values at all but one position. This happens when the sweep
word visits the same proc from different directions, creating configs
that differ at only one position despite being far apart in the cycle.

The issue: for a SWEEP (mover moves adjacently), consecutive configs
differ at the mover position. But non-consecutive configs might also
be Hamming-1 if the sweep visits the same region twice.

Let me understand EXACTLY when H-1 fails and what goes wrong.
"""

import itertools

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

# The failing case: n=5, ms=[2,3,2,3,2], some sweep word
# Let me reproduce and analyze

n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)  # 12

def enumerate_sweep_words_small(ms, n):
    CL = sum(ms)
    target_fc = {p: ms[p] for p in range(n)}
    results = []
    def dfs(word, fc):
        if len(results) > 20:
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
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for p in range(n):
        fc = {q: 0 for q in range(n)}
        fc[p] = 1
        dfs([p], fc)
    return results

def enumerate_value_sequences(m):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for v in range(m):
            if v != seq[-1]:
                if remaining == 1 and v != 0:
                    continue
                seq.append(v)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], m)
    return seqs

def build_cycle(ms, n, word, combo):
    CL = len(word)
    fc = [0] * n
    state = [combo[p][0] for p in range(n)]
    configs = [tuple(state)]
    for s in range(CL):
        p = word[s]
        fc[p] += 1
        state[p] = combo[p][fc[p]]
        configs.append(tuple(state))
    if configs[-1] != configs[0]:
        return None
    configs = configs[:-1]
    if len(set(configs)) != CL:
        return None
    return configs

words = enumerate_sweep_words_small(ms, n)
val_seqs = {p: enumerate_value_sequences(ms[p]) for p in range(n)}

print(f"Sweep words: {len(words)}")
print(f"Value sequences per proc: {[len(val_seqs[p]) for p in range(n)]}")

# Find an H-1 failing instance
for word in words[:5]:
    for combo_idx in itertools.product(*[range(len(val_seqs[p])) for p in range(n)]):
        combo = tuple(val_seqs[p][combo_idx[p]] for p in range(n))
        configs = build_cycle(ms, n, word, combo)
        if configs is None:
            continue

        # Check H-1
        good_set = set(configs)
        cfg_to_idx = {c: i for i, c in enumerate(configs)}

        for k in range(CL):
            g_k = configs[k]
            h1 = []
            for j in range(CL):
                if j == k:
                    continue
                if sum(1 for p in range(n) if g_k[p] != configs[j][p]) == 1:
                    h1.append(j)
            if len(h1) != 2:
                print(f"\nH-1 FAILURE at k={k}:")
                print(f"  Word: {word}")
                print(f"  Combo: {combo}")
                print(f"  g_{k} = {g_k}")
                print(f"  H-1 neighbors: {h1} (expected [{(k-1)%CL}, {(k+1)%CL}])")
                for j in h1:
                    diff_pos = [p for p in range(n) if g_k[p] != configs[j][p]]
                    print(f"    g_{j} = {configs[j]}, differs at pos {diff_pos}")

                # Why does this happen? Show the full cycle
                print(f"\n  Full cycle:")
                for i in range(CL):
                    mover_pos = [p for p in range(n) if configs[i][p] != configs[(i+1)%CL][p]]
                    print(f"    g_{i:2d} = {configs[i]} -> mover at {mover_pos}")

                # Check: is the mover context table still valid?
                cmap = {}
                dup = False
                for step in range(CL):
                    p = word[step]
                    g = configs[step]
                    L, S, R = get_context(g, p, n)
                    Sp = configs[(step+1) % CL][p]
                    key = (p, L, S, R)
                    if key in cmap:
                        print(f"\n  DUPLICATE CONTEXT: step {step}, key={key}")
                        print(f"    Previous: step {cmap[key][1]}, S'={cmap[key][0]}")
                        print(f"    Current:  step {step}, S'={Sp}")
                        dup = True
                    cmap[key] = (Sp, step)

                if not dup:
                    print(f"\n  No duplicate contexts (all {len(cmap)} are unique)")

                # KEY: When H-1 fails, does non-good closure still hold?
                entries = {}
                for step in range(CL):
                    p = word[step]
                    c = configs[step]
                    for q in range(n):
                        L = c[(q-1) % n]; S = c[q]; R = c[(q+1) % n]
                        if q == p:
                            Sp = configs[(step+1) % CL][p]
                            entries[(q, L, S, R)] = Sp
                        else:
                            key = (q, L, S, R)
                            if key not in entries:
                                entries[key] = S

                # Check closure
                all_cfgs = list(itertools.product(*(range(m) for m in ms)))
                non_good = [c for c in all_cfgs if c not in good_set]
                violations = 0
                for c in non_good:
                    for p in range(n):
                        L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
                        key = (p, L, S, R)
                        if key in entries and entries[key] != S:
                            nxt = list(c)
                            nxt[p] = entries[key]
                            nxt = tuple(nxt)
                            if nxt in good_set:
                                violations += 1
                                print(f"\n  CLOSURE VIOLATION: {c} -> {nxt} (good) via proc {p}")
                                # Which good config is nxt?
                                nxt_idx = cfg_to_idx[nxt]
                                # c is Hamming-1 from nxt
                                diff_pos = [pp for pp in range(n) if c[pp] != nxt[pp]]
                                print(f"    nxt = g_{nxt_idx}, diff at pos {diff_pos}")
                                # c is non-good but Hamming-1 from g_{nxt_idx}
                                # Is c a Hamming-1 neighbor of g_{nxt_idx} that's NOT g_{nxt_idx-1} or g_{nxt_idx+1}?
                                h1_nxt = [(j, configs[j]) for j in range(CL)
                                          if j != nxt_idx and sum(1 for pp in range(n) if nxt[pp] != configs[j][pp]) == 1]
                                print(f"    g_{nxt_idx} H-1 neighbors: {[j for j, _ in h1_nxt]}")
                            break

                print(f"\n  Total closure violations: {violations}")

                # STOP after first failure
                raise SystemExit(0)
