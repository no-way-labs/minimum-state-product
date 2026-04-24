#!/usr/bin/env python3
"""
ORBIT PRIVILEGE PRESERVATION — COMPREHENSIVE VERIFICATION

For each good cycle instance, find ALL shadow orbits (not just one)
and verify that EVERY config on EVERY orbit has at least one
forced-privileged proc.

Also check: does every forced orbit (from any starting non-good config
with a forced-privileged proc) preserve privilege? Or only specific ones?
"""

import itertools, time, sys
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

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
    seen = set(); unique = []
    for w in results:
        canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
        if canon not in seen: seen.add(canon); unique.append(w)
    return unique

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


def analyze_all_orbits(ms, n, word, configs):
    """
    From EVERY possible non-good starting config (g_0 shifted),
    follow the forced orbit and classify:
    - Does the orbit close at length CL?
    - Does the orbit close at some other length?
    - Does the orbit halt (no forced-priv proc)?
    - Does every orbit config have privilege?
    """
    CL = len(configs)
    good_set = set(configs)

    mct = {}
    for s in range(CL):
        p = word[s]; c = configs[s]
        L, S, R = get_context(c, p, n)
        Sp = configs[(s+1) % CL][p]
        key = (p, L, S, R)
        if key in mct: return None
        mct[key] = Sp

    def forced_privileged(c):
        result = []
        for p in range(n):
            L, S, R = get_context(c, p, n)
            key = (p, L, S, R)
            if key in mct and mct[key] != S:
                result.append((p, key))
        return result

    g0 = configs[0]
    stats = {
        "starts_tried": 0,
        "starts_with_fp": 0,
        "orbits_close_CL": 0,
        "orbits_close_other": 0,
        "orbits_halt": 0,
        "orbits_too_long": 0,
        "all_privileged_on_CL_orbits": 0,
        "privilege_failure": 0,
        "halt_steps": [],
    }

    for q in range(n):
        for d in range(1, ms[q]):
            c0 = list(g0); c0[q] = (c0[q] + d) % ms[q]; c0 = tuple(c0)
            if c0 in good_set: continue
            stats["starts_tried"] += 1

            fp0 = forced_privileged(c0)
            if not fp0: continue
            stats["starts_with_fp"] += 1

            # Follow orbit
            orbit = [c0]
            orbit_set = {c0}
            fp_counts = [len(fp0)]
            cur = c0
            halted = False
            closed = False
            cycle_len = 0

            for step in range(CL * 3):
                fps = forced_privileged(cur)
                if not fps:
                    halted = True
                    stats["orbits_halt"] += 1
                    stats["halt_steps"].append(step)
                    break
                p, key = fps[0]
                nxt = list(cur); nxt[p] = mct[key]; nxt = tuple(nxt)
                if nxt in good_set:
                    # Shouldn't happen
                    break
                if nxt in orbit_set:
                    # Found cycle
                    idx = orbit.index(tuple(nxt))
                    cycle_len = len(orbit) - idx
                    if cycle_len == CL:
                        stats["orbits_close_CL"] += 1
                        # Check privilege on the cycle part
                        cycle_fp = fp_counts[idx:]
                        if all(c > 0 for c in cycle_fp):
                            stats["all_privileged_on_CL_orbits"] += 1
                        else:
                            stats["privilege_failure"] += 1
                    else:
                        stats["orbits_close_other"] += 1
                    closed = True
                    break
                orbit.append(tuple(nxt))
                orbit_set.add(tuple(nxt))
                fp_nxt = forced_privileged(tuple(nxt))
                fp_counts.append(len(fp_nxt))
                cur = tuple(nxt)

            if not halted and not closed:
                stats["orbits_too_long"] += 1

    return stats


print("=" * 70)
print("COMPREHENSIVE ORBIT PRIVILEGE ANALYSIS")
print("=" * 70)

sys.setrecursionlimit(5000)

test_cases = [
    (9, [2, 3, 3, 2, 3, 3, 2, 3, 3], "n=9, binary at {0,3,6}"),
    (7, [2, 2, 2, 3, 3, 3, 3], "n=7, 3 consecutive binary"),
]

for n, ms, desc in test_cases:
    CL = sum(ms)
    print(f"\n--- {desc}, CL={CL} ---")

    words = enumerate_sweep_words(ms, n)
    all_combos = {p: enumerate_value_sequences(ms[p], ms[p]) for p in range(n)}

    grand_stats = defaultdict(int)

    for w in words[:2]:  # first 2 words for speed
        combo_lists = [all_combos[p] for p in range(n)]
        for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
            combo = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
            cfgs = build_cycle(ms, n, w, combo)
            if cfgs is None: continue

            stats = analyze_all_orbits(ms, n, w, cfgs)
            if stats is None: continue

            for k, v in stats.items():
                if k != "halt_steps":
                    grand_stats[k] += v if isinstance(v, int) else 0

    print(f"  Results:")
    for k in sorted(grand_stats.keys()):
        print(f"    {k}: {grand_stats[k]}")
