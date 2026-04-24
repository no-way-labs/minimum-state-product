#!/usr/bin/env python3
"""
Supplementary verification: confirm that
  (1) The orbit ALWAYS has length exactly CL (never shorter).
  (2) At each step, there is exactly 1 forced-privileged proc (determinism).
  (3) The orbit uses each mover entry exactly once.

These three facts together with the theorem give:
  - The orbit is well-defined (unique next step).
  - It runs for CL steps (never halts early).
  - Each step has a forced-privileged proc (the theorem).
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

def detailed_orbit_analysis(ms, n, word, configs):
    CL = len(configs)
    good_set = set(configs)

    mct = {}
    mct_step = {}  # maps entry key -> good cycle step index
    for s in range(CL):
        p = word[s]; c = configs[s]
        L, S, R = get_context(c, p, n)
        Sp = configs[(s+1) % CL][p]
        key = (p, L, S, R)
        if key in mct: return None
        mct[key] = Sp
        mct_step[key] = s

    def forced_privileged(c):
        result = []
        for p in range(n):
            L, S, R = get_context(c, p, n)
            key = (p, L, S, R)
            if key in mct and mct[key] != S:
                result.append((p, key))
        return result

    # Use g_0 shifted at farthest proc from mover
    g0 = configs[0]
    w0 = word[0]
    # Pick q far from w0 (ring distance > 1)
    q = None
    for qq in range(n):
        d = min(abs(qq - w0), n - abs(qq - w0))
        if d > 1:
            q = qq
            break
    if q is None:
        return None
    c0 = list(g0); c0[q] = (c0[q] + 1) % ms[q]; c0 = tuple(c0)
    if c0 in good_set:
        return None

    fp0 = forced_privileged(c0)
    if not fp0:
        return None

    # Follow orbit, recording detailed info
    orbit = [c0]
    fp_counts = [len(fp0)]  # privilege count at each orbit config
    entries_used = []
    steps_matched = []
    cur = c0

    for step in range(CL + 5):
        fps = forced_privileged(cur)
        if not fps:
            return {"halted_at": step, "orbit_len": len(orbit)}
        # Record this step's privilege count (should match fp_counts[-1])
        p, key = fps[0]
        entries_used.append(key)
        steps_matched.append(mct_step[key])
        nxt = list(cur); nxt[p] = mct[key]; nxt = tuple(nxt)
        if nxt in good_set:
            return {"reached_good_at": step}
        if nxt == c0:
            return {
                "orbit_len": step + 1,
                "expected_CL": CL,
                "fp_counts": fp_counts,
                "min_fp": min(fp_counts),
                "max_fp": max(fp_counts),
                "unique_entries": len(set(entries_used)),
                "is_permutation": sorted(steps_matched) == list(range(CL)),
                "deterministic": all(c == 1 for c in fp_counts),
            }
        # Record privilege count for the NEW config nxt
        fp_nxt = forced_privileged(nxt)
        fp_counts.append(len(fp_nxt))
        orbit.append(nxt)
        cur = nxt

    return {"did_not_close": True, "orbit_len": len(orbit)}


print("=" * 70)
print("DETAILED ORBIT ANALYSIS")
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

    total = 0
    len_CL = 0
    all_perm = 0
    all_det = 0  # all steps had exactly 1 forced-privileged proc
    multi_fp = 0  # some step had >1 forced-privileged proc

    for w in words:
        combo_lists = [all_combos[p] for p in range(n)]
        for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
            combo = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
            cfgs = build_cycle(ms, n, w, combo)
            if cfgs is None: continue

            r = detailed_orbit_analysis(ms, n, w, cfgs)
            if r is None: continue
            total += 1
            if total <= 3:
                print(f"  DEBUG r={r}")

            if "orbit_len" in r and r.get("expected_CL"):
                if r["orbit_len"] == r["expected_CL"]:
                    len_CL += 1
                if r.get("is_permutation"):
                    all_perm += 1
                if r.get("deterministic"):
                    all_det += 1
                if r.get("max_fp", 0) > 1:
                    multi_fp += 1

    print(f"  Total instances: {total}")
    print(f"  Orbit length = CL: {len_CL}/{total}")
    print(f"  Entries form permutation: {all_perm}/{total}")
    print(f"  Always exactly 1 forced-priv proc: {all_det}/{total}")
    print(f"  Some step with >1 forced-priv proc: {multi_fp}/{total}")

print("\n" + "=" * 70)
