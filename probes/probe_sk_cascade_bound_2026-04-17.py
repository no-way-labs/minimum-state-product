#!/usr/bin/env python3
"""Probe the peel-fringe size on canonical and noncanonical families.

Targets:
1. Canonical 4-binary stutter family at n=9..13 via explicit mover word +
   state-sequence search.
2. Two noncanonical exact-fire-count families at n=9,10,11.

Reports:
- |T(c*)|
- peel cascade size
- whether cascade size exceeds n-2
- whether c* survives peel
"""

from collections import Counter, defaultdict, deque
import importlib.util
import itertools
import json
import os


_HERE = os.path.dirname(os.path.abspath(__file__))
_EXTRACT_PATH = os.path.join(_HERE, "probe_sk_2n2_loop_extract_2026-04-17.py")
_DEADEND_PATH = os.path.join(_HERE, "probe_sk_deadend_peel_2026-04-17.py")

_spec = importlib.util.spec_from_file_location("probe_extract", _EXTRACT_PATH)
probe_extract = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe_extract)

_spec2 = importlib.util.spec_from_file_location("probe_dead", _DEADEND_PATH)
probe_dead = importlib.util.module_from_spec(_spec2)
_spec2.loader.exec_module(probe_dead)


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
                dfs(seq, remaining - 1)
                seq.pop()

    dfs([0], k)
    return seqs


def build_configs_from_word(ms, word, state_seqs):
    n = len(ms)
    pcs = [0] * n
    state = [0] * n
    cfgs = []
    for p in word:
        cfgs.append(tuple(state))
        pcs[p] += 1
        state[p] = state_seqs[p][pcs[p]]
    return cfgs


def check_consistency_and_det(cfgs, word):
    n = len(cfgs[0])
    L = len(word)
    det = {}
    for idx in range(L):
        c = cfgs[idx]
        cn = cfgs[(idx + 1) % L]
        mover = word[idx]
        diffs = [j for j in range(n) if c[j] != cn[j]]
        if diffs != [mover]:
            return False, None
        for i in range(n):
            key = (i, c[(i - 1) % n], c[i], c[(i + 1) % n])
            out = cn[i]
            if key in det and det[key] != out:
                return False, None
            det[key] = out
    if len(set(cfgs)) != L:
        return False, None
    return True, det


def canonical_word_4b(n):
    return [0, 1, 2, 3, 4, 4, 5, 4, 5] + list(range(6, n)) + list(range(n))


def enumerate_exact_fc_words(ms, n, target_fc, cap=300000):
    ring_adj = {p: [(p - 1) % n, (p + 1) % n] for p in range(n)}
    total_len = sum(target_fc[p] for p in range(n))
    results = []

    def dfs(word, fc):
        if len(results) >= cap:
            return
        if len(word) == total_len:
            if abs(word[-1] - word[0]) % n in (1, n - 1):
                config = [0] * n
                for p in word:
                    config[p] = (config[p] + 1) % ms[p]
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


def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def build_cycle_incrementing(ms, word):
    n = len(ms)
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def first_valid_cycle_from_word(ms, word):
    n = len(ms)
    fc = [0] * n
    for p in word:
        fc[p] += 1
    choices = [enumerate_state_sequences(ms[p], fc[p]) for p in range(n)]
    for combo in itertools.product(*choices):
        cfgs = build_configs_from_word(ms, word, combo)
        ok, det = check_consistency_and_det(cfgs, word)
        if ok:
            return cfgs, det, combo
    return None, None, None


def first_witnessed_cycle_from_word(ms, word):
    cycle, det, combo = first_valid_cycle_from_word(ms, word)
    if cycle is None:
        return None, None, None
    rec = probe_extract.analyze_cycle_record(len(ms), tuple(ms), cycle, det)
    if rec is None:
        return None, None, None
    return cycle, det, combo


def first_valid_exactfc_cycle(ms):
    n = len(ms)
    target = {i: ms[i] for i in range(n)}
    words = enumerate_exact_fc_words(ms, n, target)
    seen = set()
    for w in words:
        canon = canonicalize_word(w)
        if canon in seen:
            continue
        seen.add(canon)
        cycle = build_cycle_incrementing(ms, w)
        if cycle is None:
            continue
        ok, det = check_consistency_and_det(cycle, list(w))
        if ok:
            return list(w), cycle, det
    return None, None, None


def first_witnessed_exactfc_cycle(ms):
    n = len(ms)
    target = {i: ms[i] for i in range(n)}
    words = enumerate_exact_fc_words(ms, n, target)
    seen = set()
    for w in words:
        canon = canonicalize_word(w)
        if canon in seen:
            continue
        seen.add(canon)
        cycle = build_cycle_incrementing(ms, w)
        if cycle is None:
            continue
        ok, det = check_consistency_and_det(cycle, list(w))
        if not ok:
            continue
        rec = probe_extract.analyze_cycle_record(n, tuple(ms), cycle, det)
        if rec is not None:
            return list(w), cycle, det
    return None, None, None


def summarize_analysis(tag, n, ms, cycle, det):
    rec = probe_extract.analyze_cycle_record(n, tuple(ms), cycle, det)
    rec["cycle_index"] = 0
    a = probe_dead.analyze_record(rec)
    cascade = sum(a["peel_round_sizes"])
    return {
        "tag": tag,
        "n": n,
        "ms": list(ms),
        "good_word": a["good_word"],
        "c_star": a["c_star"],
        "q0": a["q0"],
        "T_size": rec["T_size"],
        "core_size": a["core_size"],
        "cascade_size": cascade,
        "zero_nodes": a["zero_nodes"],
        "peel_round_sizes": a["peel_round_sizes"],
        "peel_round_nodes": a["peel_round_nodes"],
        "lex_word": a["lex_word"],
    }


def main():
    out_dir = os.path.join(_HERE, "sk_cascade_bound_out")
    os.makedirs(out_dir, exist_ok=True)

    records = []

    # Canonical 4-binary family, explicit word
    for n in [9, 10, 11, 12, 13]:
        ms = [2, 2, 2, 2] + [3] * (n - 4)
        word = canonical_word_4b(n)
        cycle, det, combo = first_witnessed_cycle_from_word(ms, word)
        if cycle is None:
            raise RuntimeError(f"no valid canonical 4b cycle at n={n}")
        records.append(summarize_analysis("canonical_4b", n, ms, cycle, det))

    # Noncanonical families
    noncanonical = {
        9: [
            ("3b_spaced", [2, 3, 3, 2, 3, 3, 2, 3, 3]),
            ("5b_consec", [2, 2, 2, 2, 2, 3, 3, 3, 3]),
        ],
        10: [
            ("split_233233", [2, 2, 3, 3, 2, 3, 3, 2, 3, 3]),
            ("split_233223", [2, 3, 3, 2, 2, 3, 3, 2, 3, 3]),
        ],
        11: [
            ("3b_spaced", [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3]),
            ("5b_consec", [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3]),
        ],
    }

    for n, fams in noncanonical.items():
        for tag, ms in fams:
            word, cycle, det = first_witnessed_exactfc_cycle(ms)
            if cycle is None:
                raise RuntimeError(f"no valid cycle for {tag} at n={n}")
            records.append(summarize_analysis(tag, n, ms, cycle, det))

    out_json = os.path.join(out_dir, "records.json")
    with open(out_json, "w") as f:
        json.dump(records, f, indent=2)

    print("=" * 80)
    print("Cascade-bound probe summary")
    print("=" * 80)
    by_n = defaultdict(list)
    for r in records:
        by_n[r["n"]].append(r)
        if r["cascade_size"] > r["n"] - 2:
            print(f"DISQUALIFYING: {r['tag']} n={r['n']} cascade={r['cascade_size']} > n-2", flush=True)
            print(json.dumps(r, indent=2), flush=True)
            return

    for n in sorted(by_n):
        print(f"\nn={n}")
        for r in by_n[n]:
            print(
                f"  {r['tag']}: T={r['T_size']} core={r['core_size']} "
                f"cascade={r['cascade_size']} n-2={n-2} q0={r['q0']}",
                flush=True,
            )
            print(f"    dead_end={r['zero_nodes']}", flush=True)
            print(f"    peel_round_sizes={r['peel_round_sizes']}", flush=True)

    print(f"\njson: {out_json}", flush=True)


if __name__ == "__main__":
    main()
