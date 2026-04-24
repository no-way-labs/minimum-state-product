#!/usr/bin/env python3
"""E19: A1'-violator probe at n=8 and n=9 — confirm no phase transition
at large-n regime (where LB sorry #2 lives).

Prior evidence:
- n=5 full-axiom: 789 attempts, 0 violators (probe_sk_a1prime_violator).
- n=5 instrumented: 225 attempts, 0 violators.
- n=5 Nodup-relaxed: 225 attempts, 0 violators.
- n=6 full-axiom: 279 attempts, 0 violators.
- n=7 selected: 0 violators (probe_sk_a1prime_n7).

Gap: n=8 and n=9 untested. This probe samples sparsely at both sizes to
confirm A1' has no phase transition. If CLEAN at n=8,9, one Lean proof
discharges both SlabCountingRing sorries #1 and #2.

Strategy: same violator search shape — pin det(p,L,S1,R)=det(p,L,S2,R)=v
for distinct S1≠S2, v∉{S1,S2}; DFS for a closed good cycle consistent with
the pinned det + coverage (all movers present) + det-consistency + Nodup.
"""
from __future__ import annotations

import json
import time
from itertools import product as iproduct


def enumerate_cycles(ms, n, L_max, tb, pinned, max_cycles):
    """DFS over closed good cycles with det extending `pinned`.

    Only keep cycles covering all positions; return at most max_cycles.
    """
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > tb: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1) % n]; Sp = config[p]; Rp = config[(p+1) % n]
            km = (p, Lp, Sp, Rp); forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1) % n]; Si = config[i]; Ri = config[(i+1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > tb: break
        dfs(start, start, dict(pinned), [start], [])
    return found


def audit(cyc, movers, n, p, L_val, R_val, S1, S2):
    L = len(movers); firings = []
    for k in range(L):
        if movers[k] != p: continue
        ck = cyc[k]
        if ck[(p-1) % n] == L_val and ck[(p+1) % n] == R_val:
            firings.append((k, ck[p]))
    s_vals = [s for (_, s) in firings]
    if S1 not in s_vals or S2 not in s_vals: return False
    targets = [(s, cyc[(k+1) % L][p]) for k, s in firings]
    t1 = [v for s, v in targets if s == S1]
    t2 = [v for s, v in targets if s == S2]
    return bool(t1) and bool(t2) and t1[0] == t2[0]


def run_trial(n, ms, L_max, tb_per_dfs, total_time_budget,
              max_cycles_per_pin=5, log=None):
    """Run the (p,L,R,S1,S2,v) sweep on one multiset.

    Returns (attempts, violators, violator_examples, elapsed, truncated).
    """
    attempts = 0; violators = 0; ex = []
    t0 = time.time(); truncated = False

    def emit(s):
        print(s, flush=True)
        if log is not None: log.write(s + "\n"); log.flush()

    emit(f"  --- n={n}, ms={ms}  (L_max={L_max}, tb/dfs={tb_per_dfs}s, "
         f"budget={total_time_budget}s) ---")
    for p in range(n):
        if ms[p] < 3: continue
        for L_val in range(ms[(p-1) % n]):
            for R_val in range(ms[(p+1) % n]):
                for S1 in range(ms[p]):
                    for S2 in range(S1 + 1, ms[p]):
                        for v in range(ms[p]):
                            if v == S1 or v == S2: continue
                            if time.time() - t0 > total_time_budget:
                                truncated = True
                                emit(f"    [time] truncated at attempts={attempts}"
                                     f"  elapsed={time.time()-t0:.1f}s")
                                return attempts, violators, ex, time.time()-t0, truncated
                            pinned = {
                                (p, L_val, S1, R_val): v,
                                (p, L_val, S2, R_val): v,
                            }
                            attempts += 1
                            cycles = enumerate_cycles(
                                ms, n, L_max, tb_per_dfs, pinned,
                                max_cycles_per_pin)
                            for cyc, movers, det in cycles:
                                if len(movers) < 2 * n: continue
                                if audit(cyc, movers, n, p, L_val, R_val, S1, S2):
                                    violators += 1
                                    if len(ex) < 5:
                                        ex.append({
                                            'n': n, 'ms': list(ms), 'p': p,
                                            'L': L_val, 'R': R_val,
                                            'S1': S1, 'S2': S2, 'v': v,
                                            'cycle': [list(c) for c in cyc],
                                            'movers': movers,
                                        })
                                    emit(f"    VIOLATOR: p={p} (L,R)=({L_val},{R_val}) "
                                         f"S1={S1} S2={S2} v={v}")
                                    break  # one per pin is enough
    emit(f"  done: attempts={attempts}  violators={violators}  "
         f"elapsed={time.time()-t0:.1f}s")
    return attempts, violators, ex, time.time() - t0, truncated


def enumerate_sub_threshold_multisets(n):
    """Return all sorted multisets (m_0<=...<=m_{n-1}) with m_i>=2,
    product < 4*3^(n-2) (sub-threshold regime)."""
    threshold = 4 * (3 ** (n - 2))
    out = []

    def rec(idx, cur_sorted, prod, min_next):
        if prod >= threshold: return
        if idx == n:
            out.append(tuple(cur_sorted))
            return
        for v in range(min_next, max(2, threshold // max(prod, 1)) + 2):
            if v < 2: continue
            if prod * v >= threshold and idx < n - 1:
                # allow last slot a chance — only break if even smallest fails
                pass
            if prod * (v ** (n - idx)) >= threshold and v > min_next:
                # if even filling the rest with v overshoots, stop increasing
                # (since sorted)
                break
            rec(idx + 1, cur_sorted + [v], prod * v, v)

    rec(0, [], 1, 2)
    return out


def pick_samples(n, k):
    """Pick a sample of up to k sub-threshold multisets (sorted tuples)
    spanning binary-dominant, mixed, and ternary-dominant shapes.
    Sub-threshold = product < 4*3^(n-2).

    Drops all-binary (no position has m_p>=3 → no A1' pins possible).
    Buckets by #binary and samples evenly across buckets.
    """
    all_ms = enumerate_sub_threshold_multisets(n)
    # Drop all-binary (no pinnable position)
    all_ms = [ms for ms in all_ms if any(x >= 3 for x in ms)]
    if not all_ms:
        return [], 0
    total = len(all_ms)
    # Bucket by #binary
    from collections import defaultdict
    buckets = defaultdict(list)
    for ms in all_ms:
        nb = sum(1 for x in ms if x == 2)
        buckets[nb].append(ms)
    bucket_keys = sorted(buckets.keys())
    sample = []
    # First pass: evenly across buckets
    per_bucket_target = max(1, k // max(1, len(bucket_keys)))
    for key in bucket_keys:
        bs = buckets[key]
        stride = max(1, len(bs) // per_bucket_target)
        picked = bs[::stride][:per_bucket_target]
        sample.extend(picked)
    # Second pass: fill remaining quota with uncovered multisets
    if len(sample) < k:
        seen = set(sample)
        for key in bucket_keys:
            for ms in buckets[key]:
                if ms not in seen:
                    sample.append(ms); seen.add(ms)
                    if len(sample) >= k: break
            if len(sample) >= k: break
    return sample[:k], total


def rotate_first_ge_3(ms):
    """Rotate ms so that ms[0] >= 3 if possible — ensures p=0 is a legal
    pin-target and spreads contexts nicely. Returns rotated tuple."""
    n = len(ms)
    for i in range(n):
        if ms[i] >= 3:
            return tuple(ms[i:] + ms[:i])
    return tuple(ms)


def main():
    out_log = "./probes/sk_phase0_out/e19_a1prime_n8_n9_2026-04-20.log"
    out_json = "./probes/sk_phase0_out/e19_a1prime_n8_n9_2026-04-20.json"

    log = open(out_log, "w")

    def emit(s):
        print(s, flush=True); log.write(s + "\n"); log.flush()

    emit("=" * 72)
    emit("E19: A1'-violator probe at n=8, n=9 (2026-04-20)")
    emit("=" * 72)

    t_global = time.time()
    # Global hard stop (seconds) — 18 minutes to stay under 20-min budget.
    HARD_STOP = 18 * 60

    # ---- n=8 ----
    n8_samples_k = 15
    n8_sample, n8_total = pick_samples(8, n8_samples_k)
    emit(f"\nn=8 sub-threshold multisets: {n8_total} total; sampling {len(n8_sample)}.")
    for ms in n8_sample:
        emit(f"  sample: {ms}")

    n8_attempts = 0; n8_violators = 0; n8_examples = []; n8_truncated = 0
    # Budget per multiset at n=8 — total n=8 share ~= 9 min = 540s
    n8_total_budget = 540
    per_ms_n8 = max(20, n8_total_budget // max(1, len(n8_sample)))

    emit(f"\n{'-'*72}\nn=8 trials (per-ms budget = {per_ms_n8}s)\n{'-'*72}")
    for ms in n8_sample:
        if time.time() - t_global > HARD_STOP * 0.55:
            emit(f"  [global] n=8 share exhausted; skipping remaining n=8 samples.")
            break
        ms_r = rotate_first_ge_3(ms)
        att, viol, ex, _, trunc = run_trial(
            n=8, ms=ms_r, L_max=18, tb_per_dfs=3.0,
            total_time_budget=per_ms_n8,
            max_cycles_per_pin=5, log=log)
        n8_attempts += att; n8_violators += viol; n8_examples.extend(ex)
        if trunc: n8_truncated += 1

    # ---- n=9 ----
    n9_samples_k = 10
    n9_sample, n9_total = pick_samples(9, n9_samples_k)
    emit(f"\nn=9 sub-threshold multisets: {n9_total} total; sampling {len(n9_sample)}.")
    for ms in n9_sample:
        emit(f"  sample: {ms}")

    n9_attempts = 0; n9_violators = 0; n9_examples = []; n9_truncated = 0
    # Whatever remains up to HARD_STOP
    remaining = HARD_STOP - (time.time() - t_global)
    per_ms_n9 = max(20, int(remaining // max(1, len(n9_sample))))
    emit(f"\n{'-'*72}\nn=9 trials (per-ms budget = {per_ms_n9}s, "
         f"remaining global = {remaining:.0f}s)\n{'-'*72}")
    for ms in n9_sample:
        if time.time() - t_global > HARD_STOP:
            emit(f"  [global] HARD_STOP reached; skipping remaining n=9 samples.")
            break
        ms_r = rotate_first_ge_3(ms)
        att, viol, ex, _, trunc = run_trial(
            n=9, ms=ms_r, L_max=20, tb_per_dfs=4.0,
            total_time_budget=per_ms_n9,
            max_cycles_per_pin=5, log=log)
        n9_attempts += att; n9_violators += viol; n9_examples.extend(ex)
        if trunc: n9_truncated += 1

    total_elapsed = time.time() - t_global
    total_violators = n8_violators + n9_violators

    emit(f"\n{'='*72}\nSUMMARY ({total_elapsed:.1f}s)\n{'='*72}")
    emit(f"  n=8: {n8_attempts} attempts, {n8_violators} violators "
         f"({len(n8_sample)}/{n8_total} multisets sampled, "
         f"{n8_truncated} time-truncated)")
    emit(f"  n=9: {n9_attempts} attempts, {n9_violators} violators "
         f"({len(n9_sample)}/{n9_total} multisets sampled, "
         f"{n9_truncated} time-truncated)")

    # Verdict
    if total_violators == 0:
        n8_cov = len(n8_sample) / max(1, n8_total)
        n9_cov = len(n9_sample) / max(1, n9_total)
        if n8_cov >= 0.80 and n9_cov >= 0.80 and n8_truncated == 0 and n9_truncated == 0:
            verdict = "CLEAN"
            msg = ("A1' has no phase transition at large n. "
                   "One Lean proof discharges sorries #1 and #2.")
        else:
            verdict = "BUDGET-LIMITED"
            msg = (f"No violators found but coverage incomplete "
                   f"(n=8 {n8_cov*100:.1f}%, n=9 {n9_cov*100:.1f}%, "
                   f"time-truncated n=8={n8_truncated}, n=9={n9_truncated}). "
                   "Consistent with no-phase-transition but not exhaustive.")
    else:
        verdict = "PHASE-TRANSITION"
        msg = (f"{total_violators} violator(s) found. A1' has a phase "
               "transition at large-n; Lean strategy must handle sorries "
               "#1 and #2 separately.")

    emit(f"\n  VERDICT: {verdict}")
    emit(f"  {msg}")

    if total_violators > 0:
        emit("\n  Violator examples:")
        for e in (n8_examples + n9_examples)[:5]:
            emit(f"    n={e['n']} ms={e['ms']} p={e['p']} "
                 f"(L,R)=({e['L']},{e['R']}) "
                 f"S1={e['S1']} S2={e['S2']} v={e['v']}")
            emit(f"      cycle: {e['cycle']}")
            emit(f"      movers: {e['movers']}")

    result = {
        'verdict': verdict,
        'message': msg,
        'elapsed_seconds': total_elapsed,
        'n8': {
            'total_sub_threshold_multisets': n8_total,
            'sampled': len(n8_sample),
            'samples': [list(x) for x in n8_sample],
            'attempts': n8_attempts,
            'violators': n8_violators,
            'time_truncated_count': n8_truncated,
            'examples': n8_examples,
        },
        'n9': {
            'total_sub_threshold_multisets': n9_total,
            'sampled': len(n9_sample),
            'samples': [list(x) for x in n9_sample],
            'attempts': n9_attempts,
            'violators': n9_violators,
            'time_truncated_count': n9_truncated,
            'examples': n9_examples,
        },
    }
    with open(out_json, "w") as f:
        json.dump(result, f, indent=2)
    emit(f"\n  Log:  {out_log}")
    emit(f"  JSON: {out_json}")
    log.close()


if __name__ == "__main__":
    main()
