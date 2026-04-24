#!/usr/bin/env python3
"""Immune core drop analysis: what configs are lost at L > 2n?

At n=6: immune_core goes from 52 (L=12) to min 45 (L=14).
7 configs lost. What are they? Are they:
(a) Configs that were no-edge at L=2n but had-edge at L=2n+2?
    (impossible — different cycles/dets)
(b) Configs that are no-edge because the det's contexts shifted?
(c) Configs caught in the cascade from extra-value sinks?

This probe directly compares the immune core composition:
- At L=2n: which configs survive? All binary NG minus Z.
- At L=2n+2 (same multiset): which configs survive?
  How many are in the "strictly binary" subcube?
  How many use extra values?

The KEY question: is the strictly-binary immune core at L=2n+2
always ≥ the strictly-binary immune core at L=2n (= Lemma A value)?
If so, the proof is: extra fires only add to the binary core, never
subtract.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time

def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)

def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out

def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def compute_immune_core(ms, n, cycle, det, V):
    """Compute the immune core within the value-compatible subgraph."""
    cycle_set = set(cycle)
    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # Build forced graph within VC_NG
    adj = defaultdict(list)
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in vc_ng:
                    adj[c].append(nc)

    # Peel
    remaining = set(vc_ng)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    return remaining, vc_ng


def main():
    print("=" * 72, flush=True)
    print("Immune core drop analysis", flush=True)
    print("=" * 72, flush=True)

    # Focus on n=5 and n=6 where we have data
    for n in [5, 6]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        print(f"\n=== n={n}  {len(multisets)} multisets ===", flush=True)

        # For each multiset, find cycles at L=2n AND L=2n+2,
        # compare the strictly-binary immune core
        t0 = time.time()
        records = []
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, 2*n+3, 5.0, 500)
            by_L = defaultdict(list)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L in (2*n, 2*n+2):
                    by_L[L].append((cycle, movers, det))

            for cycle, movers, det in by_L.get(2*n+2, [])[:5]:
                L = len(movers)
                V = value_sets(cycle, n)
                immune, vc_ng = compute_immune_core(ms, n, cycle, det, V)

                # Strictly binary subcube: configs using only first 2 values at each pos
                primary = [sorted(V[i])[:2] for i in range(n)]
                strictly_binary = set(iproduct(*primary))
                sb_ng = strictly_binary - set(cycle)
                sb_immune = immune & strictly_binary

                records.append({
                    'ms': ms, 'L': L,
                    'vc_ng': len(vc_ng),
                    'immune': len(immune),
                    'sb_total': len(strictly_binary),
                    'sb_ng': len(sb_ng),
                    'sb_immune': len(sb_immune),
                    'extra_immune': len(immune - strictly_binary),
                })

            if (idx + 1) % 10 == 0:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(multisets)}]  {elapsed:.0f}s  "
                      f"records={len(records)}", flush=True)

        # Report
        if not records:
            print(f"  no L={2*n+2} cycles found", flush=True)
            continue

        target = 2 ** (n - 1)
        lemma_a_val = 2**n - 2*n - (2 if n % 2 == 1 else 0)
        print(f"\n  Lemma A value = {lemma_a_val}, target = {target}", flush=True)
        print(f"  L={2*n+2} records: {len(records)}", flush=True)

        # Key question: is sb_immune always >= target?
        min_sb_immune = min(r['sb_immune'] for r in records)
        min_immune = min(r['immune'] for r in records)
        avg_sb_immune = sum(r['sb_immune'] for r in records) / len(records)
        avg_extra = sum(r['extra_immune'] for r in records) / len(records)

        print(f"\n  Strictly-binary immune core at L={2*n+2}:", flush=True)
        print(f"    min  = {min_sb_immune} (target {target}, slack {min_sb_immune - target:+d})",
              flush=True)
        print(f"    avg  = {avg_sb_immune:.1f}", flush=True)
        print(f"    avg extra-value immune = {avg_extra:.1f}", flush=True)
        print(f"    min total immune = {min_immune} (slack {min_immune - target:+d})",
              flush=True)

        sb_ge_target = sum(1 for r in records if r['sb_immune'] >= target)
        print(f"    sb_immune >= {target}: {sb_ge_target}/{len(records)} "
              f"({100*sb_ge_target/len(records):.1f}%)", flush=True)

        sb_ge_lemma_a = sum(1 for r in records if r['sb_immune'] >= lemma_a_val)
        print(f"    sb_immune >= Lemma A ({lemma_a_val}): {sb_ge_lemma_a}/{len(records)} "
              f"({100*sb_ge_lemma_a/len(records):.1f}%)", flush=True)

        # Show the worst cases
        worst = sorted(records, key=lambda r: r['sb_immune'])[:3]
        print(f"\n  Worst cases:", flush=True)
        for r in worst:
            print(f"    ms={r['ms']}  sb_immune={r['sb_immune']}  "
                  f"extra={r['extra_immune']}  total_immune={r['immune']}  "
                  f"sb_ng={r['sb_ng']}  vc_ng={r['vc_ng']}", flush=True)


if __name__ == "__main__":
    main()
