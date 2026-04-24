#!/usr/bin/env python3
"""Exploration 2: VC forced graph structure for SK Lemma C.

After Exploration 1 killed the binary-only route, we need to understand the
full VC forced graph. Key questions:

1. Out-degree distribution: how many VC-NG configs have 0, 1, 2, ... edges?
2. Edge density: total edges vs |VC-NG| — is the graph always dense?
3. Cascade anatomy: how deep and wide is the cascade from round-0 sinks?
4. "Degree-2+ core": subset of configs with out-degree ≥ 2. Is it always
   ≥ 2^(n-1)? (These configs are cascade-resistant.)
5. The "guaranteed immune" argument: configs with out-degree ≥ 2 where
   at least one target also has out-degree ≥ 2. These are immune by
   construction (can't be peeled unless both targets are peeled first).
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
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


def analyze_vc_structure(ms, n, cycle, movers, det):
    """Full structural analysis of the VC forced graph."""
    L = len(movers)
    cycle_set = set(cycle)
    V = value_sets(cycle, n)

    # Move entries
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # VC configs
    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    # Build forced graph on VC-NG: out-edges for each config
    out_edges = defaultdict(list)  # c -> list of (target, position)
    in_edges = defaultdict(list)   # c -> list of (source, position)
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in vc_ng:
                    out_edges[c].append((nc, p))
                    in_edges[nc].append((c, p))

    # Out-degree distribution
    out_deg = Counter()
    for c in vc_ng:
        out_deg[len(out_edges[c])] += 1

    # Total edges
    total_edges = sum(len(out_edges[c]) for c in vc_ng)

    # Peel and track cascade
    remaining = set(vc_ng)
    round_counts = []
    total_peeled = 0
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in out_edges.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        round_counts.append(len(sinks))
        total_peeled += len(sinks)
        remaining -= sinks

    immune_core = remaining
    immune_size = len(immune_core)

    # Out-degree of immune core members (within immune core)
    immune_out_deg = Counter()
    for c in immune_core:
        deg = sum(1 for tgt, _ in out_edges.get(c, []) if tgt in immune_core)
        immune_out_deg[deg] += 1

    # "Degree-2+ core": configs with out-degree ≥ 2 in the full VC-NG graph
    deg2_core = set(c for c in vc_ng if len(out_edges[c]) >= 2)

    # Binary vs non-binary decomposition of immune core
    binary_immune = set(c for c in immune_core
                        if all(c[i] in (0, 1) for i in range(n)))
    nonbinary_immune = immune_core - binary_immune

    # Fire counts
    fc = [0] * n
    for m in movers:
        fc[m] += 1

    return {
        'L': L,
        'fc': fc,
        'vc_size': len(vc_all),
        'vc_ng': len(vc_ng),
        'total_edges': total_edges,
        'edge_density': total_edges / max(len(vc_ng), 1),
        'out_deg_dist': dict(out_deg),
        'deg0': out_deg.get(0, 0),
        'deg1': out_deg.get(1, 0),
        'deg2plus': sum(v for k, v in out_deg.items() if k >= 2),
        'immune_size': immune_size,
        'immune_min_outdeg': min(immune_out_deg.keys()) if immune_out_deg else -1,
        'cascade_rounds': len(round_counts),
        'cascade_profile': round_counts[:5],
        'deg2_core': len(deg2_core),
        'binary_immune': len(binary_immune),
        'nonbinary_immune': len(nonbinary_immune),
        'V_sizes': [len(V[i]) for i in range(n)],
    }


def main():
    print("=" * 72)
    print("Exploration 2: VC forced graph structure")
    print("=" * 72)

    plan = [
        (5, 1, 1500, 5.0, 16),
        (6, 2, 500, 3.0, 18),
        (7, 10, 200, 3.0, 18),
    ]

    by_nL = defaultdict(list)
    all_records = []

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===")
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                r = analyze_vc_structure(ms, n, cycle, movers, det)
                r['n'] = n
                r['ms'] = ms
                by_nL[(n, L)].append(r)
                all_records.append(r)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx + 1}/{len(sampled)}]  {elapsed:.0f}s")

    # === Summary tables ===
    print(f"\n{'=' * 72}")
    print("=== Edge density and degree distribution ===")
    print(f"  n  L   count  |VC_NG|  edges   density  "
          f"deg0    deg1    deg2+   immune  2^(n-1)  slack")
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        mn_imm = min(r['immune_size'] for r in rs)
        target = 2 ** (n - 1)
        slack = mn_imm - target
        flag = " !" if mn_imm < target else ""
        print(f"  {n}  {L:2d}  {N:5d}  {avg('vc_ng'):6.0f}  "
              f"{avg('total_edges'):6.0f}  {avg('edge_density'):7.2f}  "
              f"{avg('deg0'):6.1f}  {avg('deg1'):6.1f}  {avg('deg2plus'):6.1f}  "
              f"{mn_imm:6d}  {target:6d}  {slack:+5d}{flag}")

    # === Cascade analysis ===
    print(f"\n=== Cascade profile (avg rounds and sinks per round) ===")
    for (n, L) in sorted(by_nL.keys()):
        if L not in (2 * n, 2 * n + 2, 2 * n + 4):
            continue
        rs = by_nL[(n, L)]
        avg_rounds = sum(r['cascade_rounds'] for r in rs) / len(rs)
        # Average first few round sizes
        max_rounds = max(r['cascade_rounds'] for r in rs)
        avg_profiles = []
        for rd in range(min(5, max_rounds)):
            vals = [r['cascade_profile'][rd] for r in rs if rd < len(r['cascade_profile'])]
            if vals:
                avg_profiles.append(f"{sum(vals)/len(vals):.1f}")
        print(f"  n={n} L={L}: avg_rounds={avg_rounds:.1f}  "
              f"profile=[{', '.join(avg_profiles)}]")

    # === Deg2+ core analysis ===
    print(f"\n=== Degree-2+ core (cascade-resistant configs) ===")
    print(f"  n  L   count  |deg2+|   min_d2  2^(n-1)  d2_slack  "
          f"|immune|  min_imm")
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        min_d2 = min(r['deg2plus'] for r in rs)
        mn_imm = min(r['immune_size'] for r in rs)
        target = 2 ** (n - 1)
        d2_flag = " !" if min_d2 < target else ""
        print(f"  {n}  {L:2d}  {N:5d}  {avg('deg2plus'):7.0f}  {min_d2:7d}  "
              f"{target:6d}  {min_d2 - target:+7d}  "
              f"{avg('immune_size'):7.0f}  {mn_imm:7d}{d2_flag}")

    # === Binary vs non-binary immune decomposition ===
    print(f"\n=== Binary vs non-binary immune decomposition ===")
    for (n, L) in sorted(by_nL.keys()):
        if L not in (2 * n, 2 * n + 2, 2 * n + 4):
            continue
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        print(f"  n={n} L={L}: binary_immune={avg('binary_immune'):.1f}  "
              f"nonbinary_immune={avg('nonbinary_immune'):.1f}  "
              f"total={avg('immune_size'):.1f}  "
              f"V_sizes_avg={[round(sum(r['V_sizes'][i] for r in rs)/N, 1) for i in range(n)]}")

    # === Min immune configs: characterize hardest cases ===
    print(f"\n=== Hardest cases (lowest immune core relative to 2^(n-1)) ===")
    sorted_records = sorted(all_records,
                           key=lambda r: r['immune_size'] - 2 ** (r['n'] - 1))
    for r in sorted_records[:8]:
        n = r['n']
        slack = r['immune_size'] - 2 ** (n - 1)
        print(f"  n={n} L={r['L']} ms={r['ms']} immune={r['immune_size']} "
              f"slack={slack} vc_ng={r['vc_ng']} deg0={r['deg0']} "
              f"deg1={r['deg1']} V={r['V_sizes']} fc={r['fc']}")

    # === Violations ===
    violations = sum(1 for r in all_records if r['immune_size'] < 2 ** (r['n'] - 1))
    print(f"\n  VC IMMUNE CORE >= 2^(n-1): "
          f"{'HOLDS' if violations == 0 else f'VIOLATED ({violations})'} "
          f"({len(all_records)} records)")


if __name__ == "__main__":
    main()
