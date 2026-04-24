#!/usr/bin/env python3
"""Cascade budget probe: tighten the core-shrinkage bound.

At L=2n+k, the k extra fires create "cross-edges" from binary configs
to non-binary configs. When non-binary sinks peel, binary configs that
RELIED on cross-edges may cascade into sinks.

A binary config c is vulnerable to cascade iff:
  - It has at least one cross-edge (to a non-binary target)
  - ALL of its binary-internal edges (to binary NG targets) are
    eventually peeled too

The IMMUNE core = binary configs whose binary-internal edges form a
closed subgraph. A config is immune iff it has ≥1 edge to another
immune config.

This probe computes for each cycle at L >= 2n+2:
  1. |binary NG configs|
  2. |binary configs with ≥1 binary-internal edge| (= "round-0 immune")
  3. |binary configs with ONLY cross-edges| (= "immediately vulnerable")
  4. The actual immune core after full peeling restricted to binary subgraph
  5. |immune core| vs 2^(n-1)
  6. Per extra fire: how many binary configs does each cross-edge affect?
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


def analyze_cascade(ms, n, cycle, movers, det):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycle_set = set(cycle)
    ng = set(c for c in all_configs if c not in cycle_set)
    V = value_sets(cycle, n)

    def is_value_compat(c):
        return all(c[i] in V[i] for i in range(n))

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # Separate binary NG from non-binary NG
    binary_ng = set(c for c in ng if is_value_compat(c))
    nonbinary_ng = ng - binary_ng

    # For each binary NG config, classify its forced edges
    # as "binary-internal" (target in binary_ng) or "cross" (target in nonbinary or cycle)
    binary_internal_edges = defaultdict(list)  # c -> [targets in binary_ng]
    cross_edges = defaultdict(list)            # c -> [targets NOT in binary_ng]
    no_edge_binary = set()

    for c in binary_ng:
        has_any = False
        for p in range(n):
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                has_any = True
                if nc in binary_ng:
                    binary_internal_edges[c].append(nc)
                else:
                    cross_edges[c].append(nc)
        if not has_any:
            no_edge_binary.add(c)

    # Classify binary configs
    has_internal = set(c for c in binary_ng if binary_internal_edges[c])
    only_cross = set(c for c in binary_ng if not binary_internal_edges[c]
                     and cross_edges[c])
    # no_edge_binary already computed

    # Compute the immune core: peel the binary subgraph
    # (remove binary configs whose binary-internal edges all point outside remaining)
    remaining = set(binary_ng)
    binary_rounds = 0
    binary_peeled = 0
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in binary_internal_edges.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        binary_peeled += len(sinks)
        binary_rounds += 1
        remaining -= sinks

    immune_core = remaining
    cascade_loss = len(binary_ng) - len(no_edge_binary) - len(immune_core)

    # How many cross-edge entries are there? (det entries whose output is non-binary)
    cross_det_entries = 0
    for (p, Lv, Sv, Rv), val in move_entries.items():
        if val not in V[p] or Lv not in V[(p-1)%n] or Rv not in V[(p+1)%n]:
            continue  # context itself is non-binary — won't match binary configs
        if val in V[p]:
            # Target value is in the value set — stays binary
            pass
        else:
            cross_det_entries += 1

    # Actually, an edge is cross if TARGET config is non-binary.
    # The target changes c[p] to val. If val ∉ V[p], target is non-binary.
    # Also if val ∈ V[p] but target is in cycle, that's also "lost."
    cross_by_nonbinary_val = 0
    cross_by_in_cycle = 0
    for c in binary_ng:
        for p in range(n):
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in move_entries:
                val = move_entries[key]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                nc = tuple(nc)
                if nc not in binary_ng:
                    if val not in V[p]:
                        cross_by_nonbinary_val += 1
                    elif nc in cycle_set:
                        cross_by_in_cycle += 1

    return {
        'binary_ng': len(binary_ng),
        'nonbinary_ng': len(nonbinary_ng),
        'has_internal': len(has_internal),
        'only_cross': len(only_cross),
        'no_edge': len(no_edge_binary),
        'immune_core': len(immune_core),
        'cascade_loss': cascade_loss,
        'binary_rounds': binary_rounds,
        'binary_peeled': binary_peeled,
        'cross_nonbinary': cross_by_nonbinary_val,
        'cross_in_cycle': cross_by_in_cycle,
    }


def main():
    print("=" * 72, flush=True)
    print("Cascade budget: immune binary core analysis", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1, 1500, 5.0, 15),
        (6, 4, 500, 3.0, 17),
        (7, 20, 150, 3.0, 17),
    ]

    by_nL = defaultdict(list)

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                r = analyze_cascade(ms, n, cycle, movers, det)
                r['L'] = L
                by_nL[(n, L)].append(r)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s", flush=True)

    print(f"\n{'='*72}", flush=True)
    print(f"=== Immune core vs 2^(n-1) ===", flush=True)
    print(f"  n  L   count  avg_binNG  avg_immune  min_immune  2^(n-1)  "
          f"slack  avg_loss  avg_only_cross  avg_no_edge", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        mn_imm = min(r['immune_core'] for r in rs)
        target = 2 ** (n - 1)
        slack = mn_imm - target
        flag = " !" if mn_imm < target else ""
        print(f"  {n}  {L:2d}  {N:5d}  {avg('binary_ng'):9.0f}  "
              f"{avg('immune_core'):10.1f}  {mn_imm:10d}  {target:6d}  "
              f"{slack:+5d}  {avg('cascade_loss'):8.1f}  "
              f"{avg('only_cross'):14.1f}  {avg('no_edge'):11.1f}{flag}",
              flush=True)

    # Cross-edge breakdown
    print(f"\n=== Cross-edge breakdown (L=2n and L=2n+2) ===", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        if L not in (2*n, 2*n+2):
            continue
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        print(f"  n={n}  L={L}:  cross_nonbinary={avg('cross_nonbinary'):.1f}  "
              f"cross_in_cycle={avg('cross_in_cycle'):.1f}  "
              f"binary_rounds={avg('binary_rounds'):.1f}  "
              f"binary_peeled={avg('binary_peeled'):.1f}", flush=True)

    # Focus: the immune_core hypothesis
    total_violations = 0
    total_records = 0
    for (n, L) in sorted(by_nL.keys()):
        for r in by_nL[(n, L)]:
            total_records += 1
            if r['immune_core'] < 2 ** (n - 1):
                total_violations += 1
    print(f"\n  IMMUNE CORE >= 2^(n-1) hypothesis: "
          f"{'HOLDS' if total_violations == 0 else f'VIOLATED ({total_violations})'} "
          f"({total_records} records)", flush=True)


if __name__ == "__main__":
    main()
