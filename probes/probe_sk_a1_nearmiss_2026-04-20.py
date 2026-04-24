#!/usr/bin/env python3
"""E10: A1 near-miss probe.

A1 collision = two cycle steps k1 != k2 with same mover p and matching
local triple (L, S, R) at p. Empirically 0 collisions in 1190 cycles.

A1 near-miss = two steps with same mover p and Hamming-distance-1 on
(L, S, R). Which coordinate "protects" A1 across near-misses?

METRICS per cycle (restricted to min_case_C >= 4 / twist-regime records):
  same_mover_pairs  : pairs (k1, k2), k1 < k2, moverAt(k1) == moverAt(k2)
  collisions        : full-triple match (should be 0)
  near_miss_1       : Hamming-distance-1 on (L, S, R)
  protecting_coord  : per near-miss, which coord in {L, S, R} differs
  near_miss_positions : (k1, k2) cycle indices of each near-miss
  shallow_escape_indices : cycle indices that host a shallow escape

CORRELATION: does near-miss concentration co-locate with shallow-escape
vertices?

Pre-commit tripwire (from exploration log E10):
  T1. 0 near-misses in >=90% of records -> probe dies.
  T2. uniform coord distribution -> no single-axiom handle.
  T3. skewed coord distribution -> load-bearing coord identified.
  T4. near-miss count correlates with shallow-escape count (rho > 0.5)
      -> candidate mechanism (c) survives.
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct


def m_n(n):
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product: out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product: break
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen_cycles = set(); t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def build_tube(ms, n, cycle, movers, det):
    L = len(movers); V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n): V[q].add(c[q])
    V_list = [sorted(s) for s in V]; cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    T = set()
    for c in cycle:
        for q in range(n):
            for v in V_list[q]:
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set: T.add(nc)
    adj_edge = defaultdict(list)
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]; nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in T: adj_edge[c].append((nc, p))
    return T, dict(adj_edge), cycle_set, L, move_entries


def tarjan_scc(V, adj_plain):
    idx = {}; lowlink = {}; on_stack = set(); stack = []; counter = [0]; sccs = []
    def strongconnect(root):
        work = [(root, iter(adj_plain.get(root, [])))]
        idx[root] = counter[0]; lowlink[root] = counter[0]; counter[0] += 1
        stack.append(root); on_stack.add(root)
        while work:
            v, it = work[-1]
            try: w = next(it)
            except StopIteration:
                work.pop()
                if lowlink[v] == idx[v]:
                    comp = []
                    while True:
                        x = stack.pop(); on_stack.discard(x); comp.append(x)
                        if x == v: break
                    sccs.append(frozenset(comp))
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[v])
                continue
            if w not in idx:
                idx[w] = counter[0]; lowlink[w] = counter[0]; counter[0] += 1
                stack.append(w); on_stack.add(w)
                work.append((w, iter(adj_plain.get(w, []))))
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], idx[w])
    for v in V:
        if v not in idx: strongconnect(v)
    return sccs


def shortest_cycle_through(start, adj_plain, scc_set):
    dist = {start: 0}; parent = {start: None}; q = deque([start])
    while q:
        u = q.popleft()
        for w in adj_plain.get(u, []):
            if w not in scc_set: continue
            if w == start:
                seq = [start]; cur = u
                while cur is not None: seq.append(cur); cur = parent[cur]
                return list(reversed(seq))
            if w not in dist: dist[w] = dist[u] + 1; parent[w] = u; q.append(w)
    return None


def base_girth_cycle(T, adj_edge):
    adj_plain = {c: [cp for (cp, _) in adj_edge.get(c, [])] for c in T}
    sccs = tarjan_scc(T, adj_plain)
    best_seq = None
    for s in sccs:
        if len(s) < 2: continue
        start = next(iter(s))
        seq = shortest_cycle_through(start, adj_plain, s)
        if seq is not None and (best_seq is None or len(seq) < len(best_seq)):
            best_seq = seq
    return best_seq


def audit(ms, n, cycle, movers, det):
    """Audit the CYCLE (good cycle C itself) for A1 near-misses."""
    L = len(movers)
    # Cycle configs and firings are given directly; sourceTripleOfStep is:
    # for step k, mover = movers[k], firing config = cycle[k]
    # triple = (cycle[k][left], cycle[k][mover], cycle[k][right])
    step_triples = []
    for k in range(L):
        p = movers[k]
        ck = cycle[k]
        lv = ck[(p - 1) % n]; sv = ck[p]; rv = ck[(p + 1) % n]
        step_triples.append((p, lv, sv, rv))

    # Same-mover pairs
    by_mover = defaultdict(list)
    for k, (p, lv, sv, rv) in enumerate(step_triples):
        by_mover[p].append((k, lv, sv, rv))

    collisions = 0; near_miss_1 = 0
    protecting = Counter()  # coord that differs in near-miss
    near_miss_pairs = []
    total_pairs = 0
    for p, items in by_mover.items():
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                total_pairs += 1
                k1, l1, s1, r1 = items[i]; k2, l2, s2, r2 = items[j]
                diffs = []
                if l1 != l2: diffs.append('L')
                if s1 != s2: diffs.append('S')
                if r1 != r2: diffs.append('R')
                if len(diffs) == 0: collisions += 1
                elif len(diffs) == 1:
                    near_miss_1 += 1
                    protecting[diffs[0]] += 1
                    near_miss_pairs.append((k1, k2, p, diffs[0]))

    # Shallow escape audit (reuse from E7)
    result_build = build_tube(ms, n, cycle, movers, det)
    T, adj_edge, cycle_set, Lb, move_entries = result_build
    if not T: return None
    girth_seq = base_girth_cycle(T, adj_edge)
    if girth_seq is None: return None
    S_girth = girth_seq[:-1]; S_set = set(S_girth)
    shallow_events = []  # (c_idx_in_girth, p)
    for c_idx, c in enumerate(S_girth):
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx not in move_entries: continue
            val = move_entries[ctx]; target = list(c); target[p] = val; target = tuple(target)
            if target in S_set or target in cycle_set: continue
            if target in T: shallow_events.append((c_idx, p))

    n_shallow = len(shallow_events)

    return {
        'n': n, 'ms': list(ms), 'L': L,
        'same_mover_pairs': total_pairs,
        'collisions': collisions,
        'near_miss_1': near_miss_1,
        'protecting': dict(protecting),
        'n_shallow_escape': n_shallow,
    }


def main():
    print("=" * 72, flush=True)
    print("E10: A1 near-miss probe (2026-04-20)", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1,   40, 2.0, 15),
        (6, 4,   20, 3.0, 17),
        (7, 40,  10, 3.0, 19),
        (8, 200, 5,  4.0, 21),
    ]
    records = []; t_global = time.time()

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n(n); multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  sampled={len(sampled)} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cyc, movers, det in cycles:
                if len(movers) < 2 * n: continue
                r = audit(ms, n, cyc, movers, det)
                if r is not None: records.append(r)
            if (idx + 1) % max(1, len(sampled) // 5) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  t={time.time()-t0:.0f}s  "
                      f"records={len(records)}", flush=True)

    print(f"\n{'='*72}\nSummary ({len(records)} records, "
          f"{time.time()-t_global:.0f}s)\n{'='*72}")

    total_coll = sum(r['collisions'] for r in records)
    print(f"\nSANITY: total A1 collisions (should be 0): {total_coll}")

    by_n = defaultdict(list)
    for r in records: by_n[r['n']].append(r)

    # Per-n summary
    for n in sorted(by_n):
        recs = by_n[n]
        nm_counts = [r['near_miss_1'] for r in recs]
        smp = [r['same_mover_pairs'] for r in recs]
        any_nm = sum(1 for r in recs if r['near_miss_1'] > 0)
        coord_agg = Counter()
        for r in recs:
            for c, v in r['protecting'].items():
                coord_agg[c] += v
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    same-mover pairs per record: "
              f"min={min(smp)} median={sorted(smp)[len(smp)//2]} "
              f"mean={sum(smp)/len(smp):.1f} max={max(smp)}")
        print(f"    near-miss-1 per record: "
              f"min={min(nm_counts)} median={sorted(nm_counts)[len(nm_counts)//2]} "
              f"mean={sum(nm_counts)/len(nm_counts):.2f} max={max(nm_counts)}")
        print(f"    records with >=1 near-miss: {any_nm}/{len(recs)}  "
              f"({100*any_nm/len(recs):.0f}%)")
        if coord_agg:
            total = sum(coord_agg.values())
            dist = {c: f"{v}/{total} ({100*v/total:.0f}%)" for c, v in sorted(coord_agg.items())}
            print(f"    protecting coord distribution: {dist}")

    # Correlation between near-miss count and shallow-escape count
    print(f"\n{'='*72}\nCorrelation near-miss count vs shallow-escape count\n{'='*72}")
    for n in sorted(by_n):
        recs = by_n[n]
        xs = [r['near_miss_1'] for r in recs]
        ys = [r['n_shallow_escape'] for r in recs]
        if len(xs) < 2: continue
        mx = sum(xs)/len(xs); my = sum(ys)/len(ys)
        num = sum((x - mx)*(y - my) for x, y in zip(xs, ys))
        denx = (sum((x - mx)**2 for x in xs)) ** 0.5
        deny = (sum((y - my)**2 for y in ys)) ** 0.5
        rho = num / (denx * deny) if denx > 0 and deny > 0 else 0.0
        print(f"  n={n}  Pearson rho = {rho:+.3f}  (records={len(recs)})")

    # Tripwire verdict
    total_nm_recs = sum(sum(1 for r in by_n[n] if r['near_miss_1'] > 0) for n in by_n)
    total_recs = sum(len(by_n[n]) for n in by_n)
    print(f"\n{'='*72}\nTripwire verdicts\n{'='*72}")
    print(f"  T1 (>=90% records have 0 near-misses): "
          f"{'TRIGGERED (probe dies)' if total_nm_recs/total_recs < 0.1 else 'not triggered'}")
    # T2/T3 based on aggregate distribution
    agg_coord = Counter()
    for r in records:
        for c, v in r['protecting'].items(): agg_coord[c] += v
    if agg_coord:
        total = sum(agg_coord.values())
        shares = {c: v/total for c, v in agg_coord.items()}
        max_share = max(shares.values()); min_share = min(shares.values())
        if max_share - min_share < 0.2:
            print(f"  T2 (uniform coord distribution): TRIGGERED "
                  f"(shares {dict((c, f'{s:.0%}') for c,s in shares.items())})")
        else:
            print(f"  T3 (skewed coord distribution): TRIGGERED "
                  f"(shares {dict((c, f'{s:.0%}') for c,s in shares.items())})")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'a1_nearmiss_2026-04-20.json')
    with open(out_path, 'w') as f: json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path}.", flush=True)


if __name__ == "__main__":
    main()
