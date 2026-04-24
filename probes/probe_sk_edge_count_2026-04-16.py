#!/usr/bin/env python3
"""Edge-count pigeonhole upgrade.

The existing slab_unblocked lemma gives ≥ 1 unblocked forced NG-edge.
If we can show #{unblocked NG-edges} ≥ |VC_NG| + 1, then by pigeonhole
the forced NG-graph has average out-degree ≥ 1 + 1/|VC_NG|, which
yields a directed cycle in NG.

More generally: if every c ∈ VC_NG has a forced NG-successor, then VC_NG
is the domain of a self-map f: VC_NG → VC_NG (since successors stay in
VC_NG when all values in V_i appear in cycle). This feeds directly into
`sk_nonempty_of_self_map` via `exists_closed_nonempty_subset`.

Tests:
  E1: fraction of configs in VC_NG with a forced NG-successor
  E2: |VC_NG| vs #configs-with-NG-successor
  E3: out-degree distribution
  E4: is VC_NG always a valid domain for a self-map (100% have successor)?
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


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Out-degree in forced NG-graph
    out_deg = {}
    ng_successor_count = 0
    cycle_edge_count = 0
    no_edge_count = 0
    for c in VC_NG:
        deg_ng = 0
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in VC_NG:
                    deg_ng += 1
                elif nc in cycle_set:
                    pass  # edge to cycle — doesn't help
        out_deg[c] = deg_ng
        if deg_ng > 0:
            ng_successor_count += 1
        else:
            # Check: does it at least have a forced edge? (maybe just to cycle)
            has_any = any(
                (p, c[(p - 1) % n], c[p], c[(p + 1) % n]) in move_entries
                for p in range(n)
            )
            if has_any:
                cycle_edge_count += 1
            else:
                no_edge_count += 1

    total_ng_edges = sum(out_deg.values())
    deg_dist = Counter(out_deg.values())

    return {
        'n': n, 'ms': ms, 'L': L,
        'VC_NG_size': len(VC_NG),
        'has_ng_succ': ng_successor_count,
        'only_cycle_edges': cycle_edge_count,
        'no_edges': no_edge_count,
        'total_ng_edges': total_ng_edges,
        'avg_out_deg': total_ng_edges / max(len(VC_NG), 1),
        'min_out_deg': min(out_deg.values()) if out_deg else 0,
        'max_out_deg': max(out_deg.values()) if out_deg else 0,
        'deg_dist': dict(deg_dist),
    }


def main():
    print("=" * 72, flush=True)
    print("NG out-degree / self-map feasibility probe", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 3.0, 17),
        (8, 500, 3, 12.0, 20),
    ]
    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2: continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        vcng = [r['VC_NG_size'] for r in recs]
        has_succ = [r['has_ng_succ'] for r in recs]
        only_cyc = [r['only_cycle_edges'] for r in recs]
        noedg = [r['no_edges'] for r in recs]

        # Core: is every c in VC_NG having an NG successor? (100% means self-map exists)
        all_have = sum(1 for r in recs if r['has_ng_succ'] == r['VC_NG_size'])
        frac_have_full = 100 * all_have / len(recs) if recs else 0

        fracs = [r['has_ng_succ'] / max(r['VC_NG_size'], 1) for r in recs]
        min_deg = [r['min_out_deg'] for r in recs]
        avg_deg = [r['avg_out_deg'] for r in recs]

        print(f"\n  n={n}  records={len(recs)}")
        print(f"    |VC_NG|: min={min(vcng)} max={max(vcng)} avg={sum(vcng)/len(vcng):.1f}")
        print(f"    ALL configs have NG successor: {all_have}/{len(recs)} ({frac_have_full:.1f}%)")
        print(f"    frac configs w/ NG successor: min={min(fracs):.3f} max={max(fracs):.3f} avg={sum(fracs)/len(fracs):.3f}")
        print(f"    min out-deg (NG): min={min(min_deg)} max={max(min_deg)}")
        print(f"    avg out-deg (NG): min={min(avg_deg):.2f} max={max(avg_deg):.2f} avg={sum(avg_deg)/len(avg_deg):.2f}")
        # Configs stuck (no NG or cycle edge)
        stuck = sum(r['no_edges'] for r in recs)
        tot_cfg = sum(vcng)
        print(f"    configs w/ no forced edge at all: {stuck}/{tot_cfg}")


if __name__ == "__main__":
    main()
