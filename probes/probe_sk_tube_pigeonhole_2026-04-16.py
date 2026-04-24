#!/usr/bin/env python3
"""Tube pigeonhole: count edges vs sinks inside N_3(C) ∩ VC_NG.

Let T = N_3(C) ∩ VC_NG.
Let E(T) = {forced NG-edges (c, c') with c, c' ∈ T}.
Let Sink(T) = {c ∈ T : no forced NG-successor in T}.

Claim (hoped): |E(T)| ≥ |T| - |Sink(T)| + 1 (strict inequality).
If this holds, then the subgraph G[T\Sink] has |V|=|T|-|Sink|,
|E|≥|V|+1, hence contains a cycle. But G[T\Sink] has out-deg ≥ 1
by definition, so by peeling we get SK.Nonempty.

Simpler check: Does `peel(T)` = `{c : keep after iteratively removing
N_3-sinks}` ≠ ∅? If so, we have a cycle.

Tests:
  P1: |E(T)| vs |T|
  P2: |T \ peel(T)| = total removed; |peel(T)|
  P3: Frequency of peel(T) = ∅ (empty) vs nonempty
  P4: If peel(T) nonempty, |peel(T)| distribution
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


def hamming(a, b, n):
    return sum(1 for i in range(n) if a[i] != b[i])


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    T = {c for c in VC_NG if min(hamming(c, cc, n) for cc in cycle) <= 3}
    # Also compute with k=1,2
    Ts = {}
    for k in [1, 2, 3]:
        Ts[k] = {c for c in VC_NG if min(hamming(c, cc, n) for cc in cycle) <= k}

    # Adjacency restricted to each T_k
    def build_adj_in(T):
        adj = defaultdict(list)
        for c in T:
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in T:
                        adj[c].append(nc)
        return adj

    def peel(T, adj):
        """Remove sinks iteratively until none left."""
        cur = set(T)
        changed = True
        while changed:
            changed = False
            to_remove = set()
            for c in cur:
                succs = [s for s in adj[c] if s in cur]
                if not succs:
                    to_remove.add(c)
            if to_remove:
                cur -= to_remove
                changed = True
        return cur

    results = {}
    for k in [1, 2, 3]:
        if not Ts[k]:
            results[k] = {'T_size': 0, 'E_size': 0, 'sinks': 0, 'peel_size': 0}
            continue
        adj = build_adj_in(Ts[k])
        E_size = sum(len(adj[c]) for c in Ts[k])
        sinks = sum(1 for c in Ts[k] if not adj[c])
        peeled = peel(Ts[k], adj)
        results[k] = {
            'T_size': len(Ts[k]),
            'E_size': E_size,
            'sinks': sinks,
            'peel_size': len(peeled),
        }

    return {
        'n': n, 'ms': ms, 'L': L,
        'VC_NG_size': len(VC_NG),
        'per_k': results,
    }


def main():
    print("=" * 72, flush=True)
    print("Tube pigeonhole probe: does peel(N_k ∩ VC_NG) always nonempty?", flush=True)
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
        print(f"\n  n={n}  records={len(recs)}")
        for k in [1, 2, 3]:
            valid = [r['per_k'][k] for r in recs if r['per_k'][k]['T_size'] > 0]
            if not valid: continue
            nonempty_peel = sum(1 for x in valid if x['peel_size'] > 0)
            ts = [x['T_size'] for x in valid]
            ps = [x['peel_size'] for x in valid]
            es = [x['E_size'] for x in valid]
            sks = [x['sinks'] for x in valid]
            # Edge-minus-sink margin
            margins = [x['E_size'] - (x['T_size'] - x['sinks']) for x in valid]
            print(f"    k={k}: peel(N_{k} ∩ VC-NG) nonempty: {nonempty_peel}/{len(valid)} ({100*nonempty_peel/len(valid):.1f}%)")
            print(f"      |T|: min={min(ts)} max={max(ts)} avg={sum(ts)/len(ts):.1f}")
            print(f"      |E|: min={min(es)} max={max(es)} avg={sum(es)/len(es):.1f}")
            print(f"      |sinks|: min={min(sks)} max={max(sks)} avg={sum(sks)/len(sks):.1f}")
            print(f"      |peel|: min={min(ps)} max={max(ps)} avg={sum(ps)/len(ps):.1f}")
            print(f"      |E| - (|T|-|sinks|): min={min(margins)} max={max(margins)} avg={sum(margins)/len(margins):.1f}")


if __name__ == "__main__":
    main()
