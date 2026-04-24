#!/usr/bin/env python3
"""Tube closure: is N_k(C) ∩ VC_NG forward-closed under forced NG-moves?

If yes for some small k, then for any c ∈ N_k(C) ∩ VC_NG with a forced NG
successor f(c), f(c) also lies in N_k(C) ∩ VC_NG. Combined with "every
c has a forced NG-successor" (partial), this gives a self-map on
{c ∈ N_k(C) ∩ VC_NG : c has an NG-successor}.

For each record, for k ∈ {1, 2, 3}:
  T1: |N_k(C) ∩ VC_NG|
  T2: Fraction of configs in N_k(C) ∩ VC_NG with ALL forced NG-successors
      also in N_k(C) ∩ VC_NG (i.e., forward-closed)
  T3: Fraction with ≥ 1 forced NG-successor in N_k(C) ∩ VC_NG
  T4: Does SCC equal peel(N_k(C) ∩ VC_NG) for some k?

Also: is there a canonical successor function? For each c in SCC, define
f(c) = the smallest-position forced NG-successor that stays in SCC.
Check that f is deterministic and SCC = orbit of some c under f.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import sys, time


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


def tarjan_scc(nodes, adj):
    index = {}; low = {}
    stack = []; on_stack = set()
    counter = [0]; sccs = []
    sys.setrecursionlimit(500000)
    def strong(v):
        index[v] = counter[0]; low[v] = counter[0]; counter[0] += 1
        stack.append(v); on_stack.add(v)
        for w in adj.get(v, []):
            if w not in index:
                strong(w); low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); on_stack.discard(w)
                comp.append(w)
                if w == v: break
            sccs.append(comp)
    for v in nodes:
        if v not in index: strong(v)
    return sccs


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Min Hamming distance from each config in VC_NG to C
    hd = {c: min(hamming(c, cc, n) for cc in cycle) for c in VC_NG}

    # NG-adjacency
    adj = defaultdict(list)
    for c in VC_NG:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in VC_NG:
                    adj[c].append(nc)

    # Find SCC
    sccs = tarjan_scc(list(VC_NG), adj)
    nontriv = [c for c in sccs if len(c) >= 2 or (len(c) == 1 and c[0] in adj.get(c[0], []))]
    scc_union = set()
    for c in nontriv: scc_union.update(c)

    # For k ∈ {1, 2, 3}: test closure
    results_per_k = {}
    for k in [1, 2, 3]:
        Nk = {c for c in VC_NG if hd[c] <= k}
        if not Nk:
            results_per_k[k] = None; continue
        all_in_k = 0
        some_in_k = 0
        no_succ = 0
        for c in Nk:
            succs = adj.get(c, [])
            if not succs:
                no_succ += 1; continue
            all_in = all(s in Nk for s in succs)
            some_in = any(s in Nk for s in succs)
            if all_in: all_in_k += 1
            if some_in: some_in_k += 1
        has_any_succ = len(Nk) - no_succ
        results_per_k[k] = {
            'size': len(Nk),
            'all_in': all_in_k,
            'some_in': some_in_k,
            'no_succ': no_succ,
            'has_any_succ': has_any_succ,
            'frac_all_closed': all_in_k / max(len(Nk), 1),
            'frac_some_closed': some_in_k / max(len(Nk), 1),
        }

    # SCC relation to N_k
    scc_in_n3 = all(hd[c] <= 3 for c in scc_union) if scc_union else False
    scc_in_n2 = all(hd[c] <= 2 for c in scc_union) if scc_union else False
    scc_in_n1 = all(hd[c] <= 1 for c in scc_union) if scc_union else False

    # Canonical successor: first p with NG-successor in SCC
    if scc_union:
        canonical = {}
        for c in scc_union:
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in scc_union:
                        canonical[c] = nc
                        break
        canonical_total = all(c in canonical for c in scc_union)
        # Orbit from arbitrary start
        if canonical_total:
            start = next(iter(scc_union))
            orbit_seen = {start}
            cur = canonical[start]
            orbit_len = 1
            while cur not in orbit_seen and orbit_len < len(scc_union) * 2:
                orbit_seen.add(cur)
                cur = canonical[cur]
                orbit_len += 1
            orbit_covers_scc = orbit_seen >= scc_union  # does orbit visit all SCC nodes
        else:
            orbit_len = None; orbit_covers_scc = False
    else:
        canonical_total = False; orbit_len = None; orbit_covers_scc = False

    return {
        'n': n, 'ms': ms, 'L': L,
        'scc_size': len(scc_union),
        'scc_in_n1': scc_in_n1, 'scc_in_n2': scc_in_n2, 'scc_in_n3': scc_in_n3,
        'canonical_total': canonical_total,
        'orbit_len': orbit_len,
        'orbit_covers_scc': orbit_covers_scc,
        'per_k': results_per_k,
    }


def main():
    print("=" * 72, flush=True)
    print("Tube closure + canonical successor probe", flush=True)
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
        # SCC ⊆ N_k
        in1 = sum(1 for r in recs if r['scc_in_n1'])
        in2 = sum(1 for r in recs if r['scc_in_n2'])
        in3 = sum(1 for r in recs if r['scc_in_n3'])
        print(f"    SCC ⊆ N_1: {in1}/{len(recs)} ({100*in1/len(recs):.1f}%)")
        print(f"    SCC ⊆ N_2: {in2}/{len(recs)} ({100*in2/len(recs):.1f}%)")
        print(f"    SCC ⊆ N_3: {in3}/{len(recs)} ({100*in3/len(recs):.1f}%)")
        # Canonical successor
        ct = sum(1 for r in recs if r['canonical_total'])
        oc = sum(1 for r in recs if r['orbit_covers_scc'])
        print(f"    every SCC config has canonical-first-NG successor: {ct}/{len(recs)} ({100*ct/len(recs):.1f}%)")
        print(f"    canonical orbit covers entire SCC: {oc}/{len(recs)} ({100*oc/len(recs):.1f}%)")
        if ct:
            ols = [r['orbit_len'] for r in recs if r['canonical_total']]
            print(f"    canonical orbit len: min={min(ols)} max={max(ols)} avg={sum(ols)/len(ols):.1f}")
        # per-k tube closure
        for k in [1, 2, 3]:
            valid = [r['per_k'][k] for r in recs if r['per_k'].get(k)]
            if not valid: continue
            all_closed = [x['frac_all_closed'] for x in valid]
            some_closed = [x['frac_some_closed'] for x in valid]
            full_closure = sum(1 for x in valid if x['all_in'] + x['no_succ'] == x['size'])
            some_full = sum(1 for x in valid if x['some_in'] + x['no_succ'] == x['size'])
            print(f"    N_{k}: avg frac ALL-NG-succ-in-N_{k}: {sum(all_closed)/len(all_closed):.3f} | "
                  f"avg frac SOME-NG-succ-in-N_{k}: {sum(some_closed)/len(some_closed):.3f}")
            print(f"    N_{k}: full ALL-closure rate: {full_closure}/{len(valid)} | "
                  f"full SOME-closure rate: {some_full}/{len(valid)}")


if __name__ == "__main__":
    main()
