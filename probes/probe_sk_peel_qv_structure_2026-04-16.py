#!/usr/bin/env python3
"""Characterize the (q, v) anchor set of peel(N_1).

Finding: at n=7, #distinct (q,v) = EXACTLY 14 = 2n in 200/200 records.
Questions:
  Q1. Is it exactly 2 values of v per q?
  Q2. At each q, which 2 values? (vs. cycle values V_q)
  Q3. For n=5, 6: is #distinct (q,v) ≈ 2n, with spread?
      n=5: avg 9.8 (2n=10), n=6: avg 11.7 (2n=12). Very close to 2n.
  Q4. What characterizes v vs. c_i[q] along cycle?
  Q5. For each (q,v), how many i's make c_i[q←v] ∈ peel? (max #i avg ~7 at n=7).
      Does it depend on |V_q|?
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
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in range(ms[q]):
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)

    adj = defaultdict(list)
    for c in N1:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in N1:
                    adj[c].append(nc)

    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove: break
        cur -= to_remove
    peel = cur
    if not peel: return None

    # For each (q, v), count #i for which c_i[q←v] ∈ peel
    qv_icount = defaultdict(int)
    qv_ilist = defaultdict(list)
    for c_s in peel:
        for i, c in enumerate(cycle):
            diffs = [k for k in range(n) if c[k] != c_s[k]]
            if len(diffs) == 1:
                q = diffs[0]; v = c_s[q]
                qv_icount[(q, v)] += 1
                qv_ilist[(q, v)].append(i)

    # Per-q: number of v values that survive
    q_vcount = defaultdict(set)
    for (q, v) in qv_icount:
        q_vcount[q].add(v)

    # Classify v: inside V_q or outside?
    inside = outside = 0
    inside_pairs = []; outside_pairs = []
    for (q, v), cnt in qv_icount.items():
        if v in V[q]:
            inside += cnt; inside_pairs.append((q, v, cnt, sorted(V[q])))
        else:
            outside += cnt; outside_pairs.append((q, v, cnt, sorted(V[q])))

    # Per-q v distribution
    per_q_vsizes = [len(q_vcount[q]) for q in range(n)]
    # q with ≥1 anchor
    q_with_any = sum(1 for q in range(n) if q_vcount[q])

    # m_q for each q
    m_per_q = list(ms)

    return {
        'n': n, 'ms': ms, 'L': L, 'peel_size': len(peel),
        'n_qv_pairs': len(qv_icount),
        'per_q_vsizes': per_q_vsizes,
        'q_with_any': q_with_any,
        'inside_total': inside,
        'outside_total': outside,
        'm_per_q': m_per_q,
        'V_sizes': [len(V[q]) for q in range(n)],
        'qv_icount_max': max(qv_icount.values()) if qv_icount else 0,
        'qv_icount_min': min(qv_icount.values()) if qv_icount else 0,
    }


def main():
    print("=" * 72, flush=True)
    print("(q, v) structure of peel(N_1)", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 4.0, 17),
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
                if r is None: continue
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 6) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        print(f"\n  n={n}  records={len(recs)}")
        peel_sizes = [r['peel_size'] for r in recs]
        nqv = [r['n_qv_pairs'] for r in recs]
        print(f"    |peel|: min={min(peel_sizes)} max={max(peel_sizes)} avg={sum(peel_sizes)/len(peel_sizes):.1f}")
        print(f"    #(q,v): min={min(nqv)} max={max(nqv)} avg={sum(nqv)/len(nqv):.1f}  2n={2*n}")

        # Per-q vsize histogram
        vsize_hist = Counter()
        for r in recs:
            for s in r['per_q_vsizes']:
                vsize_hist[s] += 1
        print(f"    Per-q #v-anchors distribution: {dict(sorted(vsize_hist.items()))}")

        # # of q's with anchors
        q_any_hist = Counter(r['q_with_any'] for r in recs)
        print(f"    # q's with any anchor: {dict(sorted(q_any_hist.items()))}")

        # inside vs outside V_q
        in_out = [(r['inside_total'], r['outside_total']) for r in recs]
        in_total = sum(x[0] for x in in_out)
        out_total = sum(x[1] for x in in_out)
        print(f"    v ∈ V_q (inside cycle-values): total={in_total}")
        print(f"    v ∉ V_q (outside cycle-values): total={out_total}")

        # Per-m_q analysis: for positions where m_q = k, how many v values anchor?
        per_m_vsize = defaultdict(list)
        for r in recs:
            for q in range(n):
                per_m_vsize[r['m_per_q'][q]].append(r['per_q_vsizes'][q])
        print(f"    Per-m_q #v-anchor stats:")
        for m_q, lst in sorted(per_m_vsize.items()):
            avg = sum(lst)/len(lst) if lst else 0
            print(f"      m_q={m_q}: count={len(lst)}, avg #v={avg:.2f}, min={min(lst)}, max={max(lst)}")

        # Per (m_q, |V_q|) analysis: does #v-anchor depend on cycle coverage?
        per_mV_vsize = defaultdict(list)
        for r in recs:
            for q in range(n):
                per_mV_vsize[(r['m_per_q'][q], r['V_sizes'][q])].append(r['per_q_vsizes'][q])
        print(f"    Per (m_q, |V_q|) #v-anchor:")
        for (m_q, Vq), lst in sorted(per_mV_vsize.items()):
            avg = sum(lst)/len(lst) if lst else 0
            print(f"      m_q={m_q}, |V_q|={Vq}: count={len(lst)}, avg #v={avg:.2f}, min={min(lst)}, max={max(lst)}")


if __name__ == "__main__":
    main()
