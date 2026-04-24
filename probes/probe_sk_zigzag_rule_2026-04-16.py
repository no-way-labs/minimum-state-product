#!/usr/bin/env python3
"""Extract the zig-zag L-cycle construction rule.

For each record, find the shortest L-cycle in peel(N_1).
For each step j ∈ [0, L):
  - walk config c_s^j and next c_s^{j+1}
  - firing position p_j (where they differ)
  - anchor (i_j, q_j, v_j): c_s^j = c_{i_j}[q_j ← v_j]
  - good cycle's firing at step i_j: M_j := movers[i_j]

Questions:
  Q1. Does p_j == M_j? (walk fires same position as good cycle at anchor step)
  Q2. Does i_{j+1} = i_j + 1? (anchor index advances in lockstep)
  Q3. What's the relation between (q_j, v_j) and (q_{j+1}, v_{j+1})?
      - Case A: q_{j+1} == q_j (anchor position unchanged)
      - Case B: q_{j+1} = M_j (anchor shifts to firing position, which just became different)
      - Case C: other
  Q4. When firing p at c_s = c_i[q ← v]:
        - If p == q: anchor goes "away from q" to some other position
        - If p != q: anchor stays at q, but i advances? (since c_{i+1}[p] = new)

Hypothesis H_zigzag:
  At step j with anchor (i, q, v) and walk firing p:
    (a) If p == movers[i] (firing matches good cycle):
        - Then c_s^j = c_i[q ← v], and walking fires p to c_{i+1}[q ← v'] for
          some v' (the walk keeps anchor position q but v changes as p==movers[i]
          affects c_i[p]).
        - Wait, firing p at c_s = c_i[q←v] (with p != q):
            c_s[p] = c_i[p] (since p != q), new value = det[p, c_s-context]
            = det[p, L_p, S_p, R_p] where L_p, S_p, R_p are c_s's context at p.
          If c_s[p's context] matches c_i[p's context] (because q is far from p),
          then det gives c_{i+1}[p]. So result = c_s[p ← c_{i+1}[p]] =
          (same as c_i except q=v and p = c_{i+1}[p]) = c_{i+1}[q ← v] if v != c_{i+1}[q].
          Hence new anchor = (i+1, q, v).
        - This keeps the anchor position q fixed and advances i by 1.
    (b) If p == q (firing is at anchor position):
        - c_s[q] = v. Firing q in c_s requires (L_q, v, R_q) context.
        - If v is not c_i[q], the context differs from good cycle's context at q.
          Det might still have an entry for this context (because cycle visits it
          at some different step j' where c_{j'}[q] = v). Then new value = det's
          value, and new anchor could be (j', q', v') for some different j'.
        - This is where the "jump" comes from.

So the rule may be:
  - p_j == M_j: lockstep advance (i, q, v) → (i+1, q, v)
  - p_j != M_j: anchor position q must equal p_j? and jumps to a different i.
"""
from itertools import product as iproduct
from collections import defaultdict, deque
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


def compute_peel_and_cycle(ms, n, cycle, movers, det, L):
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
    if not peel: return None, None

    # Find shortest cycle of length L
    for src in peel:
        dist = {src: 0}
        pred = {}
        qd = deque([src])
        while qd:
            u = qd.popleft()
            if dist[u] >= L: break
            for vv in adj[u]:
                if vv not in peel: continue
                if vv == src and dist[u] + 1 == L:
                    path = [u]
                    while path[-1] != src:
                        path.append(pred[path[-1]])
                    path.reverse()
                    path.append(src)
                    return peel, path  # length L+1 (closed)
                if vv not in dist:
                    dist[vv] = dist[u] + 1
                    pred[vv] = u
                    qd.append(vv)
    return peel, None


def analyze_cycle(ms, n, cycle, movers, path, L):
    """path is the L-cycle configs [c_s^0, c_s^1, ..., c_s^L (= c_s^0)]."""
    N = n
    rows = []
    for j in range(L):
        c_s = path[j]
        c_s_next = path[j + 1]
        # Firing position
        diffs = [k for k in range(N) if c_s[k] != c_s_next[k]]
        p_fire = diffs[0] if len(diffs) == 1 else None
        # All Hamming-1 anchors for c_s
        anchors = []
        for i, c in enumerate(cycle):
            dd = [k for k in range(N) if c[k] != c_s[k]]
            if len(dd) == 1:
                anchors.append((i, dd[0], c_s[dd[0]]))
        # All Hamming-1 anchors for c_s_next
        anchors_next = []
        for i, c in enumerate(cycle):
            dd = [k for k in range(N) if c[k] != c_s_next[k]]
            if len(dd) == 1:
                anchors_next.append((i, dd[0], c_s_next[dd[0]]))
        rows.append({
            'j': j, 'c_s': c_s, 'c_s_next': c_s_next, 'p_fire': p_fire,
            'anchors_c_s': anchors, 'anchors_c_s_next': anchors_next,
            'movers_at_anchors': [movers[a[0]] for a in anchors],
        })
    return rows


def test_hypothesis_H(rows, movers, L):
    """Test H: for each step j, ∃ anchor (i, q, v) of c_s^j such that p_fire == movers[i],
       AND the resulting step's anchor has i_next = (i+1) % L (in some anchor of c_s_next)."""
    H_match = 0
    H_advance = 0
    H_full = 0
    for r in rows:
        p = r['p_fire']
        # Is there an anchor (i, q, v) with movers[i] == p?
        matching_anchors = [(i, q, v) for (i, q, v) in r['anchors_c_s'] if movers[i] == p]
        if matching_anchors:
            H_match += 1
            # For each matching anchor, check if (i+1) % L is an anchor index of c_s_next
            next_anchor_is = [a[0] for a in r['anchors_c_s_next']]
            if any(((i + 1) % L in next_anchor_is) for (i, q, v) in matching_anchors):
                H_advance += 1
                H_full += 1
    return H_match, H_advance, H_full


def main():
    print("=" * 72, flush=True)
    print("Zig-zag L-cycle construction rule probe", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 10, 3.0, 16),
        (6, 8, 5, 4.0, 17),
    ]
    all_tests = []
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
                if L < 2 * n + 2: continue
                peel, path = compute_peel_and_cycle(ms, n, cycle, movers, det, L)
                if peel is None or path is None: continue
                rows = analyze_cycle(ms, n, cycle, movers, path, L)
                H_m, H_a, H_f = test_hypothesis_H(rows, movers, L)
                all_tests.append({
                    'n': n, 'ms': ms, 'L': L, 'peel_size': len(peel),
                    'H_match': H_m, 'H_advance': H_a, 'H_full': H_f,
                })
            if (idx + 1) % max(1, len(sampled) // 5) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={len(all_tests)}", flush=True)

    print(f"\n{'='*72}\nHypothesis H (∃ anchor i with movers[i]=p_fire AND (i+1)%L in next-anchors)\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_tests: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        totL = sum(r['L'] for r in recs)
        totM = sum(r['H_match'] for r in recs)
        totF = sum(r['H_full'] for r in recs)
        print(f"  n={n}  records={len(recs)}  total steps={totL}")
        print(f"    p_fire matches some anchor's movers[i]: {totM}/{totL} ({100*totM/totL:.1f}%)")
        print(f"    p_fire matches AND (i+1)%L is next-anchor: {totF}/{totL} ({100*totF/totL:.1f}%)")
        # Per-record: fraction of steps satisfying H_full
        per_rec_full = [r['H_full'] / r['L'] for r in recs]
        full_records = sum(1 for r in recs if r['H_full'] == r['L'])
        print(f"    records with 100% H_full: {full_records}/{len(recs)} ({100*full_records/len(recs):.1f}%)")
        if per_rec_full:
            print(f"    avg fraction H_full per record: {sum(per_rec_full)/len(per_rec_full):.3f}")


if __name__ == "__main__":
    main()
