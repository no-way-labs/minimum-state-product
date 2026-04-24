#!/usr/bin/env python3
"""Parallel-cycle probe: does NG contain a cycle of length L (shadowing C)?

Empirically sk_size ~ 2L and shortest forced cycle is in [L, L+3].
Hypothesis: for every (ms, C), ∃ a bijection φ : C → VC-NG such that
φ(C) is a directed cycle in the forced NG-graph using the same
mover-at-each-step sequence as C.

For each step k of C with mover p_k at config c_k:
  φ(c_k) has forced move at position p_k → φ(c_{k+1})
  applyMove(φ(c_k), p_k, det_output) = φ(c_{k+1})
  φ(c_k) ≠ c_k (parallel ≠ original)

Tests:
  (P1) Does a parallel-cycle exist for every record?
  (P2) If yes, what's the "shift" structure? Is φ(c)[i] = c[i] + δ_i
       for some fixed δ ∈ Z/m_1 × ... × Z/m_n? Or some other form?
  (P3) Is φ(C) ⊂ SK always? (It must be, if φ(C) is a closed forced cycle.)

Search strategy: for each candidate first config c' = 1-flip of c_0
(or a forced neighbor of c_0 from detOf), attempt to walk the same
mover sequence and check if the det forces consistent steps.
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


def try_parallel_cycle(cycle, movers, det, n, ms, cycle_set):
    """Try to find a cycle φ(C) = c'_0 → c'_1 → ... → c'_0 in NG that
    uses the same mover sequence as C but starts at some c'_0 ≠ c_0."""
    L = len(movers)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    V = value_sets(cycle, n)

    # Try each candidate first config c'_0 in VC-NG
    for init in iproduct(*[sorted(V[i]) for i in range(n)]):
        if init in cycle_set:
            continue
        # Walk mover sequence
        c = init
        path = [c]
        ok = True
        for k in range(L):
            p = movers[k]
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx not in move_entries:
                ok = False
                break
            v = move_entries[ctx]
            nc = list(c); nc[p] = v; nc = tuple(nc)
            if nc in cycle_set:
                ok = False
                break
            path.append(nc)
            c = nc
        if not ok:
            continue
        if c == init:
            # Shift structure?
            delta = tuple((path[0][i] - cycle[0][i]) % ms[i] for i in range(n))
            # Check if all steps have same delta
            consistent = all(
                tuple((path[k][i] - cycle[k][i]) % ms[i] for i in range(n)) == delta
                for k in range(L)
            )
            return (init, delta, consistent, tuple(path))
    return None


def try_parallel_forced_reachable(cycle, movers, det, n, ms, cycle_set):
    """Looser test: from each 1-flip of cycle[0], does it 'track' some
    forced sequence back to itself? Even if mover sequence differs."""
    # Only test 1-flip starts
    c0 = cycle[0]
    V = value_sets(cycle, n)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    candidates = []
    for i in range(n):
        for v in V[i]:
            if v == c0[i]: continue
            c = list(c0); c[i] = v; c = tuple(c)
            if c not in cycle_set:
                candidates.append(c)
    # For each candidate, do a BFS looking for a cycle back to it with only forced moves
    found_any = False
    for start in candidates:
        # BFS up to depth L+5
        visited = {start: None}
        q = [start]
        qi = 0
        max_depth = {start: 0}
        while qi < len(q):
            c = q[qi]; qi += 1
            d = max_depth[c]
            if d > len(movers) + 5:
                continue
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in cycle_set:
                        continue
                    if nc == start:
                        found_any = True
                        break
                    if nc not in visited:
                        visited[nc] = c
                        max_depth[nc] = d + 1
                        q.append(nc)
            if found_any:
                break
        if found_any:
            break
    return found_any


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    # P1: rigid parallel cycle (same mover seq)
    pc_rigid = try_parallel_cycle(cycle, movers, det, n, ms, cycle_set)
    # P4: any forced cycle starting at 1-flip of c_0
    pc_1flip = try_parallel_forced_reachable(cycle, movers, det, n, ms, cycle_set)
    return {
        'n': n, 'ms': ms, 'L': L,
        'rigid_parallel_cycle': pc_rigid is not None,
        'rigid_parallel_consistent_shift': pc_rigid[2] if pc_rigid else False,
        'rigid_parallel_delta': pc_rigid[1] if pc_rigid else None,
        'one_flip_forced_cycle': pc_1flip,
    }


def main():
    print("=" * 72)
    print("Parallel-cycle probe — does NG always contain a cycle shadowing C?")
    print("=" * 72)
    plan = [
        (5, 1, 200, 3.0, 14),
        (6, 8, 80, 2.0, 14),
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
                if L < 2 * n + 2:
                    continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        rpc = sum(1 for r in recs if r['rigid_parallel_cycle'])
        rpc_sh = sum(1 for r in recs if r['rigid_parallel_consistent_shift'])
        of1 = sum(1 for r in recs if r['one_flip_forced_cycle'])
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    P1 rigid parallel cycle exists:         {rpc}/{len(recs)} ({100*rpc/len(recs):.1f}%)")
        print(f"      of which consistent-shift (φ=c+δ):    {rpc_sh}/{rpc if rpc else 1}")
        print(f"    P4 1-flip start has forced back-cycle:  {of1}/{len(recs)} ({100*of1/len(recs):.1f}%)")

        # Delta distribution
        delta_counter = Counter()
        for r in recs:
            if r['rigid_parallel_delta']:
                delta_counter[r['rigid_parallel_delta']] += 1
        print(f"    rigid parallel δ distribution (top 5): {delta_counter.most_common(5)}")


if __name__ == "__main__":
    main()
