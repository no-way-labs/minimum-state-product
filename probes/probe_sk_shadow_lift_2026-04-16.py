#!/usr/bin/env python3
"""Shadow-lift test: for some (q, v, i), is the lifted walk c_i[q←v] closed?

For each cycle C = (c_0, ..., c_{L-1}) firing at positions p_0, ..., p_{L-1},
and each choice of position q and value v ∈ V_q \ {c_0[q]} and start i,
attempt to walk the lifted path:
  step j: current config w_j, originally at cycle step (i+j) mod L, firing at p_{(i+j) mod L}.
  If p_{(i+j) mod L} ∉ {q-1, q, q+1} mod n:
    the lift applies: w_{j+1} = w_j[p_*←det_val]. Still in N_1(C).
  Else:
    check det at w_j at position p_*. If determined and result ∈ N_1(C) ∪ C, continue.
    (else break)

Question: does the walk return to w_0 after L steps (closed)?

Even simpler first: for some (q, v, i), is the walk DEFINED for all L steps
(never exits N_1(C) ∪ C)? If yes, and the walk ends at w_0, we have a cycle.

Tests:
  L1: ∃ (q, v, i) such that walk runs all L steps without leaving N_1(C)?
  L2: ∃ (q, v, i) such that walk runs all L steps AND returns to start?
  L3: Frequency of break-points on best q.
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
    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in V[q]:
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)

    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Best q: minimize # cycle steps firing in {q-1, q, q+1}
    fire_count = [0] * n
    for p_i in movers:
        fire_count[p_i] += 1
    F = [fire_count[(q-1)%n] + fire_count[q] + fire_count[(q+1)%n] for q in range(n)]
    best_q = min(range(n), key=lambda q: F[q])

    # For each q, each v ∈ V_q \ {start_val}, each starting cycle index i:
    # attempt lifted walk of length L
    any_closed = False
    closed_witness = None
    any_survives_L = False
    best_survive = 0  # max length walk that stays in N1 ∪ C (without break)
    best_walk_q = None

    results_per_q = {}
    for q in range(n):
        best_this_q = 0
        closed_this_q = False
        for v in V[q]:
            for i_start in range(L):
                c0 = cycle[i_start]
                if v == c0[q]: continue
                w = list(c0); w[q] = v; w = tuple(w)
                if w in cycle_set: continue  # not in N_1
                # Walk L steps
                current = w
                cycle_idx = i_start
                survived = 0
                closed = False
                for step in range(L):
                    # Firing position for step cycle_idx → (cycle_idx + 1) mod L
                    p_fire = movers[cycle_idx]
                    ctx = (p_fire, current[(p_fire - 1) % n], current[p_fire], current[(p_fire + 1) % n])
                    if ctx not in move_entries:
                        break
                    new_val = move_entries[ctx]
                    new_current = list(current); new_current[p_fire] = new_val
                    new_current = tuple(new_current)
                    if new_current in cycle_set:
                        # Walk hit the cycle — breaks N_1 lift
                        break
                    if new_current not in N1:
                        break
                    current = new_current
                    cycle_idx = (cycle_idx + 1) % L
                    survived = step + 1
                    if current == w and step == L - 1:
                        closed = True
                        break
                if survived > best_this_q:
                    best_this_q = survived
                if closed:
                    closed_this_q = True
                    if not any_closed:
                        any_closed = True
                        closed_witness = (q, v, i_start)
                if survived == L:
                    any_survives_L = True
        results_per_q[q] = (best_this_q, closed_this_q)
        if best_this_q > best_survive:
            best_survive = best_this_q
            best_walk_q = q

    return {
        'n': n, 'ms': ms, 'L': L,
        'best_q_F': F[best_q],
        'min_F': min(F),
        'any_closed_walk': any_closed,
        'any_survives_full_L': any_survives_L,
        'best_survive': best_survive,
        'closed_witness': closed_witness,
    }


def main():
    print("=" * 72)
    print("Shadow-lift probe: closed walk in N_1(C)?")
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
                if L < 2 * n + 2:
                    continue
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
        closed = sum(1 for r in recs if r['any_closed_walk'])
        full_L = sum(1 for r in recs if r['any_survives_full_L'])
        avg_best = sum(r['best_survive'] for r in recs) / len(recs)
        avg_minF = sum(r['min_F'] for r in recs) / len(recs)
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    ∃ closed lifted walk (returns to start): {closed}/{len(recs)} ({100*closed/len(recs):.1f}%)")
        print(f"    ∃ walk survives full L steps:            {full_L}/{len(recs)} ({100*full_L/len(recs):.1f}%)")
        print(f"    avg best survive length:                 {avg_best:.1f}")
        print(f"    avg min_q F(q) (break-points on best q): {avg_minF:.1f}")


if __name__ == "__main__":
    main()
