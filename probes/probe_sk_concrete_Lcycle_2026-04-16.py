#!/usr/bin/env python3
"""Extract one concrete L-cycle from peel(N_1(C)) and dump its structure.

For a small n=5 record, find the shortest cycle in peel(N_1) of length L,
dump: (cycle config c_i, shadow config c_s, firing position p, new value).
Analyze:
  - Which cycle index i does each shadow config correspond to?
  - Does the firing position p match movers[i]?
  - Is there a pattern in (q, v, i) → (q', v', i')?
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


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def dump_example(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in V[q]:
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

    # Peel
    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove: break
        cur -= to_remove
    peel_set = cur
    if not peel_set: return None

    # Find shortest cycle via BFS with predecessor tracking
    for src in peel_set:
        dist = {src: 0}
        pred = {}
        q = deque([src])
        found_cycle = None
        while q and not found_cycle:
            u = q.popleft()
            for v in adj[u]:
                if v not in peel_set: continue
                if v == src:
                    # Reconstruct path: src -> ... -> u -> src
                    path = [u]
                    while path[-1] != src:
                        path.append(pred[path[-1]])
                    path.reverse()
                    path.append(src)
                    found_cycle = path
                    break
                if v not in dist:
                    dist[v] = dist[u] + 1
                    pred[v] = u
                    q.append(v)
        if found_cycle and len(found_cycle) - 1 == L:
            return (cycle, movers, found_cycle, peel_set)
    return None


def main():
    n = 5
    tb = 3.0
    Mn = m_n_sharp(n)
    multisets = enumerate_multisets(n, Mn)
    # Pick a simple ms
    for ms in multisets[:20]:
        cycles = enumerate_all_cycles(ms, n, 16, tb, 5)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n + 2: continue
            result = dump_example(ms, n, cycle, movers, det)
            if result is None: continue
            c_path, c_movers, s_cycle, peel_set = result
            print(f"ms = {ms}, n = {n}, L = {L}")
            print(f"Good cycle C (length {L}):")
            for i, c in enumerate(c_path):
                print(f"  i={i:2d}  c_i = {c}   fires at p={c_movers[i]}")
            print(f"\nShadow L-cycle in peel(N_1) (length {len(s_cycle)-1}):")
            for j in range(len(s_cycle) - 1):
                c_s = s_cycle[j]
                c_next = s_cycle[j + 1]
                # Firing position and anchor to cycle
                p_fire = [k for k in range(n) if c_s[k] != c_next[k]][0]
                new_val = c_next[p_fire]
                # Hamming-1 anchors
                anchors = []
                for i, c in enumerate(c_path):
                    diffs = [k for k in range(n) if c[k] != c_s[k]]
                    if len(diffs) == 1:
                        q = diffs[0]; v = c_s[q]
                        anchors.append((i, q, v))
                print(f"  j={j:2d}  c_s={c_s}  anchors={anchors}  fires p={p_fire} → v'={new_val}")
            print(f"\n|peel(N_1)| = {len(peel_set)}")
            # First anchor sequence: pick one (i, q, v) per step
            print("\nFirst anchor at each step:")
            for j in range(len(s_cycle) - 1):
                c_s = s_cycle[j]
                for i, c in enumerate(c_path):
                    diffs = [k for k in range(n) if c[k] != c_s[k]]
                    if len(diffs) == 1:
                        q = diffs[0]; v = c_s[q]
                        print(f"  j={j:2d}  (i={i}, q={q}, v={v})")
                        break
            return  # print only one example
    print("No example found within scope.")


if __name__ == "__main__":
    main()
