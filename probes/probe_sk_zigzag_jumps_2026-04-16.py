#!/usr/bin/env python3
"""Characterize the ~15% 'jump' steps in the zig-zag L-cycle.

Finding: H_lockstep (p_fire = movers[i], i advances) covers 85% of steps.
The remaining 15% are 'jump' steps where the anchor re-indexes.

For each NON-H step, record:
  J1. Is p_fire == q (anchor position)? — if yes, anchor-fires
  J2. What's q_{j+1} - q_j? (anchor position change)
  J3. What's i_{j+1} - i_j? (anchor index jump)
  J4. Is there a *different* matching anchor at step j that does lockstep?
  J5. Characterize jumps by (q_j, v_j) structure.

Also: maybe the rule is simpler if we pick the RIGHT anchor among multiple.
Some c_s have multiple anchors; H tests existence. Maybe the RIGHT rule is:
  'Pick the anchor with smallest i such that ...' — yielding 100% lockstep.
"""
from itertools import product as iproduct
from collections import defaultdict, deque, Counter
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
                    return peel, path
                if vv not in dist:
                    dist[vv] = dist[u] + 1
                    pred[vv] = u
                    qd.append(vv)
    return peel, None


def main():
    print("=" * 72, flush=True)
    print("Jump-step characterization", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 10, 3.0, 16),
        (6, 8, 5, 4.0, 17),
    ]
    jump_stats = Counter()
    total_jumps = 0
    total_steps = 0
    lockstep_via_anchor_selection = 0
    first_example_printed = False
    for (n, stride, max_cycles, tb, L_max) in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        rec_count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2: continue
                peel, path = compute_peel_and_cycle(ms, n, cycle, movers, det, L)
                if peel is None or path is None: continue
                rec_count += 1
                for j in range(L):
                    c_s = path[j]; c_s_next = path[j + 1]
                    diffs = [k for k in range(n) if c_s[k] != c_s_next[k]]
                    p_fire = diffs[0]
                    # All anchors of c_s
                    anchors = []
                    for i, c in enumerate(cycle):
                        dd = [k for k in range(n) if c[k] != c_s[k]]
                        if len(dd) == 1:
                            anchors.append((i, dd[0], c_s[dd[0]]))
                    # All anchors of c_s_next
                    anchors_next = []
                    for i, c in enumerate(cycle):
                        dd = [k for k in range(n) if c[k] != c_s_next[k]]
                        if len(dd) == 1:
                            anchors_next.append((i, dd[0], c_s_next[dd[0]]))
                    total_steps += 1
                    # Check lockstep: ∃ anchor (i, q, v) of c_s with
                    #   movers[i] = p_fire AND (i+1)%L, q, v in anchors_next
                    lockstep_exists = False
                    for (i, q, v) in anchors:
                        if movers[i] == p_fire:
                            if ((i + 1) % L, q, v) in anchors_next:
                                lockstep_exists = True
                                break
                    if lockstep_exists:
                        lockstep_via_anchor_selection += 1
                    else:
                        total_jumps += 1
                        # Characterize
                        # Is p_fire == q for some anchor?
                        afq = [(i, q, v) for (i, q, v) in anchors if q == p_fire]
                        # Number of anchors
                        jump_stats[f'n_anchors={len(anchors)}'] += 1
                        if afq:
                            jump_stats['p_fire_is_anchor_q'] += 1
                        # Does ANY anchor have movers[i] == p_fire?
                        mi_match = any(movers[i] == p_fire for (i, q, v) in anchors)
                        if mi_match:
                            jump_stats['some_anchor_i_has_movers_match'] += 1
                        # Dump one example
                        if not first_example_printed and ms == (2,2,2,2,3):
                            print(f"\nEXAMPLE jump at j={j}, ms={ms}, L={L}")
                            print(f"  c_s = {c_s}, c_s_next = {c_s_next}")
                            print(f"  p_fire = {p_fire}")
                            print(f"  anchors_c_s: {anchors}")
                            print(f"  movers at those i: {[movers[a[0]] for a in anchors]}")
                            print(f"  anchors_c_s_next: {anchors_next}")
                            first_example_printed = True
            if (idx + 1) % max(1, len(sampled) // 5) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  recs={rec_count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    print(f"Total steps: {total_steps}")
    print(f"Lockstep under ANCHOR SELECTION: {lockstep_via_anchor_selection}/{total_steps} "
          f"({100*lockstep_via_anchor_selection/total_steps:.2f}%)")
    print(f"Jump steps (no lockstep possible): {total_jumps}/{total_steps} "
          f"({100*total_jumps/total_steps:.2f}%)")
    print(f"\nJump breakdown:")
    for k, v in jump_stats.most_common():
        print(f"  {k}: {v}/{total_jumps}")


if __name__ == "__main__":
    main()
