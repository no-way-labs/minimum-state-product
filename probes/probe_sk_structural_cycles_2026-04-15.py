#!/usr/bin/env python3
"""Structural probe: WHY is the forced graph never a DAG at sub-M_n?

Instead of counting |SK|, find the STRUCTURAL reason SK ≠ ∅.
For each fair cycle at sub-M_n with L ≥ 2n+2:

1. Forced 2-cycles: pairs (c, c') where c→c' and c'→c in the forced
   graph. These are permanent SK members — immune to sink removal.
   If they always exist, that's the proof.

2. Minimum cycle length in the forced graph (shortest directed cycle).
   If always ≤ some small constant, the proof is "find a short cycle."

3. Forced edges per det entry: how many NG configs match each
   (p, L, S, R) pattern? High fan-out means the det "forces"
   many configs simultaneously → structural dependencies.

4. The "self-supporting set": the smallest subset S ⊆ NG where
   every member of S has at least one forced edge to another member
   of S. This is exactly SK. What's the typical structure of the
   minimum such set?

5. Forced 2-cycles via the p*-toggle: at a min-fc processor p* with
   value set {v0, v1}, does det(p*, L, v0, R) = v1 AND
   det(p*, L, v1, R) = v0 for some (L, R) context? If so, every
   config c with c[left(p*)] = L and c[right(p*)] = R has BOTH
   (c with c[p*]=v0) and (c with c[p*]=v1) forming a 2-cycle.
   This gives a whole FAMILY of 2-cycles.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys

sys.setrecursionlimit(20000)


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
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


def analyze_forced_graph(ms, n, cycle, det):
    """Build the forced graph on NG(C) and analyze its cycle structure."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycle_set = set(cycle)
    ng = [c for c in all_configs if c not in cycle_set]
    ng_set = set(ng)

    # Build adjacency: c -> list of (target, position)
    adj = defaultdict(list)
    for c in ng:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))

    # 1. Find forced 2-cycles
    two_cycles = []
    seen_pairs = set()
    for c in ng:
        for tgt, p in adj.get(c, []):
            if tgt in adj:
                for back, p2 in adj[tgt]:
                    if back == c:
                        pair = (min(c, tgt), max(c, tgt))
                        if pair not in seen_pairs:
                            seen_pairs.add(pair)
                            two_cycles.append((c, tgt, p, p2))

    # 2. Find forced 2-cycles specifically at p* (min-fc toggle)
    fv_list = [0] * n
    for p in [cycle[i] for i in range(len(cycle))]:
        pass  # wrong, need movers
    # Skip mover-based analysis; just count 2-cycles

    # 3. Compute SK (for comparison)
    remaining = set(ng)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    sk = remaining

    # 4. Shortest cycle in the forced graph (BFS from each SK member)
    shortest_cycle = float('inf')
    if sk:
        for start in list(sk)[:50]:  # sample for speed
            dist = {start: 0}
            queue = [start]
            found = False
            while queue and not found:
                c = queue.pop(0)
                for tgt, _ in adj.get(c, []):
                    if tgt == start and dist[c] > 0:
                        shortest_cycle = min(shortest_cycle, dist[c] + 1)
                        found = True
                        break
                    if tgt not in dist and tgt in sk:
                        dist[tgt] = dist[c] + 1
                        if dist[tgt] < shortest_cycle:
                            queue.append(tgt)

    # 5. Edge density
    total_edges = sum(len(v) for v in adj.values())

    return {
        'ng_size': len(ng),
        'sk_size': len(sk),
        'num_2cycles': len(two_cycles),
        'shortest_cycle': shortest_cycle if shortest_cycle < float('inf') else -1,
        'total_edges': total_edges,
        'two_cycle_positions': [(p1, p2) for _, _, p1, p2 in two_cycles[:10]],
    }


def analyze_toggle_2cycles(ms, n, cycle, movers, det):
    """Check if the det dictionary creates toggle 2-cycles at any position.

    A toggle 2-cycle at position p means: there exists a context (L, R)
    such that det(p, L, v0, R) = v1 AND det(p, L, v1, R) = v0 for
    some v0 ≠ v1. Then EVERY config c with c[left(p)]=L, c[right(p)]=R
    and c[p] ∈ {v0, v1} participates in a 2-cycle (c ↔ c').
    """
    toggles = []
    for p in range(n):
        # Collect all det entries at position p
        entries = {}
        for (pp, L, S, R), val in det.items():
            if pp == p and val != S:
                entries[(L, S, R)] = val
        # Check for toggles: (L, v0, R) → v1 AND (L, v1, R) → v0
        for (L, v0, R), v1 in entries.items():
            if (L, v1, R) in entries and entries[(L, v1, R)] == v0:
                toggles.append((p, L, v0, v1, R))

    # For each toggle, count how many NG configs participate
    cycle_set = set(cycle)
    toggle_participants = 0
    for p, Lval, v0, v1, Rval in toggles:
        # Configs with c[left(p)]=Lval, c[right(p)]=Rval, c[p] ∈ {v0,v1}
        for v in [v0, v1]:
            for other_vals in iproduct(*[range(ms[i]) for i in range(n) if i != p
                                         and i != (p-1) % n and i != (p+1) % n]):
                c = [0] * n
                c[p] = v
                c[(p-1) % n] = Lval
                c[(p+1) % n] = Rval
                idx = 0
                for i in range(n):
                    if i != p and i != (p-1) % n and i != (p+1) % n:
                        c[i] = other_vals[idx]
                        idx += 1
                c = tuple(c)
                if c not in cycle_set:
                    toggle_participants += 1

    return {
        'num_toggles': len(toggles),
        'toggle_positions': [(p, Lval, v0, v1, Rval) for p, Lval, v0, v1, Rval in toggles[:5]],
        'toggle_participants': toggle_participants,
    }


def main():
    print("=" * 72, flush=True)
    print("Structural probe: forced-graph cycle analysis at sub-M_n", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1, 1500, 6.0, 15),
        (6, 4,  500, 4.0, 17),
        (7, 20, 150, 3.0, 17),
    ]

    # Aggregation
    has_2cycle = Counter()       # (n, L) -> count of cycles with ≥1 forced 2-cycle
    has_toggle = Counter()       # (n, L) -> count with toggle 2-cycles
    total_by_nL = Counter()
    min_shortest = {}            # (n, L) -> min shortest cycle length
    toggle_always = Counter()    # how often toggles exist
    toggle_pos_hist = Counter()  # which positions have toggles

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
                if L < 2 * n:
                    continue
                key = (n, L)
                total_by_nL[key] += 1

                # Forced graph analysis
                fg = analyze_forced_graph(ms, n, cycle, det)
                if fg['num_2cycles'] > 0:
                    has_2cycle[key] += 1
                if fg['shortest_cycle'] > 0:
                    if key not in min_shortest or fg['shortest_cycle'] < min_shortest[key]:
                        min_shortest[key] = fg['shortest_cycle']

                # Toggle analysis (only for L >= 2n+2 to save time)
                if L >= 2 * n + 2:
                    tg = analyze_toggle_2cycles(ms, n, cycle, movers, det)
                    if tg['num_toggles'] > 0:
                        has_toggle[key] += 1
                        toggle_always[key] += 1
                    for p, L_v, v0, v1, R_v in tg.get('toggle_positions', []):
                        # Categorize by fire count of toggle position
                        fv = [0] * n
                        for m in movers:
                            fv[m] += 1
                        toggle_pos_hist[(n, fv[p])] += 1

            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s", flush=True)

    print(f"\n{'='*72}", flush=True)
    print(f"=== Forced 2-cycle prevalence ===", flush=True)
    print(f"  n  L   total  has_2cycle  rate", flush=True)
    for key in sorted(total_by_nL.keys()):
        n, L = key
        total = total_by_nL[key]
        c2 = has_2cycle.get(key, 0)
        rate = 100 * c2 / total if total else 0
        flag = " !" if rate < 100 else ""
        print(f"  {n}  {L:2d}  {total:5d}  {c2:5d}      {rate:5.1f}%{flag}", flush=True)

    print(f"\n=== Toggle 2-cycle prevalence (L >= 2n+2 only) ===", flush=True)
    print(f"  n  L   total  has_toggle  rate", flush=True)
    for key in sorted(has_toggle.keys()):
        n, L = key
        total = total_by_nL[key]
        tg = has_toggle[key]
        rate = 100 * tg / total if total else 0
        flag = " !" if rate < 100 else ""
        print(f"  {n}  {L:2d}  {total:5d}  {tg:5d}      {rate:5.1f}%{flag}", flush=True)

    print(f"\n=== Toggle position fire-count distribution ===", flush=True)
    for (n, fc), cnt in sorted(toggle_pos_hist.items()):
        print(f"  n={n}  fc={fc}: {cnt}", flush=True)

    print(f"\n=== Shortest forced cycle (across all cycles) ===", flush=True)
    for key in sorted(min_shortest.keys()):
        print(f"  n={key[0]}  L={key[1]}  shortest_cycle={min_shortest[key]}", flush=True)


if __name__ == "__main__":
    main()
