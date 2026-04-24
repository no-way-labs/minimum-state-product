#!/usr/bin/env python3
"""Topological fiber probe for SK structure.

Central question: is SK ≠ ∅ captured by a lower-dimensional fiber cycle?

For position p and value v, the fiber F_{p,v} = {c ∈ VC : c[p] = v}.
Intra-fiber forced edges: position-q forced moves for q ≠ p (these stay in F).
Inter-fiber edges: position-p forced moves (these leave F).

We test:

  H1 (fiber reducibility): SK ≠ ∅ iff ∃ (p,v) s.t. the intra-fiber forced
      subgraph on F_{p,v} ∩ NG contains a directed cycle.

  H2 (which (p,v) work): distribution over (p,v) of "fiber carries SK witness".

  H3 (winding comparison): for mixed multisets, compute winding of cycle C
      around each axis with m_p ≥ 3 (cyclic order 0→1→...→m-1→0); compute
      winding of every short simple NG-forced cycle; ask whether NG-cycle
      windings differ systematically from C's winding.

  H4 (fiber SK count): for each (p,v), count |fiber_SK|. Does sum over
      fibers exceed or relate to |SK| as a whole?

Run at n=5,6 mixed (m_p >= 3 present), L >= 2n+2.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys


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


def build_forced_graph(ms, n, cycle, det):
    """Return (vc_ng, out_edges, edge_pos) where edge_pos[(c,c')] = position p."""
    cycle_set = set(cycle)
    V = value_sets(cycle, n)
    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    out_edges = defaultdict(set)
    edge_pos = {}
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in vc_ng:
                    out_edges[c].add(nc)
                    edge_pos[(c, nc)] = p
    return vc_ng, out_edges, edge_pos


def compute_sk(vc_ng, out_edges):
    remaining = set(vc_ng)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in out_edges[c])}
        if not sinks:
            break
        remaining -= sinks
    return remaining


def compute_fiber_sk(vc_ng, out_edges, edge_pos, p, v):
    """SK restricted to fiber F_{p,v}, using only intra-fiber edges (position != p)."""
    fiber = {c for c in vc_ng if c[p] == v}
    intra = defaultdict(set)
    for c in fiber:
        for t in out_edges[c]:
            if t in fiber and edge_pos[(c, t)] != p:
                intra[c].add(t)
    remaining = set(fiber)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in intra[c])}
        if not sinks:
            break
        remaining -= sinks
    return remaining, len(fiber)


def cyclic_step(a, b, m):
    """+1 if b=(a+1)%m, -1 if b=(a-1)%m, else 0 (non-cyclic move)."""
    if (a + 1) % m == b:
        return 1
    if (a - 1) % m == b:
        return -1
    return 0


def cycle_winding(cycle, movers, det, n, ms):
    """Winding vector of cycle C around each axis (treating V_p as Z/m_p)."""
    w = [0] * n
    L = len(movers)
    for k in range(L):
        p = movers[k]
        a = cycle[k][p]
        b = cycle[(k + 1) % L][p]
        w[p] += cyclic_step(a, b, ms[p])
    return tuple(w)


def find_short_ng_cycles(vc_ng, out_edges, max_len):
    """Find some short simple directed cycles in the NG forced graph."""
    found = []
    seen = set()
    # DFS from each SK vertex; we keep cycles up to length max_len.
    sk = compute_sk(vc_ng, out_edges)
    for start in sk:
        stack = [(start, [start], {start})]
        while stack:
            node, path, on_path = stack.pop()
            if len(path) > max_len:
                continue
            for t in out_edges[node]:
                if t == start and len(path) >= 2:
                    norm = tuple(path)
                    # rotate to smallest
                    L = len(norm)
                    rot = min(tuple(norm[i:] + norm[:i]) for i in range(L))
                    if rot not in seen:
                        seen.add(rot)
                        found.append(list(norm))
                        if len(found) >= 500:
                            return found
                elif t in sk and t not in on_path:
                    stack.append((t, path + [t], on_path | {t}))
    return found


def ng_cycle_winding(cycle_path, edge_pos, n, ms):
    w = [0] * n
    L = len(cycle_path)
    for k in range(L):
        c1 = cycle_path[k]
        c2 = cycle_path[(k + 1) % L]
        p = edge_pos[(c1, c2)]
        w[p] += cyclic_step(c1[p], c2[p], ms[p])
    return tuple(w)


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    vc_ng, out_edges, edge_pos = build_forced_graph(ms, n, cycle, det)
    sk = compute_sk(vc_ng, out_edges)

    # H1: fiber reducibility
    fiber_results = []
    any_fiber_nonempty = False
    for p in range(n):
        for v in set(c[p] for c in cycle):
            fiber_sk, fiber_size = compute_fiber_sk(vc_ng, out_edges, edge_pos, p, v)
            if fiber_sk:
                any_fiber_nonempty = True
            fiber_results.append({
                'p': p, 'v': v, 'fiber_size': fiber_size,
                'fiber_sk': len(fiber_sk),
            })

    # H3/H4: windings
    c_w = cycle_winding(cycle, movers, det, n, ms)
    # NG cycle windings (up to some short length)
    ng_cycles = find_short_ng_cycles(vc_ng, out_edges, max_len=2 * n + 2)
    ng_windings = Counter()
    for path in ng_cycles:
        w = ng_cycle_winding(path, edge_pos, n, ms)
        ng_windings[w] += 1

    return {
        'n': n, 'ms': ms, 'L': L,
        'vc_ng': len(vc_ng),
        'sk': len(sk),
        'sk_empty': len(sk) == 0,
        'fiber_nonempty_any': any_fiber_nonempty,
        'fibers_with_sk': sum(1 for f in fiber_results if f['fiber_sk'] > 0),
        'total_fiber_sk': sum(f['fiber_sk'] for f in fiber_results),
        'c_winding': c_w,
        'n_ng_cycles_sampled': len(ng_cycles),
        'ng_winding_classes': len(ng_windings),
        'ng_windings': dict(ng_windings),
    }


def main():
    print("=" * 72)
    print("Topological fiber probe: SK structure via fiber reduction + windings")
    print("=" * 72)

    plan = [
        (5, 1, 400, 3.0, 16),
        (6, 15, 30, 2.0, 14),
    ]

    all_records = []

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        mixed = [ms for ms in multisets if max(ms) >= 3]
        sampled = mixed[::stride]
        print(f"\n=== n={n}  {len(sampled)} mixed multisets (of {len(mixed)}) ===")
        t0 = time.time()
        n_start_idx = len(all_records)
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
            if (idx + 1) % 5 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx + 1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={len(all_records)-n_start_idx}", flush=True)

    if not all_records:
        print("No records collected. Increasing budget may be needed.")
        return

    # H1 test: fiber reducibility
    print(f"\n{'='*72}")
    print(f"H1: SK!=∅ iff some fiber has intra-fiber SK cycle")
    print(f"{'='*72}")
    sk_ne_and_fiber = sum(1 for r in all_records if not r['sk_empty'] and r['fiber_nonempty_any'])
    sk_ne_no_fiber = sum(1 for r in all_records if not r['sk_empty'] and not r['fiber_nonempty_any'])
    sk_empty_fiber = sum(1 for r in all_records if r['sk_empty'] and r['fiber_nonempty_any'])
    sk_empty_no_fiber = sum(1 for r in all_records if r['sk_empty'] and not r['fiber_nonempty_any'])
    print(f"  SK!=∅ AND fiber-SK: {sk_ne_and_fiber}")
    print(f"  SK!=∅ AND no fiber-SK: {sk_ne_no_fiber}   (<-- counterexamples to H1)")
    print(f"  SK=∅ AND fiber-SK: {sk_empty_fiber}   (<-- impossible if fibers ⊆ NG)")
    print(f"  SK=∅ AND no fiber-SK: {sk_empty_no_fiber}")
    print(f"  Total: {len(all_records)}")

    # Fiber counting
    print(f"\n  Fibers with SK distribution:")
    fd = Counter(r['fibers_with_sk'] for r in all_records)
    for k in sorted(fd):
        print(f"    {k} fibers with SK: {fd[k]} records")

    # H3 test: winding analysis
    print(f"\n{'='*72}")
    print(f"H3: winding-class comparison (mixed ms with m_p>=3)")
    print(f"{'='*72}")
    windings_equal_c = 0
    ng_has_other_class = 0
    ng_has_no_cycles = 0
    for r in all_records:
        if r['n_ng_cycles_sampled'] == 0:
            ng_has_no_cycles += 1
            continue
        classes = set(r['ng_windings'].keys())
        if r['c_winding'] in classes and len(classes) == 1:
            windings_equal_c += 1
        if any(w != r['c_winding'] for w in classes):
            ng_has_other_class += 1
    print(f"  Records with ≥1 sampled NG cycle: {len(all_records)-ng_has_no_cycles}")
    print(f"  NG cycles all = C's winding class: {windings_equal_c}")
    print(f"  NG has cycle with DIFFERENT winding class: {ng_has_other_class}")
    print(f"  No NG cycles sampled (SK=∅ or deep): {ng_has_no_cycles}")

    # Show some examples
    print(f"\n  Example winding distributions (first 6):")
    shown = 0
    for r in all_records:
        if r['n_ng_cycles_sampled'] == 0:
            continue
        print(f"    n={r['n']} ms={r['ms']} L={r['L']} |SK|={r['sk']}")
        print(f"      C winding: {r['c_winding']}")
        print(f"      NG winding classes ({r['ng_winding_classes']}):")
        for w, cnt in sorted(r['ng_windings'].items(), key=lambda x: -x[1])[:5]:
            diff = " (= C)" if w == r['c_winding'] else ""
            print(f"         {w}: {cnt} cycles{diff}")
        shown += 1
        if shown >= 6:
            break


if __name__ == "__main__":
    main()
