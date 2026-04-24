#!/usr/bin/env python3
"""Rank / Euler characteristic angle on F|_{VC-NG} for |SK| ≥ 2^(n-1).

Approach:
  Every SK node has ≥1 outgoing forced edge within SK (that's the fixpoint def).
  So |E(F|_SK)| ≥ |SK|.

  Each forced-move rule (p, L, S, R) → val contributes at most
     ∏_{i ∉ {p-1, p, p+1}} |V_i|
  potential edges, and at most
     ∏_{i ∉ {p-1, p, p+1}} |V_i|  −  |{(x_{p-1}, x_p, x_{p+1}) = (L,S,R) configs in C}|
  edges into VC_NG.

  Summing over rules that actually yield edges in SK gives an UPPER bound on
  |E(F|_SK)|. If the upper bound ≥ |SK|, that's consistent; if we can invert it,
  we can bound |SK| from below in terms of # rules and ring freedom.

  Concrete: for each (ms, cycle) compute
    |SK|, |E|, out-deg distribution, in-deg distribution,
    per-rule edge contribution, upper bound from rule count,
    and a candidate lower bound |SK| ≤ |E| ≤ (sum over rules).

  Also: count SHORT cycles (length 2 — pairs of mutually forced-reachable
  configs) and longer primitive cycles. If every forced SCC contains many
  2-cycles, the SCC size is related to # 2-cycles.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk_and_adj(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)
    remaining = set(non_good)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        remaining -= sinks
    return remaining, adj, V_sorted, move_entries


def rank_analysis(sk, adj, V_sorted, move_entries, n, cycle):
    """Compute rank-like invariants on F|_SK."""
    if not sk:
        return None
    # Edges in SK
    edges = []
    for c in sk:
        for t in adj.get(c, []):
            if t in sk:
                edges.append((c, t))
    num_edges = len(edges)
    # Out-degrees and in-degrees within SK
    outdeg = Counter()
    indeg = Counter()
    for u, v in edges:
        outdeg[u] += 1; indeg[v] += 1
    out_vals = [outdeg.get(c, 0) for c in sk]
    in_vals = [indeg.get(c, 0) for c in sk]
    out_hist = Counter(out_vals)
    in_hist = Counter(in_vals)
    # 2-cycles: pairs (u, v) with u→v and v→u within SK
    two_cycles = set()
    edge_set = set(edges)
    for u, v in edges:
        if (v, u) in edge_set:
            two_cycles.add(frozenset({u, v}))
    # Self-loops
    self_loops = sum(1 for u, v in edges if u == v)
    # Per-rule edge contribution
    rule_contrib = Counter()
    cycle_set = set(cycle)
    ng_set = set(tuple(cfg) for cfg in iproduct(*V_sorted)) - cycle_set
    for (p, L, S, R), val in move_entries.items():
        # count how many SK configs c have c[p-1]=L, c[p]=S, c[p+1]=R,
        # and whose image (c with c[p]=val) is also in SK
        count = 0
        for c in sk:
            if c[(p-1)%n] == L and c[p] == S and c[(p+1)%n] == R:
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in sk:
                    count += 1
        rule_contrib[(p, L, S, R, val)] = count
    # Context frequency analysis
    active_rules = {k: v for k, v in rule_contrib.items() if v > 0}
    max_rule_contrib = max(rule_contrib.values()) if rule_contrib else 0
    total_free_product = sum(rule_contrib.values())  # should equal |E|
    # Theoretical max edges per rule: product over i not in {p-1,p,p+1} of |V_i|
    rule_max = {}
    for (p, L, S, R), val in move_entries.items():
        prod = 1
        for i in range(n):
            if i not in {(p-1)%n, p, (p+1)%n}:
                prod *= len(V_sorted[i])
        rule_max[(p, L, S, R, val)] = prod
    # Information: how close is actual to theoretical max?
    return {
        'sk_size': len(sk),
        'num_edges': num_edges,
        'out_hist': dict(out_hist),
        'in_hist': dict(in_hist),
        'num_2cycles': len(two_cycles),
        'num_self_loops': self_loops,
        'num_active_rules': len(active_rules),
        'max_rule_contrib': max_rule_contrib,
        'total_rule_contrib': sum(rule_contrib.values()),
        'free_prod_available': sum(rule_max.values()),
        'edges_minus_nodes': num_edges - len(sk),
        'min_out': min(out_vals), 'min_in': min(in_vals),
    }


def main():
    print("=" * 100)
    print("RANK / EDGE-COUNT ANGLE: bounds on |SK| via |E(F|_SK)|")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,2,3), (2,2,2,3,3), (2,2,2,3,4), (2,2,3,3,3)], 16, 8, 25.0),
        (6, [(2,2,2,3,3,3), (2,2,3,3,3,3)], 17, 4, 40.0),
        (7, [(2,2,2,3,3,3,3)], 17, 2, 45.0),
        (8, [(2,2,2,3,3,3,3,3)], 19, 1, 60.0),
    ]

    all_recs = []
    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound=2^{n-1}={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                sk, adj, V_sorted, move_entries = compute_sk_and_adj(ms, n, cycle, det)
                if not sk: continue
                r = rank_analysis(sk, adj, V_sorted, move_entries, n, cycle)
                r['n'] = n; r['ms'] = ms; r['L'] = len(cycle); r['bound'] = bound
                all_recs.append(r)
                print(f"  ms={ms} L={len(cycle)} |SK|={r['sk_size']:4d} |E|={r['num_edges']:4d} "
                      f"2cyc={r['num_2cycles']:3d} rules={r['num_active_rules']:3d} "
                      f"min_out={r['min_out']} min_in={r['min_in']} |E|-|V|={r['edges_minus_nodes']}")

    # Analyze
    print("\n" + "=" * 100)
    print("RANK RELATIONSHIPS")
    print("=" * 100)
    for n in sorted({r['n'] for r in all_recs}):
        recs = [r for r in all_recs if r['n'] == n]
        bound = 2 ** (n - 1)
        print(f"\n  n={n}  bound={bound}  trials={len(recs)}")
        for r in recs[:5]:
            # In-degree/out-degree sums:
            # |E| = sum of out-degs = sum of in-degs = sum of rule contribs
            E = r['num_edges']; V = r['sk_size']
            ratio = E / V if V else 0
            # Min out-degree: is it 1? If so, |E| ≥ |SK|
            # Max possible edges: if each node had max out-deg = # rules fired
            print(f"    ms={r['ms']} L={r['L']}  |SK|={V} |E|={E} "
                  f"|E|/|SK|={ratio:.2f} 2cyc={r['num_2cycles']} "
                  f"rules={r['num_active_rules']} free_prod={r['free_prod_available']}")
        # Aggregate check: is |E|/|SK| ≥ some constant?
        ratios = [r['num_edges']/r['sk_size'] for r in recs if r['sk_size']]
        if ratios:
            print(f"    |E|/|SK| range: [{min(ratios):.2f}, {max(ratios):.2f}]")

    # Check: sum over rules equals |E|?
    # And: is there a lower bound |SK| ≥ bound expressible via min_in/min_out?
    print("\n" + "=" * 100)
    print("KNASTER-TARSKI VERIFICATION + DEGREE BOUNDS")
    print("=" * 100)
    # If min_out ≥ 1 always (fixpoint), and min_in ≥ 1 (recurrence), we have
    #   |SK| ≤ |E| ≤ |SK| · max_out
    # Not a lower bound by itself. But if every SK node participates in a 2-cycle,
    # then |SK| ≤ 2 · |2-cycles|, i.e., # 2-cycles ≥ |SK|/2.
    for r in all_recs[:10]:
        n = r['n']; bound = r['bound']
        cov = 2 * r['num_2cycles'] / r['sk_size'] if r['sk_size'] else 0
        # Does every SK node have at least one 2-cycle neighbor?
        print(f"    n={n} L={r['L']} |SK|={r['sk_size']:4d} 2-cycles={r['num_2cycles']:3d} "
              f"2·|2c|/|SK|={cov:.3f} ({'full' if cov >= 1 else 'partial'})")


if __name__ == "__main__":
    main()
