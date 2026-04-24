#!/usr/bin/env python3
"""SK cycle structure probe: does the forced NG-graph always have a cycle
at sub-threshold multisets for n=5,6,7?

For each sub-threshold multiset, we enumerate good cycles via DFS (no
random system needed -- we build deterministic-consistency-preserving
cycles directly), then build the forced NG-graph and compute SK by
iterative sink removal.

Key questions:
  - Is SK always nonempty? (i.e., does the forced NG-graph always have a cycle?)
  - Is |SK| >= 2^(n-1) universal?
  - What is the cycle structure inside SK?
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys


# ── helpers ──────────────────────────────────────────────────────────────

def sub_threshold(n):
    """4 * 3^(n-2)."""
    return 4 * (3 ** (n - 2))


def enumerate_multisets(n, max_product):
    """Enumerate sorted tuples (m_0,...,m_{n-1}) with each m_i >= 2
    and product < max_product."""
    out = []
    def rec(i, prefix, prod, lo):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        remaining = n - i
        for m in range(lo, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (remaining - 1)
            if new_prod * min_remaining >= max_product:
                break
            rec(i + 1, prefix + [m], new_prod, m)
    rec(0, [], 1, 2)
    return out


def all_configs(ms):
    return list(iproduct(*[range(m) for m in ms]))


# ── cycle enumeration (DFS with det consistency) ─────────────────────────

def enumerate_cycles(ms, n, L_max, time_budget, max_cycles):
    """Enumerate fair simple good cycles via DFS.
    Returns list of (cycle_configs, movers, det)."""
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_norms = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        # Check if we can close the cycle
        if len(path) > 1 and config == start:
            if set(movers) == set(range(n)):
                L = len(movers)
                norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
                if norm not in seen_norms:
                    seen_norms.add(norm)
                    found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        path_set = set(path)
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                # Build new det with this move
                new_det = dict(det)
                new_det[km] = new_val
                # Check non-mover consistency
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False
                        break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in path_set:
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])

    return found


# ── forced graph / SK ────────────────────────────────────────────────────

def build_forced_ng_graph(ms, n, det, good_set):
    """Build forced graph restricted to NG = all_configs - good_set."""
    configs = all_configs(ms)
    ng_list = [c for c in configs if c not in good_set]
    ng_set = set(ng_list)

    adj = defaultdict(list)
    edge_count = 0
    for c in ng_list:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
                    edge_count += 1

    return ng_list, ng_set, adj, edge_count


def compute_sk(ng_list, adj):
    """Iterative sink removal. Returns (SK set, peeling_rounds, round_sizes)."""
    remaining = set(ng_list)
    rounds = []
    while True:
        sinks = set()
        for c in remaining:
            has_out = any(tgt in remaining for tgt, _ in adj.get(c, []))
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        rounds.append(len(sinks))
        remaining -= sinks
    return remaining, len(rounds), rounds


def find_sccs(sk_set, adj):
    """Tarjan's SCC (iterative). Returns list of non-trivial SCCs
    (size > 1, or size 1 with self-loop)."""
    sk_list = list(sk_set)
    if not sk_list:
        return []
    idx_map = {c: i for i, c in enumerate(sk_list)}
    N = len(sk_list)

    adj_idx = [[] for _ in range(N)]
    for c in sk_list:
        i = idx_map[c]
        for tgt, _ in adj.get(c, []):
            if tgt in sk_set:
                adj_idx[i].append(idx_map[tgt])

    index_counter = [0]
    stack = []
    on_stack = [False] * N
    index_arr = [-1] * N
    lowlink = [0] * N
    sccs = []

    for start in range(N):
        if index_arr[start] != -1:
            continue
        work = [(start, 0)]
        while work:
            v, ni = work[-1]
            if index_arr[v] == -1:
                index_arr[v] = index_counter[0]
                lowlink[v] = index_counter[0]
                index_counter[0] += 1
                stack.append(v)
                on_stack[v] = True

            done = True
            for j in range(ni, len(adj_idx[v])):
                w = adj_idx[v][j]
                if index_arr[w] == -1:
                    work[-1] = (v, j + 1)
                    work.append((w, 0))
                    done = False
                    break
                elif on_stack[w]:
                    lowlink[v] = min(lowlink[v], index_arr[w])

            if done:
                work.pop()
                if lowlink[v] == index_arr[v]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack[w] = False
                        scc.append(w)
                        if w == v:
                            break
                    sccs.append(scc)
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[v])

    # Keep only non-trivial SCCs
    result = []
    for scc in sccs:
        scc_idx_set = set(scc)
        if len(scc) > 1:
            result.append([sk_list[i] for i in scc])
        elif len(scc) == 1:
            # Check self-loop
            i = scc[0]
            if i in set(adj_idx[i]):
                result.append([sk_list[i]])
    return result


# ── main analysis ────────────────────────────────────────────────────────

def process_n(n, L_max, time_budget_per_ms, max_cycles_per_ms):
    threshold = sub_threshold(n)
    multisets = enumerate_multisets(n, threshold)
    print(f"\n{'='*72}")
    print(f"n = {n}, threshold = {threshold}, sub-threshold multisets: {len(multisets)}")
    print(f"L_max = {L_max}, time_budget/ms = {time_budget_per_ms}s, "
          f"max_cycles/ms = {max_cycles_per_ms}")
    print(f"{'='*72}")

    total_pairs = 0
    sk_empty_count = 0
    sk_nonempty_count = 0
    sk_sizes = []
    ng_sizes = []
    cycle_lengths = []
    peeling_rounds_all = []
    long_cycle_pairs = 0
    long_cycle_sk_empty = 0
    counterexamples = []

    for ms_idx, ms in enumerate(multisets):
        prod = 1
        for m in ms:
            prod *= m
        total_configs = prod
        t0 = time.time()
        print(f"\n  ms={ms}  product={prod}  total_configs={total_configs}  "
              f"[{ms_idx+1}/{len(multisets)}]")

        cycles = enumerate_cycles(ms, n, L_max, time_budget_per_ms, max_cycles_per_ms)
        elapsed = time.time() - t0
        print(f"    Found {len(cycles)} cycles in {elapsed:.1f}s")

        if not cycles:
            continue

        # Length distribution
        lengths = [len(c[0]) for c in cycles]
        len_counter = Counter(lengths)
        print(f"    Length distribution: {dict(sorted(len_counter.items()))}")

        for ci, (cycle, movers, det) in enumerate(cycles):
            L = len(cycle)
            good_set = set(tuple(c) for c in cycle)

            ng_list, ng_set, adj, edge_count = build_forced_ng_graph(ms, n, det, good_set)
            sk, num_rounds, round_sizes = compute_sk(ng_list, adj)

            total_pairs += 1
            ng_size = len(ng_list)
            sk_size = len(sk)
            ng_sizes.append(ng_size)
            sk_sizes.append(sk_size)
            cycle_lengths.append(L)
            peeling_rounds_all.append(num_rounds)

            is_long = (L >= 2 * n + 2)
            if is_long:
                long_cycle_pairs += 1

            # Count initial sinks
            sinks_in_ng = sum(1 for c in ng_list
                              if not any(tgt in ng_set for tgt, _ in adj.get(c, [])))

            if sk_size == 0:
                sk_empty_count += 1
                if is_long:
                    long_cycle_sk_empty += 1
                counterexamples.append({
                    'ms': ms, 'L': L, 'ng': ng_size,
                    'edges': edge_count, 'rounds': num_rounds,
                    'round_sizes': round_sizes,
                    'cycle': cycle, 'det': det,
                    'sinks0': sinks_in_ng,
                })
                tag = " *** SK=EMPTY ***"
            else:
                sk_nonempty_count += 1
                tag = ""

            if ci < 8 or sk_size == 0:
                # Find SCCs in SK
                sccs = find_sccs(sk, adj) if sk_size > 0 else []
                scc_sizes = sorted([len(s) for s in sccs], reverse=True)
                ratio = sk_size / ng_size if ng_size > 0 else 0

                print(f"    [{ci}] L={L}  |NG|={ng_size}  edges={edge_count}  "
                      f"|SK|={sk_size}({100*ratio:.0f}%)  "
                      f"peel={num_rounds}r  "
                      f"sinks0={sinks_in_ng}  "
                      f"SCCs={len(sccs)} {scc_sizes[:5]}{tag}")

    # ── Summary ──
    print(f"\n{'='*72}")
    print(f"SUMMARY for n={n}")
    print(f"{'='*72}")
    print(f"  Sub-threshold multisets: {len(multisets)}")
    print(f"  Total (multiset, cycle) pairs tested: {total_pairs}")
    print(f"  SK nonempty: {sk_nonempty_count}")
    print(f"  SK EMPTY (counterexamples): {sk_empty_count}")

    if sk_sizes:
        avg_sk = sum(sk_sizes) / len(sk_sizes)
        avg_ng = sum(ng_sizes) / len(ng_sizes)
        avg_ratio = avg_sk / avg_ng if avg_ng > 0 else 0
        min_sk = min(sk_sizes)
        max_sk = max(sk_sizes)
        print(f"  |SK| range: [{min_sk}, {max_sk}]")
        print(f"  Average |SK|={avg_sk:.1f}, |NG|={avg_ng:.1f}, ratio={100*avg_ratio:.1f}%")
        below_half = sum(1 for s in sk_sizes if s < 2**(n-1))
        print(f"  |SK| < 2^(n-1)={2**(n-1)}: {below_half}/{len(sk_sizes)}")

    if cycle_lengths:
        cl = Counter(cycle_lengths)
        print(f"  Cycle length distribution: {dict(sorted(cl.items()))}")

    if peeling_rounds_all:
        print(f"  Peeling rounds: avg={sum(peeling_rounds_all)/len(peeling_rounds_all):.1f}, "
              f"max={max(peeling_rounds_all)}")

    print(f"  Long cycles (L >= {2*n+2}): {long_cycle_pairs} tested, "
          f"{long_cycle_sk_empty} with SK=empty")

    if counterexamples:
        print(f"\n  *** {len(counterexamples)} COUNTEREXAMPLES (SK=empty) ***")
        for i, cx in enumerate(counterexamples[:10]):
            print(f"\n  Counterexample {i+1}:")
            print(f"    ms={cx['ms']}, L={cx['L']}, |NG|={cx['ng']}, "
                  f"edges={cx['edges']}, sinks0={cx['sinks0']}")
            print(f"    peeling: {cx['rounds']} rounds, sizes={cx['round_sizes']}")
            print(f"    cycle:")
            for j, c in enumerate(cx['cycle'][:15]):
                print(f"      [{j}] {c}")
            if cx['L'] > 15:
                print(f"      ... ({cx['L']} total)")
    else:
        print(f"\n  No counterexamples. SK always nonempty.")

    return total_pairs, sk_empty_count, counterexamples


def main():
    t0 = time.time()
    all_cx = []

    # n=5: product < 108, state spaces are small. Explore long cycles.
    pairs5, empty5, cx5 = process_n(
        n=5, L_max=30, time_budget_per_ms=30.0, max_cycles_per_ms=200)
    all_cx.extend(cx5)

    # n=6: product < 324. Larger spaces but still manageable.
    pairs6, empty6, cx6 = process_n(
        n=6, L_max=25, time_budget_per_ms=30.0, max_cycles_per_ms=100)
    all_cx.extend(cx6)

    # n=7: product < 972. Tight time budget.
    pairs7, empty7, cx7 = process_n(
        n=7, L_max=22, time_budget_per_ms=20.0, max_cycles_per_ms=50)
    all_cx.extend(cx7)

    elapsed = time.time() - t0
    print(f"\n{'='*72}")
    print(f"GLOBAL SUMMARY  ({elapsed:.1f}s)")
    print(f"{'='*72}")
    print(f"  Total counterexamples: {len(all_cx)}")
    if all_cx:
        print("  SK=empty cases found -- forced NG-graph is a DAG for these cycles.")
    else:
        print("  All tested pairs have nonempty SK.")
        print("  Consistent with: forced NG-graph always has a cycle at sub-threshold.")


if __name__ == "__main__":
    main()
