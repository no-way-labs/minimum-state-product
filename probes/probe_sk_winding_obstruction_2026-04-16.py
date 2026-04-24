#!/usr/bin/env python3
"""Exploration 6: Winding obstruction for SK ≥ 1.

The forced graph on VC-NG has a directed cycle iff no potential function
r: VC-NG → ℤ exists where r increases along every forced edge.

Each forced edge changes one coordinate on a ring. The det transitions
at position p depend on ring neighbors (c[p-1], c[p+1]). If the
monotonicity constraints from adjacent positions "wind" around the ring,
no potential exists.

Concrete formalization: assign a "direction" to each det move entry.
Entry (p, a, b, d) → e changes c[p] from b to e. Define the "signed
shift" δ_p = e - b (mod m_p). The winding number W is the sum of
signed shifts around a forced path that traverses all positions.

If W ≠ 0 (mod something), no potential exists, and the forced graph
has a cycle.

This probe:
1. For each cycle, compute the "signed shifts" of all det move entries
2. Look for forced PATHS in the VC-NG graph that wind around the ring
3. Test whether such paths always exist at sub-M_n
4. Characterize the winding structure

KEY INSIGHT TO TEST: Does every forced cycle in the VC-NG graph have
nonzero winding? If so, SK ≥ 1 follows from the existence of ANY
forced cycle, which follows from edge density > 1.

Actually, let me think about this differently. The winding obstruction
is about the IMPOSSIBILITY of a consistent potential, not about
finding specific cycles.

A potential r: VC-NG → ℤ must satisfy r(c') > r(c) for every forced
edge c → c'. Each edge changes one coordinate. Define:
  Δr(c, p) = r(c') - r(c) where c' = c with c[p] changed by the det.

For consistency: Δr(c, p) > 0 for every matching (c, p).

Now consider a "loop" of transitions: start at some config c₀, apply
forced moves at positions p₁, p₂, ..., pₖ, and return to c₀. The
total potential change must be 0 (since r(c₀) = r(c₀)). But each
step has Δr > 0, so the total is > 0. Contradiction.

So: if a FORCED LOOP exists in VC-NG, no potential exists, and SK ≥ 1.

A forced loop = directed cycle in the forced graph. This is EXACTLY
what SK ≥ 1 means. So the winding argument is: prove that the forced
graph has a directed cycle.

OK so let me think about what the WINDING adds. The winding is a
property of the POSITIONS visited, not just the configs.

Define the "position winding" of a path c₀ →^{p₁} c₁ →^{p₂} c₂ → ...
as the sequence of mover positions (p₁, p₂, ...). If the movers make
a "net rotation" around the ring, the path has nonzero winding.

HYPOTHESIS: in the VC-NG forced graph, every connected component with
a cycle has a cycle whose mover sequence winds around the ring. And
winding around the ring forces the coordinate values to shift in a way
that can't return to the start without creating a topological
obstruction at sub-M_n.

Let me test this computationally.
"""
from itertools import product as iproduct
from collections import defaultdict, deque
import time
import sys


N_PROC = 5
TARGET = 1  # We only need SK >= 1


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_mixed_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product and max(prefix) >= 3:
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


def find_forced_cycles(ms, n, cycle, det):
    """Find ALL directed cycles in the forced graph on VC-NG.

    Returns list of (cycle_configs, mover_sequence) for each forced cycle.
    """
    cycle_set = set(cycle)
    V = value_sets(cycle, n)

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_ng = set(iproduct(*vc_ranges)) - cycle_set

    # Build forced graph with labeled edges (position p)
    out_edges = {}  # c -> list of (target, position, delta)
    for c in vc_ng:
        edges = []
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                old_val = c[p]
                new_val = move_entries[key]
                nc[p] = new_val
                nc = tuple(nc)
                if nc in vc_ng:
                    delta = (new_val - old_val) % ms[p]
                    edges.append((nc, p, delta))
        out_edges[c] = edges

    # Find shortest cycle using BFS from each vertex
    shortest_cycles = []

    # Use DFS to find cycles, tracking mover sequence
    # For efficiency, only find cycles up to length 2*n+10
    max_cycle_len = 3 * n

    for start in vc_ng:
        # DFS with path tracking
        stack = [(start, [start], [], set([start]))]
        while stack:
            curr, path, movers, visited = stack.pop()
            if len(path) > max_cycle_len:
                continue
            for tgt, pos, delta in out_edges.get(curr, []):
                if tgt == start and len(path) > 1:
                    # Found a cycle!
                    shortest_cycles.append((list(path), movers + [pos]))
                    continue
                if tgt in visited:
                    continue
                stack.append((tgt, path + [tgt], movers + [pos],
                             visited | {tgt}))
            # Only find first few cycles per start
            if len(shortest_cycles) > 100:
                break
        if len(shortest_cycles) > 1000:
            break

    return shortest_cycles, out_edges, vc_ng


def analyze_winding(ms, n, forced_cycles, out_edges, vc_ng):
    """Analyze the winding structure of forced cycles.

    For each forced cycle, compute:
    1. The mover sequence (which positions fire)
    2. The "position winding" — does the mover sequence wrap around the ring?
    3. The "value shifts" at each position
    4. The net signed shift per position
    """
    results = []
    for path, movers in forced_cycles[:50]:  # analyze up to 50
        L = len(movers)
        # Position histogram
        pos_counts = defaultdict(int)
        for p in movers:
            pos_counts[p] += 1

        # Net value shift at each position
        net_shift = [0] * n
        for t in range(L):
            p = movers[t]
            c = path[t]
            c_next = path[(t + 1) % L]
            shift = (c_next[p] - c[p]) % ms[p]
            net_shift[p] = (net_shift[p] + shift) % ms[p]

        # Does the mover sequence "wind" around the ring?
        # Define winding as: do the movers visit all positions in a
        # cyclic order? Look for the longest monotone subsequence.
        mover_positions = [p for p in movers]

        # Check if net shift is zero at all positions
        # (must be zero for a cycle, since we return to start)
        net_zero = all(s == 0 for s in net_shift)

        results.append({
            'length': L,
            'movers': mover_positions,
            'pos_counts': dict(pos_counts),
            'net_shift': net_shift,
            'net_zero': net_zero,
            'positions_used': len(pos_counts),
        })

    return results


def compute_sk(ms, n, cycle, det):
    """Compute |SK| quickly."""
    cycle_set = set(cycle)
    V = value_sets(cycle, n)
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_ng = set(iproduct(*vc_ranges)) - cycle_set
    out_targets = {}
    for c in vc_ng:
        targets = []
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in vc_ng:
                    targets.append(nc)
        out_targets[c] = targets
    remaining = set(vc_ng)
    while True:
        sinks = [c for c in remaining
                 if not any(t in remaining for t in out_targets[c])]
        if not sinks:
            break
        for c in sinks:
            remaining.discard(c)
    return len(remaining)


def main():
    n = N_PROC
    Mn = m_n_sharp(n)

    print("=" * 72, flush=True)
    print(f"Exploration 6: Winding obstruction analysis, n={n}", flush=True)
    print("=" * 72, flush=True)

    multisets = enumerate_mixed_multisets(n, Mn)
    # Sample a few representative multisets
    sample = []
    seen_products = set()
    for ms in multisets:
        prod = 1
        for m in ms:
            prod *= m
        if prod not in seen_products:
            sample.append(ms)
            seen_products.add(prod)
    # Also add a specific one from each product class
    sample = sample[:6]

    print(f"\nTesting {len(sample)} representative multisets", flush=True)

    for ms in sample:
        prod = 1
        for m in ms:
            prod *= m
        print(f"\n{'='*60}", flush=True)
        print(f"ms={ms}  product={prod}", flush=True)

        cycles = enumerate_all_cycles(ms, n, 18, 10.0, 500)
        print(f"  Found {len(cycles)} good cycles", flush=True)

        # For each good cycle, find forced cycles in VC-NG
        total_forced = 0
        cycle_details = []

        for ci, (cyc, movers, det) in enumerate(cycles[:20]):
            L = len(movers)
            sk = compute_sk(ms, n, cyc, det)
            forced, out_edges, vc_ng = find_forced_cycles(ms, n, cyc, det)
            total_forced += len(forced)

            if forced:
                winding = analyze_winding(ms, n, forced, out_edges, vc_ng)
                # Characterize the shortest forced cycle
                shortest = min(forced, key=lambda x: len(x[1]))
                s_len = len(shortest[1])
                s_movers = shortest[1]
                s_positions = len(set(s_movers))

                # Key: does the shortest forced cycle visit ALL positions?
                all_pos = s_positions == n
                cycle_details.append({
                    'good_L': L,
                    'sk': sk,
                    'num_forced': len(forced),
                    'shortest_forced_len': s_len,
                    'shortest_movers': s_movers[:20],
                    'all_positions': all_pos,
                    'net_zero': winding[0]['net_zero'] if winding else None,
                })
            else:
                cycle_details.append({
                    'good_L': L,
                    'sk': sk,
                    'num_forced': 0,
                })

        # Summary for this multiset
        print(f"  Forced cycles found: {total_forced}", flush=True)
        for d in cycle_details[:10]:
            if d['num_forced'] > 0:
                print(f"    good_L={d['good_L']}  SK={d['sk']}  "
                      f"forced={d['num_forced']}  "
                      f"shortest={d['shortest_forced_len']}  "
                      f"all_pos={'Y' if d['all_positions'] else 'N'}  "
                      f"movers={d['shortest_movers']}", flush=True)
            else:
                print(f"    good_L={d['good_L']}  SK={d['sk']}  "
                      f"NO forced cycles found (search limit)", flush=True)

    # === KEY QUESTION: Do all forced cycles visit all n positions? ===
    print(f"\n{'='*72}", flush=True)
    print("KEY QUESTION: Do forced cycles always visit all positions?",
          flush=True)
    print("If YES: the mover sequence winds around the ring, giving a",
          flush=True)
    print("topological obstruction to any potential function.", flush=True)


if __name__ == "__main__":
    main()
