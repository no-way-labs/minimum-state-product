#!/usr/bin/env python3
"""
CΦ 6-tuple verification at n=10 + TP-reachable fc spectrum comparison n=9 vs n=10.

Task 1: Verify the 617-edge 6-tuple set extends from n=9 to n=10.
Task 2: Compare TP-reachable fc spectra across boundary configs at n=9 vs n=10.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque

# --- Helper functions (same as proof107) ---

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)

def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def boundary6(c, n):
    """Extract boundary 6-tuple: (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])."""
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def encode6(t6):
    """Encode 6-tuple as mixed-radix integer.
    c[0] in {0,1} (mod 2), c[1..4] in {0,1,2} (mod 3), c[5] in {0,1} (mod 2).
    Encoding: c[0]*1 + c[1]*2 + c[2]*6 + c[3]*18 + c[4]*54 + c[5]*162.
    Total states = 2*3*3*3*3*2 = 324.
    """
    return t6[0] + t6[1]*2 + t6[2]*6 + t6[3]*18 + t6[4]*54 + t6[5]*162


def compute_cphi_data(n_val):
    """Compute all CΦ data for a given n. Returns dict with all results."""
    t0 = time.time()
    ms, fs = build_system(n_val)
    n = n_val

    print(f"  Building system n={n}, product={ms[0]}*3^{n-2}*{ms[-1]}={4*3**(n-2)}...")
    result = verify_system(ms, fs)
    assert result['valid'], f"System invalid at n={n}!"
    good_set = result['good_configs']
    print(f"    Valid! {len(good_set)} good configs, cycle length {result['cycle_length']}")

    all_configs_list = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs_list if c not in good_set]
    bad_set = set(bad_list)
    print(f"    {len(bad_list)} bad configs")

    # Cache fc values
    fc_cache = {}
    for c in bad_list:
        fc_cache[c] = fc(c, n)

    # Build TP-preserving edges (bad -> bad with all 3 monotone quantities preserved)
    tp_edges = []  # (src, dst, proc, dfc)
    tp_fwd = defaultdict(list)
    for c in bad_list:
        e2c = exp2_count(c, n)
        i21c = int_21(c, n)
        ewc = exp2_weight(c, n)
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
                if succ in bad_set:
                    if succ not in fc_cache:
                        fc_cache[succ] = fc(succ, n)
                    e2s = exp2_count(succ, n)
                    i21s = int_21(succ, n)
                    ews = exp2_weight(succ, n)
                    if e2s == e2c and i21s == i21c and ews == ewc:
                        dfc = fc_cache[succ] - fc_cache[c]
                        tp_edges.append((c, succ, i, dfc))
                        tp_fwd[c].append((succ, dfc))

    print(f"    {len(tp_edges)} TP-preserving bad edges")

    # Compute Φ_full via fixpoint: g[c] = max over TP-successors of (dfc + g[succ])
    tp_nodes = set()
    for c, s, _, _ in tp_edges:
        tp_nodes.add(c)
        tp_nodes.add(s)
    for c in bad_list:
        tp_nodes.add(c)

    g = {c: 0 for c in tp_nodes}
    for iteration in range(2 * n + 10):
        changed = False
        for c in tp_nodes:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]:
                    g[c] = new_g
                    changed = True
        if not changed:
            break

    phi = {c: fc_cache.get(c, fc(c, n)) + g[c] for c in tp_nodes}

    # Verify Φ_full non-increasing
    phi_viols = sum(1 for c, s, _, _ in tp_edges if phi.get(s, 0) > phi.get(c, 0))
    assert phi_viols == 0, f"Φ_full violations at n={n}!"
    print(f"    Φ_full non-increasing: VERIFIED (0 violations)")

    # Extract CΦ edges (TP-preserving AND Φ_full preserved)
    const_edges = [(c, s, pos, dfc) for c, s, pos, dfc in tp_edges
                   if phi.get(s, 0) == phi.get(c, 0)]
    print(f"    {len(const_edges)} constant-Φ_full edges")

    # Extract boundary-changing 6-tuple transitions
    t6_trans = set()
    t6_adj = defaultdict(set)
    for c, s, pos, dfc in const_edges:
        b6c = boundary6(c, n)
        b6s = boundary6(s, n)
        if b6c != b6s:
            t6_trans.add((b6c, b6s))
            t6_adj[b6c].add(b6s)

    # Encode as integer pairs
    t6_encoded = set()
    for src, dst in t6_trans:
        t6_encoded.add((encode6(src), encode6(dst)))

    # DAG check on 6-tuple automaton
    t6_nodes = set()
    for src, dst in t6_trans:
        t6_nodes.add(src)
        t6_nodes.add(dst)

    # Simple DFS cycle check
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in t6_nodes}
    is_dag = True
    for start in t6_nodes:
        if color[start] != WHITE:
            continue
        stack = [(start, iter(t6_adj.get(start, set())))]
        color[start] = GRAY
        while stack:
            node, children = stack[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    is_dag = False
                    break
                if color[child] == WHITE:
                    color[child] = GRAY
                    stack.append((child, iter(t6_adj.get(child, set()))))
            except StopIteration:
                color[node] = BLACK
                stack.pop()
            if not is_dag:
                break
        if not is_dag:
            break

    # Rank computation
    rank = 0
    if is_dag:
        out_deg = {c: len(t6_adj.get(c, set())) for c in t6_nodes}
        sinks = [c for c in t6_nodes if out_deg[c] == 0]
        rank_map = {c: 0 for c in sinks}
        radj = defaultdict(list)
        for c in t6_nodes:
            for s in t6_adj.get(c, set()):
                radj[s].append(c)
        q = deque(sinks)
        while q:
            s = q.popleft()
            for c in radj.get(s, []):
                new_r = rank_map[s] + 1
                if c not in rank_map or new_r > rank_map[c]:
                    rank_map[c] = new_r
                    q.append(c)
        rank = max(rank_map.values()) if rank_map else 0

    elapsed = time.time() - t0
    print(f"    6-tuple: DAG={'YES' if is_dag else 'NO'}, "
          f"{len(t6_trans)} transitions, {len(t6_nodes)} states, rank {rank}")
    print(f"    Elapsed: {elapsed:.1f}s")

    return {
        'n': n_val,
        'ms': ms,
        'fs': fs,
        'good_set': good_set,
        'bad_set': bad_set,
        'bad_list': bad_list,
        'tp_edges': tp_edges,
        'tp_fwd': tp_fwd,
        'fc_cache': fc_cache,
        'phi': phi,
        'const_edges': const_edges,
        't6_trans': t6_trans,
        't6_encoded': t6_encoded,
        't6_nodes': t6_nodes,
        'is_dag': is_dag,
        'rank': rank,
    }


def task1_verify_6tuple():
    """Task 1: Verify 617-edge set at n=9 and n=10."""
    print("=" * 70)
    print("TASK 1: Verify CΦ 617-edge 6-tuple set at n=10")
    print("=" * 70)

    data9 = compute_cphi_data(9)
    data10 = compute_cphi_data(10)

    trans9 = data9['t6_trans']
    trans10 = data10['t6_trans']
    enc9 = data9['t6_encoded']
    enc10 = data10['t6_encoded']

    print(f"\n  Comparison:")
    print(f"    n=9:  {len(trans9)} 6-tuple transitions")
    print(f"    n=10: {len(trans10)} 6-tuple transitions")

    only9 = trans9 - trans10
    only10 = trans10 - trans9
    common = trans9 & trans10

    print(f"    Common: {len(common)}")
    print(f"    Only in n=9:  {len(only9)}")
    print(f"    Only in n=10: {len(only10)}")

    if not only9 and not only10:
        print(f"\n  CONFIRMED: n-independent. The 6-tuple transition set is IDENTICAL")
        print(f"  at n=9 and n=10: exactly {len(common)} transitions.")
    else:
        if only9:
            print(f"\n  Transitions in n=9 but NOT n=10:")
            for src, dst in sorted(only9):
                print(f"    {src} -> {dst}")
        if only10:
            print(f"\n  NEW transitions at n=10 (not in n=9):")
            for src, dst in sorted(only10):
                print(f"    {src} -> {dst}")

    # Encoded comparison
    enc_only9 = enc9 - enc10
    enc_only10 = enc10 - enc9
    print(f"\n  Encoded check: only_in_9={len(enc_only9)}, only_in_10={len(enc_only10)}")

    return data9, data10


def task2_fc_spectrum(data9, data10):
    """Task 2: TP-reachable fc spectrum comparison for sample boundaries."""
    print("\n" + "=" * 70)
    print("TASK 2: TP-reachable fc spectrum comparison n=9 vs n=10")
    print("=" * 70)

    results = {}

    for label, data in [("n=9", data9), ("n=10", data10)]:
        n = data['n']
        bad_set = data['bad_set']
        tp_fwd = data['tp_fwd']
        fc_cache = data['fc_cache']
        phi = data['phi']

        # Group bad configs by boundary 6-tuple
        boundary_groups = defaultdict(list)
        for c in bad_set:
            b6 = boundary6(c, n)
            boundary_groups[b6].append(c)

        # For each boundary, compute max Φ_full and fc spectrum
        boundary_data = {}
        for b6, configs in boundary_groups.items():
            fc_vals = set()
            phi_vals = set()
            for c in configs:
                fc_vals.add(fc_cache.get(c, fc(c, n)))
                phi_vals.add(phi.get(c, fc_cache.get(c, fc(c, n))))

            # TP-reachable fc values: BFS from each config in this boundary group
            tp_reachable_fc = set()
            tp_reachable_phi = set()
            for c in configs:
                # BFS
                visited = set()
                queue = deque([c])
                visited.add(c)
                while queue:
                    node = queue.popleft()
                    tp_reachable_fc.add(fc_cache.get(node, fc(node, n)))
                    tp_reachable_phi.add(phi.get(node, 0))
                    for succ, dfc in tp_fwd.get(node, []):
                        if succ not in visited:
                            visited.add(succ)
                            queue.append(succ)

            max_phi = max(tp_reachable_phi) if tp_reachable_phi else 0
            max_fc = max(tp_reachable_fc) if tp_reachable_fc else 0
            boundary_data[b6] = {
                'count': len(configs),
                'fc_vals': sorted(fc_vals),
                'phi_vals': sorted(phi_vals),
                'tp_fc': sorted(tp_reachable_fc),
                'tp_phi': sorted(tp_reachable_phi),
                'max_phi': max_phi,
                'max_fc': max_fc,
            }

        results[label] = boundary_data
        print(f"\n  {label}: {len(boundary_groups)} distinct boundaries, "
              f"{len(bad_set)} bad configs")

    # Find shared boundaries
    b9 = set(results["n=9"].keys())
    b10 = set(results["n=10"].keys())
    shared = b9 & b10
    print(f"\n  Shared boundaries: {len(shared)} (out of {len(b9)} at n=9, {len(b10)} at n=10)")

    # Sample 20 boundaries (or all shared if fewer)
    sample = sorted(shared)[:20]
    print(f"\n  Comparing {len(sample)} boundary configs:")
    print(f"  {'Boundary 6-tuple':>30s} | {'n=9 max_phi':>10s} {'n=10 max_phi':>11s} | "
          f"{'n=9 fc_set':>20s} {'n=10 fc_set':>20s} | Match")
    print(f"  {'-'*30} | {'-'*10} {'-'*11} | {'-'*20} {'-'*20} | -----")

    all_match = True
    for b6 in sample:
        d9 = results["n=9"][b6]
        d10 = results["n=10"][b6]
        phi_match = d9['max_phi'] == d10['max_phi']
        fc_match = set(d9['tp_fc']) == set(d10['tp_fc'])
        both = phi_match and fc_match
        if not both:
            all_match = False
        print(f"  {str(b6):>30s} | {d9['max_phi']:>10d} {d10['max_phi']:>11d} | "
              f"{str(d9['tp_fc']):>20s} {str(d10['tp_fc']):>20s} | "
              f"{'YES' if both else 'NO'}")

    # Summary over ALL shared boundaries
    phi_mismatches = 0
    fc_mismatches = 0
    for b6 in shared:
        d9 = results["n=9"][b6]
        d10 = results["n=10"][b6]
        if d9['max_phi'] != d10['max_phi']:
            phi_mismatches += 1
        if set(d9['tp_fc']) != set(d10['tp_fc']):
            fc_mismatches += 1

    print(f"\n  Over ALL {len(shared)} shared boundaries:")
    print(f"    Phi_full mismatches: {phi_mismatches}")
    print(f"    FC set mismatches:   {fc_mismatches}")

    if phi_mismatches == 0 and fc_mismatches == 0:
        print(f"\n  CONFIRMED: Phi_full and fc spectra are IDENTICAL for all "
              f"{len(shared)} shared boundaries.")
        print(f"  Strong evidence for Phi_full locality (boundary-determined).")
    else:
        print(f"\n  DIFFERENCES FOUND. Phi_full is NOT purely boundary-determined.")
        # Show first few mismatches
        count = 0
        for b6 in sorted(shared):
            d9 = results["n=9"][b6]
            d10 = results["n=10"][b6]
            if d9['max_phi'] != d10['max_phi'] or set(d9['tp_fc']) != set(d10['tp_fc']):
                print(f"    {b6}: n=9 phi={d9['max_phi']} fc={d9['tp_fc']} | "
                      f"n=10 phi={d10['max_phi']} fc={d10['tp_fc']}")
                count += 1
                if count >= 10:
                    print(f"    ... ({phi_mismatches + fc_mismatches - count} more)")
                    break

    # Deeper analysis: check if the DIFFERENCE is constant
    print(f"\n  --- Phi_full difference analysis ---")
    diffs = {}
    for b6 in shared:
        d9 = results["n=9"][b6]
        d10 = results["n=10"][b6]
        diff = d10['max_phi'] - d9['max_phi']
        diffs[b6] = diff

    diff_vals = set(diffs.values())
    from collections import Counter
    diff_counter = Counter(diffs.values())
    print(f"  Phi_full(n=10) - Phi_full(n=9) distribution:")
    for d, cnt in sorted(diff_counter.items()):
        print(f"    delta = {d}: {cnt} boundaries ({100*cnt/len(shared):.1f}%)")

    if len(diff_vals) == 1:
        d = list(diff_vals)[0]
        print(f"\n  UNIFORM SHIFT: Phi_full grows by exactly {d} from n=9 to n=10")
        print(f"  for ALL {len(shared)} boundaries.")
        print(f"  This is consistent with Phi_full = boundary_rank + (n-dependent offset).")
        print(f"  The 6-tuple DAG structure (which boundaries can reach which) is UNCHANGED.")
        print(f"  Only the absolute fc scale shifts, which is expected since max fc grows with n.")
    else:
        print(f"\n  NON-UNIFORM shift across boundaries. Values: {sorted(diff_vals)}")

    # Check fc set shift pattern
    print(f"\n  --- FC set shift analysis ---")
    fc_diff_patterns = Counter()
    for b6 in shared:
        d9 = results["n=9"][b6]
        d10 = results["n=10"][b6]
        # Check if n=10 fc set = n=9 fc set union {max+1}
        s9 = set(d9['tp_fc'])
        s10 = set(d10['tp_fc'])
        new_in_10 = s10 - s9
        gone_from_9 = s9 - s10
        pattern = f"+{sorted(new_in_10)}" if new_in_10 else "same"
        if gone_from_9:
            pattern += f" -{sorted(gone_from_9)}"
        fc_diff_patterns[pattern] += 1

    print(f"  FC set change patterns (n=10 vs n=9):")
    for pat, cnt in fc_diff_patterns.most_common(10):
        print(f"    {pat}: {cnt} boundaries")


def main():
    sys.stdout.reconfigure(line_buffering=True)
    print("CΦ 6-tuple verification and fc spectrum comparison")
    print("=" * 70)
    print()

    data9, data10 = task1_verify_6tuple()
    task2_fc_spectrum(data9, data10)

    print("\n" + "=" * 70)
    print("DONE")
    print("=" * 70)


if __name__ == '__main__':
    main()
