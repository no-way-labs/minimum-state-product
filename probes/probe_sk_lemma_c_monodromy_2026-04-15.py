#!/usr/bin/env python3
"""Exploration 3: Monodromy domain analysis for SK Lemma C.

The monodromy μ is the composition of all L forced transitions following
the cycle's mover sequence. It's a partial function on VC.

Key insight: if no single-step forced edge goes from VC-NG to C (confirmed
empirically), then no multi-step path crosses either. So the monodromy
domain restricted to VC-NG is forward-invariant: μ(D ∩ VC-NG) ⊆ D ∩ VC-NG.

Since μ|_{D ∩ VC-NG} is an injective self-map of a finite set, it's a
bijection, so every orbit is a cycle, so D ∩ VC-NG ⊆ SK.

Questions:
1. What is |D ∩ VC-NG| where D is the monodromy domain?
2. Is |D ∩ VC-NG| ≥ 2^(n-1)?
3. What fraction of VC-NG configs survive all L transition steps?
4. At which steps do configs fail to be covered?
5. How does the monodromy domain compare to the peeling immune core?
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


def compute_monodromy_domain(ms, n, cycle, movers, det):
    """Compute the monodromy domain and its restriction to VC-NG.

    The monodromy follows the cycle's mover sequence. At each step,
    fire position movers[t] using the det. Config must have a matching
    det entry at each step (the non-mover entries impose "stay" constraints
    that are automatically satisfied since we only change one coordinate).
    """
    L = len(movers)
    cycle_set = set(cycle)
    V = value_sets(cycle, n)

    # Move entries
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # All det entries (including stay entries)
    all_det = dict(det)

    # VC configs
    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    # Compute monodromy for each VC-NG config
    # The monodromy applies each step of the cycle's mover sequence
    mono_domain_vcng = set()
    mono_image = {}  # c -> μ(c)
    mono_period = {}  # c -> period of c under μ

    # Also track: at which step does the first failure occur?
    failure_step_dist = Counter()

    for c0 in vc_ng:
        c = list(c0)
        alive = True
        for t in range(L):
            p = movers[t]
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key not in all_det:
                # This position at this config has no det entry — monodromy undefined
                failure_step_dist[t] += 1
                alive = False
                break
            # Apply the transition: change c[p] to det value
            new_val = all_det[key]
            if new_val != c[p]:
                c[p] = new_val
            # Note: non-movers stay (c[q] unchanged for q ≠ p), which
            # is consistent with det stay entries
        if alive:
            result = tuple(c)
            mono_domain_vcng.add(c0)
            mono_image[c0] = result

    # Verify forward-invariance: μ(D ∩ VC-NG) ⊆ D ∩ VC-NG
    forward_invariant = True
    escape_to_cycle = 0
    escape_to_outside = 0
    for c0 in mono_domain_vcng:
        img = mono_image[c0]
        if img in cycle_set:
            escape_to_cycle += 1
            forward_invariant = False
        elif img not in vc_ng:
            escape_to_outside += 1
            forward_invariant = False
        elif img not in mono_domain_vcng:
            # Image is in VC-NG but NOT in monodromy domain
            # This is fine — μ is still defined at c0, and the image is in VC-NG
            # Forward-invariance of the DOMAIN requires μ(c0) ∈ D ∩ VC-NG
            forward_invariant = False

    # Compute orbits of μ on D ∩ VC-NG
    orbit_configs = set()
    if forward_invariant:
        # μ maps D ∩ VC-NG to D ∩ VC-NG bijectively
        # Every orbit is a cycle
        visited = set()
        for c0 in mono_domain_vcng:
            if c0 in visited:
                continue
            # Follow orbit
            orbit = []
            c = c0
            while c not in visited:
                visited.add(c)
                orbit.append(c)
                c = mono_image[c]
            orbit_configs.update(orbit)

    # Also compute the peeling immune core for comparison
    out_edges = defaultdict(list)
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in vc_ng:
                    out_edges[c].append(nc)
    remaining = set(vc_ng)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in out_edges.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    immune_core = remaining

    return {
        'L': L,
        'vc_ng': len(vc_ng),
        'mono_domain': len(mono_domain_vcng),
        'mono_frac': len(mono_domain_vcng) / max(len(vc_ng), 1),
        'forward_invariant': forward_invariant,
        'escape_cycle': escape_to_cycle,
        'escape_outside': escape_to_outside,
        'orbit_configs': len(orbit_configs) if forward_invariant else -1,
        'immune_core': len(immune_core),
        'domain_vs_immune': len(mono_domain_vcng) - len(immune_core),
        'failure_step_dist': dict(failure_step_dist),
        'domain_subset_immune': mono_domain_vcng.issubset(immune_core),
    }


def main():
    print("=" * 72)
    print("Exploration 3: Monodromy domain analysis")
    print("=" * 72)

    plan = [
        (5, 1, 1500, 5.0, 16),
        (6, 3, 500, 3.0, 18),
        (7, 15, 150, 3.0, 18),
    ]

    by_nL = defaultdict(list)
    all_records = []
    fi_violations = 0

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===")
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                r = compute_monodromy_domain(ms, n, cycle, movers, det)
                r['n'] = n
                r['ms'] = ms
                if not r['forward_invariant']:
                    fi_violations += 1
                by_nL[(n, L)].append(r)
                all_records.append(r)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx + 1}/{len(sampled)}]  {elapsed:.0f}s")

    # === Summary ===
    print(f"\n{'=' * 72}")
    print("=== Monodromy domain vs immune core ===")
    print(f"  n  L   count  |VC_NG|  |domain|  frac    |immune|  "
          f"dom⊆imm  FI  min_dom  2^(n-1)  slack")
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        min_dom = min(r['mono_domain'] for r in rs)
        min_imm = min(r['immune_core'] for r in rs)
        all_fi = all(r['forward_invariant'] for r in rs)
        all_subset = all(r['domain_subset_immune'] for r in rs)
        target = 2 ** (n - 1)
        dom_slack = min_dom - target
        flag = " !" if min_dom < target else ""
        print(f"  {n}  {L:2d}  {N:5d}  {avg('vc_ng'):6.0f}  "
              f"{avg('mono_domain'):7.0f}  {avg('mono_frac'):5.2f}  "
              f"{avg('immune_core'):7.0f}  "
              f"{'Y' if all_subset else 'N':>7s}  "
              f"{'Y' if all_fi else 'N':>2s}  "
              f"{min_dom:7d}  {target:6d}  {dom_slack:+5d}{flag}")

    # === Forward invariance check ===
    total_fi = sum(1 for r in all_records if r['forward_invariant'])
    print(f"\n=== Forward invariance ===")
    print(f"  Forward-invariant: {total_fi} / {len(all_records)}")
    print(f"  Violations: {fi_violations}")
    # Show escape details for non-FI cases
    esc_cycle = sum(r['escape_cycle'] for r in all_records)
    esc_outside = sum(r['escape_outside'] for r in all_records)
    print(f"  Total escapes to cycle: {esc_cycle}")
    print(f"  Total escapes to outside: {esc_outside}")
    # FI failures that are NOT escape: domain failure
    non_esc_fi_fail = sum(1 for r in all_records
                         if not r['forward_invariant']
                         and r['escape_cycle'] == 0
                         and r['escape_outside'] == 0)
    print(f"  Domain-only FI failures (image in VC-NG but not in domain): "
          f"{non_esc_fi_fail}")

    # === Domain subset of immune? ===
    subset_fails = sum(1 for r in all_records if not r['domain_subset_immune'])
    print(f"\n=== Domain ⊆ immune core? ===")
    print(f"  Always: {'YES' if subset_fails == 0 else f'NO ({subset_fails} failures)'}")

    # === Monodromy domain vs 2^(n-1) ===
    dom_violations = sum(1 for r in all_records
                        if r['mono_domain'] < 2 ** (r['n'] - 1))
    print(f"\n  MONODROMY DOMAIN >= 2^(n-1): "
          f"{'HOLDS' if dom_violations == 0 else f'VIOLATED ({dom_violations})'} "
          f"({len(all_records)} records)")

    # === Hardest cases ===
    print(f"\n=== Hardest cases (lowest monodromy domain) ===")
    sorted_records = sorted(all_records,
                           key=lambda r: r['mono_domain'] - 2 ** (r['n'] - 1))
    for r in sorted_records[:5]:
        n = r['n']
        slack = r['mono_domain'] - 2 ** (n - 1)
        print(f"  n={n} L={r['L']} ms={r['ms']} domain={r['mono_domain']} "
              f"immune={r['immune_core']} slack={slack} "
              f"FI={'Y' if r['forward_invariant'] else 'N'} "
              f"frac={r['mono_frac']:.3f}")


if __name__ == "__main__":
    main()
