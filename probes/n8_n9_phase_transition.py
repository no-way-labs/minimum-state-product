#!/usr/bin/env python3
"""n8_n9_phase_transition.py — What breaks at n=9 for the 3-binary+quaternary construction?

At n=8: ms=(2,2,2,3,4,3,3,3), product=2592=32*3^4. Valid system EXISTS.
At n=9: ms=(2,2,2,3,4,3,3,3,3), product=7776=32*3^5. NO valid system exists.

Both have 3 binary procs, both sub-threshold (< 4*3^(n-2)).
What structural quantity crosses a threshold between n=8 and n=9?
"""

import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from math import prod

# ============================================================
# SECTION 1: Build and verify n=8 witness
# ============================================================

def build_bounce_system(n, ms):
    """Build bounce-cycle system with good-targeting completion."""
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    movers = None
    for step, mover in enumerate(full):
        if step >= len(full):
            break
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            return None
        visited.add(nc)
        cycle.append(nc)

    if movers is None:
        return None

    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Extract determined entries from cycle
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    # Find free entries
    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Pre-index configs by (p, L, S, R) for speed
    triple_index = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
            triple_index[(p, L, S, R)].append(c)

    # Good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = float('inf')
        for out in range(ms[p]):
            if out == S:
                ng_edges = 0
                good_count = 0
            else:
                # Count how many non-good configs with this context would go to good/non-good
                good_count = 0
                ng_edges = 0
                for c in triple_index.get(key, []):
                    new_c = tuple(c[j] if j != p else out for j in range(n))
                    if new_c in good_set:
                        good_count += 1
                    elif new_c in non_good_set:
                        ng_edges += 1
            if good_count > best_good or (good_count == best_good and ng_edges < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng_edges
        comp[key] = best_out

    # Liveness fix
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
            for p in range(n)
        )
        if not has_priv:
            for p in range(n):
                L2 = c[(p-1)%n]; S2 = c[p]; R2 = c[(p+1)%n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            comp[key] = out
                            break
                    break

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    return {
        'ms': ms, 'fs': fs, 'comp': comp,
        'cycle': cycle, 'movers': movers,
        'good_set': good_set, 'det': det, 'free_entries': free_entries
    }


def verify_convergence_only(ms, comp, good_set):
    """Check convergence: no cycle in bad configs under nondeterministic transitions."""
    n = len(ms)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad = set()
    for c in all_configs:
        if c not in good_set:
            bad.add(c)

    # Build bad->bad transition graph
    bad_succs = defaultdict(set)
    for c in bad:
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            out = comp.get((p, L, S, R), S)
            if out != S:  # privileged
                new_c = tuple(c[j] if j != p else out for j in range(n))
                if new_c in bad:
                    bad_succs[c].add(new_c)

    # DFS cycle detection
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in bad}
    has_cycle = False

    def dfs(u):
        nonlocal has_cycle
        color[u] = GRAY
        for v in bad_succs.get(u, set()):
            if color[v] == GRAY:
                has_cycle = True
                return
            if color[v] == WHITE:
                dfs(u=v)
                if has_cycle:
                    return
        color[u] = BLACK

    sys.setrecursionlimit(500000)
    for c in bad:
        if color[c] == WHITE:
            dfs(c)
            if has_cycle:
                return False
    return True


# ============================================================
# SECTION 2: Context utilization analysis
# ============================================================

def context_utilization_analysis(n, ms):
    """Compute context utilization metrics."""
    product_val = prod(ms)

    # Cycle length for bounce cycle
    # Up: 0,1,...,n-1; Down: n-2,...,1. Total movers per period: 2(n-1)
    # Binary procs fire every m_p=2 times to return. Ternary every 3. Quat every 4.
    # Cycle length = LCM structure... let's compute directly
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    CL = None
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            CL = step + 1
            break
        if nc in visited:
            CL = None
            break
        visited.add(nc)
        cycle.append(nc)

    if CL is None:
        return None

    # Context sizes at each processor
    context_sizes = []
    for p in range(n):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        ctx_size = m_L * m_S * m_R
        context_sizes.append(ctx_size)

    total_contexts = sum(context_sizes)

    # How many distinct contexts appear in the cycle at each processor?
    cycle_contexts_per_proc = [set() for _ in range(n)]
    for c in cycle:
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            cycle_contexts_per_proc[p].add((L, S, R))

    # Per-processor utilization
    proc_utilization = []
    for p in range(n):
        used = len(cycle_contexts_per_proc[p])
        total = context_sizes[p]
        proc_utilization.append((used, total, used/total))

    # Global: cycle_length * n total context-appearances, vs total_contexts
    global_util = (CL * n) / total_contexts if total_contexts > 0 else 0
    # Alternative: CL / min_context_size (bottleneck processor)
    min_ctx = min(context_sizes)
    bottleneck_util = CL / min_ctx

    return {
        'n': n, 'ms': ms, 'product': product_val,
        'cycle_length': CL, 'total_contexts': total_contexts,
        'context_sizes': context_sizes,
        'proc_utilization': proc_utilization,
        'global_utilization': global_util,
        'bottleneck_utilization': bottleneck_util,
        'min_context_size': min_ctx,
    }


# ============================================================
# SECTION 3: Entry conflict analysis
# ============================================================

def entry_conflict_analysis(n, ms):
    """For every good cycle, check if entry conflicts exist.

    Entry conflict: same (p, L, S, R) context appears as both
    mover and non-mover in the cycle.
    """
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    movers_list = None
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers_list = full[:step + 1]
            break
        if nc in visited:
            return None
        visited.add(nc)
        cycle.append(nc)

    if movers_list is None:
        return None

    CL = len(cycle)

    # Collect mover and non-mover contexts per processor
    mover_contexts = defaultdict(set)    # p -> set of (L, S, R)
    nonmover_contexts = defaultdict(set)  # p -> set of (L, S, R)

    for idx in range(CL):
        c = cycle[idx]
        mv = movers_list[idx]
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            ctx = (L, S, R)
            if p == mv:
                mover_contexts[p].add(ctx)
            else:
                nonmover_contexts[p].add(ctx)

    # Entry conflict = mover_contexts ∩ nonmover_contexts
    conflicts = {}
    total_conflicts = 0
    for p in range(n):
        overlap = mover_contexts[p] & nonmover_contexts[p]
        conflicts[p] = overlap
        total_conflicts += len(overlap)

    return {
        'cycle_length': CL,
        'mover_contexts': {p: len(mover_contexts[p]) for p in range(n)},
        'nonmover_contexts': {p: len(nonmover_contexts[p]) for p in range(n)},
        'conflicts': conflicts,
        'total_conflicts': total_conflicts,
        'conflict_procs': [p for p in range(n) if len(conflicts[p]) > 0],
    }


# ============================================================
# SECTION 4: Exhaustive search over ALL good cycles (for smaller n)
# ============================================================

def exhaustive_good_cycles(n, ms, max_cycles=10000):
    """Find all good cycles via DFS on incrementing transitions.

    For each starting config, follow the incrementing mover-word cycle.
    This is a simplified version; real search needs all transition modes.
    """
    product_val = prod(ms)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    # Enumerate mover words (circular sequences of processor indices)
    # that form valid good cycles with incrementing transitions.
    # A good cycle: start at config c, apply mover sequence, return to c.
    # Each config in cycle has exactly 1 privileged proc (the mover).

    # For a cycle of length CL, each proc p fires exactly m_p times
    # (since it must return to its starting value with increment transitions).
    # So CL = sum(m_p for p in range(n)).

    CL = sum(ms)

    # For checking: how many contexts does each proc have?
    context_sizes = []
    for p in range(n):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        context_sizes.append(m_L * m_S * m_R)

    return {
        'cycle_length': CL,
        'context_sizes': context_sizes,
        'min_context_size': min(context_sizes),
        'CL_vs_min_ctx': CL / min(context_sizes),
    }


# ============================================================
# SECTION 5: Pigeonhole / context saturation analysis
# ============================================================

def pigeonhole_analysis(n, ms):
    """The key insight: cycle length vs context capacity.

    In a good cycle of length CL, each step i has a mover p_i.
    Processor p_i sees context (L, S, R) and must fire (change state).
    Non-mover procs see contexts where they must NOT fire.

    At each step, 1 mover context and (n-1) non-mover contexts are used.
    Total contexts used per proc = number of times it appears as mover + non-mover.
    Mover appearances at proc p = m_p (each fires exactly m_p times).
    Non-mover appearances at proc p = CL - m_p.

    For proc p: it has context_size(p) = m_L * m_S * m_R total contexts.
    It uses m_p as mover + (CL - m_p) as non-mover = CL contexts total.
    But some mover and non-mover contexts might coincide -- that's the entry conflict!

    If all CL contexts at proc p were distinct, we need CL <= context_size(p).
    If CL > context_size(p), then by pigeonhole, at least two cycle steps
    share a context at proc p. If one is mover and one is non-mover: entry conflict!
    """
    CL_increment = sum(ms)  # cycle length with incrementing transitions

    product_val = prod(ms)

    results = []
    for p in range(n):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        ctx_size = m_L * m_S * m_R

        mover_fires = ms[p]
        nonmover_fires = CL_increment - ms[p]

        # Pigeonhole: if mover_fires + nonmover_fires > ctx_size,
        # some context must be shared. But shared doesn't necessarily
        # mean mover-nonmover conflict (could be two mover steps or two nonmover steps).

        # Stronger: if CL > ctx_size, pigeonhole gives a collision.
        # If mover_fires > ctx_size, then two mover steps share a context (impossible
        # since mover context determines output, and we need different outputs).
        # So actually mover contexts must all be distinct => mover_fires <= ctx_size.
        # Non-mover contexts can repeat (same output: keep state).
        # Entry conflict happens when a mover context equals a non-mover context.

        # Key ratio: what fraction of contexts are used by movers?
        mover_density = mover_fires / ctx_size
        total_density = CL_increment / ctx_size

        results.append({
            'proc': p, 'm_p': ms[p],
            'm_L': m_L, 'm_R': m_R,
            'ctx_size': ctx_size,
            'mover_fires': mover_fires,
            'nonmover_fires': nonmover_fires,
            'total_context_uses': CL_increment,
            'mover_density': mover_density,
            'total_density': total_density,
            'pigeonhole_forced': CL_increment > ctx_size,
        })

    return results


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    from verifier import verify_system

    print("=" * 80)
    print("PHASE TRANSITION ANALYSIS: n=8 vs n=9 for 3-binary + quaternary")
    print("=" * 80)

    # --- Context utilization for a range of n ---
    print("\n" + "=" * 80)
    print("SECTION A: Context Utilization (bounce cycle, 3 binary + 1 quaternary)")
    print("=" * 80)

    for n in range(5, 12):
        ms = tuple([2, 2, 2, 3, 4] + [3] * (n - 5))
        result = context_utilization_analysis(n, ms)
        if result:
            print(f"\nn={n}: ms={ms}, product={result['product']}, threshold=4*3^{n-2}={4*3**(n-2)}")
            print(f"  Cycle length: {result['cycle_length']}")
            print(f"  Context sizes per proc: {result['context_sizes']}")
            print(f"  Min context size: {result['min_context_size']}")
            print(f"  CL/min_ctx = {result['cycle_length']}/{result['min_context_size']} = {result['bottleneck_utilization']:.3f}")
            print(f"  Global utilization (CL*n / total_ctx): {result['global_utilization']:.3f}")
            print(f"  Sub-threshold: {result['product'] < 4*3**(n-2)}")
            print(f"  Per-proc utilization (used/total):")
            for p, (used, total, ratio) in enumerate(result['proc_utilization']):
                marker = " ***" if ratio > 1.0 else ""
                print(f"    P{p} (m={ms[p]}): {used}/{total} = {ratio:.3f}{marker}")

    # --- Pigeonhole analysis ---
    print("\n" + "=" * 80)
    print("SECTION B: Pigeonhole / Context Saturation Analysis")
    print("=" * 80)

    for n in range(5, 12):
        ms = tuple([2, 2, 2, 3, 4] + [3] * (n - 5))
        CL = sum(ms)
        product_val = prod(ms)

        print(f"\nn={n}: ms={ms}, product={product_val}, CL={CL}")
        print(f"  {'Proc':<6} {'m_p':<5} {'m_L':<5} {'m_R':<5} {'ctx':<6} {'mover':<7} {'nonmov':<8} {'CL/ctx':<8} {'pigeonhole'}")
        print(f"  {'-'*65}")

        ph_results = pigeonhole_analysis(n, ms)
        any_forced = False
        for r in ph_results:
            forced = "FORCED" if r['pigeonhole_forced'] else ""
            if r['pigeonhole_forced']:
                any_forced = True
            print(f"  P{r['proc']:<5} {r['m_p']:<5} {r['m_L']:<5} {r['m_R']:<5} {r['ctx_size']:<6} "
                  f"{r['mover_fires']:<7} {r['nonmover_fires']:<8} {r['total_density']:<8.3f} {forced}")

        if any_forced:
            print(f"  ==> PIGEONHOLE FORCES CONTEXT COLLISION at n={n}")
        else:
            print(f"  ==> No pigeonhole at n={n} — room for collision-free cycle")

    # --- Entry conflict analysis ---
    print("\n" + "=" * 80)
    print("SECTION C: Entry Conflict Analysis (bounce cycle)")
    print("=" * 80)

    for n in range(5, 12):
        ms = tuple([2, 2, 2, 3, 4] + [3] * (n - 5))
        ec = entry_conflict_analysis(n, ms)
        if ec:
            print(f"\nn={n}: ms={ms}, CL={ec['cycle_length']}")
            print(f"  Total entry conflicts: {ec['total_conflicts']}")
            print(f"  Conflicting procs: {ec['conflict_procs']}")
            for p in range(n):
                mc = ec['mover_contexts'][p]
                nc = ec['nonmover_contexts'][p]
                conflicts = ec['conflicts'][p]
                status = f" EC={len(conflicts)}" if len(conflicts) > 0 else ""
                print(f"    P{p}: mover_ctx={mc}, nonmover_ctx={nc}{status}")

    # --- Attempt to build valid system at n=8 ---
    print("\n" + "=" * 80)
    print("SECTION D: Build and Verify n=8 Witness")
    print("=" * 80)

    n = 8
    ms = tuple([2, 2, 2, 3, 4, 3, 3, 3])
    print(f"\nBuilding system for n={n}, ms={ms}, product={prod(ms)}")
    t0 = time.time()
    sys_result = build_bounce_system(n, ms)
    t1 = time.time()

    if sys_result:
        print(f"  Bounce cycle built in {t1-t0:.2f}s, CL={len(sys_result['cycle'])}")
        print(f"  Determined entries: {len(sys_result['det'])}")
        print(f"  Free entries: {len(sys_result['free_entries'])}")

        # Verify
        result = verify_system(list(ms), sys_result['fs'], verbose=False)
        print(f"  Valid: {result['valid']}")
        if result['valid']:
            for prop, (ok, msg) in result['properties'].items():
                print(f"    {prop}: {ok} — {msg}")
        else:
            print(f"  Properties: {result['properties']}")

            # Check convergence separately
            print("  Checking convergence...")
            conv = verify_convergence_only(list(ms), sys_result['comp'], sys_result['good_set'])
            print(f"  Convergence (no bad cycles): {conv}")
    else:
        print("  Bounce cycle failed to close!")

    # --- Attempt to build valid system at n=9 ---
    print("\n" + "=" * 80)
    print("SECTION E: Build and Verify n=9 (expected to FAIL)")
    print("=" * 80)

    n = 9
    ms = tuple([2, 2, 2, 3, 4, 3, 3, 3, 3])
    print(f"\nBuilding system for n={n}, ms={ms}, product={prod(ms)}")
    t0 = time.time()
    sys_result = build_bounce_system(n, ms)
    t1 = time.time()

    if sys_result:
        print(f"  Bounce cycle built in {t1-t0:.2f}s, CL={len(sys_result['cycle'])}")
        print(f"  Determined entries: {len(sys_result['det'])}")
        print(f"  Free entries: {len(sys_result['free_entries'])}")

        # Check entry conflicts
        ec = entry_conflict_analysis(n, ms)
        if ec:
            print(f"  Entry conflicts in this cycle: {ec['total_conflicts']}")

        # Try verification anyway
        result = verify_system(list(ms), sys_result['fs'], verbose=False)
        print(f"  Valid: {result['valid']}")
        if not result['valid']:
            for prop, (ok, msg) in result['properties'].items():
                print(f"    {prop}: {ok} — {msg}")
    else:
        print("  Bounce cycle failed to close!")

    # --- The critical comparison ---
    print("\n" + "=" * 80)
    print("SECTION F: Critical Comparison — WHY n=9 breaks")
    print("=" * 80)

    for n in [8, 9, 10]:
        ms = tuple([2, 2, 2, 3, 4] + [3] * (n - 5))
        CL = sum(ms)
        product_val = prod(ms)
        threshold = 4 * 3**(n-2)

        # Count binary, ternary, quaternary
        binary_count = sum(1 for m in ms if m == 2)
        ternary_count = sum(1 for m in ms if m == 3)
        quat_count = sum(1 for m in ms if m == 4)

        # Number of "boundary ternary" procs (ternary procs adjacent to binary)
        boundary_ternary = 0
        for p in range(n):
            if ms[p] == 3:
                L_is_binary = ms[(p-1)%n] == 2
                R_is_binary = ms[(p+1)%n] == 2
                if L_is_binary or R_is_binary:
                    boundary_ternary += 1

        # Interior ternary (ternary with both neighbors ternary or quaternary)
        interior_ternary = ternary_count - boundary_ternary

        # Context sizes
        min_ctx = min(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))

        # The critical ratio
        ratio = CL / min_ctx

        print(f"\nn={n}: ms={ms}")
        print(f"  product={product_val}, threshold={threshold}, sub-threshold={product_val < threshold}")
        print(f"  CL={CL}, min_ctx={min_ctx}, CL/min_ctx={ratio:.4f}")
        print(f"  binary={binary_count}, ternary={ternary_count}, quaternary={quat_count}")
        print(f"  boundary_ternary={boundary_ternary}, interior_ternary={interior_ternary}")
        print(f"  Ring structure: {' '.join(str(m) for m in ms)}")

        # The per-proc analysis for the tightest processors
        print(f"  Per-proc CL/ctx:")
        for p in range(n):
            m_L = ms[(p-1)%n]; m_S = ms[p]; m_R = ms[(p+1)%n]
            ctx = m_L * m_S * m_R
            density = CL / ctx
            marker = ""
            if density > 1.0:
                marker = " *** EXCEEDS 1.0"
            elif density > 0.9:
                marker = " (tight)"
            print(f"    P{p}: m=({m_L},{m_S},{m_R}), ctx={ctx}, CL/ctx={density:.4f}{marker}")
