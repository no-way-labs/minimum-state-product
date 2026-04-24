#!/usr/bin/env python3
"""CUP: Prove no bad cycle exists via shift-only + top reset analysis.

Key insight from orchestrator: In any bad cycle,
1. All move types present (Thm 5b)
2. Middle Δfc ∈ {-2,-1,0}, Top Δfc ∈ {0,+2}, Bottom Δfc ∈ {-2,-1,0,+1}
3. Net Δfc = 0 around cycle
4. If ANY middle has Δfc<0, top/bottom must compensate with Δfc>0
5. Key question: can the positive/negative fc changes balance in a cycle?

Approach: Show that in ANY execution segment between consecutive top firings,
the middle moves MUST include at least one Δfc<0 move (type change or annihilation).
This means fc strictly decreases between top firings. Since top Δfc ∈ {0,+2},
and fc must return to start in a cycle, we get a contradiction.

Actually, top can increase fc by 2. So we need: between consecutive top firings,
middle+bottom decrease fc by MORE than top increased it.

Let's verify the sharper claim: after top fires, within O(n) steps,
fc must decrease (regardless of daemon).
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict, deque


def sol3_v1_rules(ms, n):
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f
    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f
    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f
    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def get_privileged(c, fs, n):
    priv = []
    for i in range(n):
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(c, i, fs, n):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    lst = list(c); lst[i] = fs[i](L, S, R); return tuple(lst)


def frontier_count(c, n):
    return sum(1 for i in range(n) if (c[(i+1) % n] - c[i]) % 3 != 0)


def get_d_vector(c, n):
    return tuple((c[(i+1)%n] - c[i]) % 3 for i in range(n))


# ================================================================
# KEY CLAIM 1: In a bad cycle, every middle move must be Δfc=0.
# Proof: In a cycle, Σ Δfc = 0.
# Top Δfc ∈ {0, +2}. When top fires with d_{n-2}=0,d_{n-1}=0: Δfc=+2.
# When d_{n-2}≠0,d_{n-1}≠0: Δfc=0 (only case: d_{n-2}=2,d_{n-1}=1).
# Bottom Δfc ∈ {-2,-1,0,+1}.
# Middle Δfc ∈ {-2,-1,0}.
#
# For net 0: (sum of top +2's) + (sum of bottom +1's) =
#            (sum of middle -1's and -2's) + (sum of bottom -1's and -2's)
#
# This doesn't force all middle Δfc=0. BUT:
# Can we show that the number of "compensating" top+2 moves is bounded,
# forcing a contradiction?
# ================================================================

def verify_top_privilege_d_values(max_n=10):
    """When top is privileged, what are d_{n-2} and d_{n-1}?
    Prove: d_{n-2} ∈ {0, 2} (never 1), d_{n-1} determined by d_{n-2}."""
    print("=" * 60)
    print("TOP PRIVILEGE: d_{n-2} and d_{n-1} values")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        configs = list(cartesian(*(range(m) for m in ms)))
        cases = defaultdict(int)
        for c in configs:
            priv = get_privileged(c, fs, n)
            if n-1 in priv:
                d = get_d_vector(c, n)
                cases[(d[n-2], d[n-1])] += 1
        print(f"  n={n}: top privileged with (d_{{n-2}}, d_{{n-1}}): {dict(cases)}")


def verify_bottom_privilege_cases(max_n=8):
    """When bottom is privileged, characterize (d_0, d_{n-1}, c_0) and Δfc."""
    print("\n" + "=" * 60)
    print("BOTTOM PRIVILEGE: cases and Δfc")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        configs = list(cartesian(*(range(m) for m in ms)))
        cases = defaultdict(int)
        for c in configs:
            priv = get_privileged(c, fs, n)
            if 0 in priv:
                d = get_d_vector(c, n)
                succ = apply_move(c, 0, fs, n)
                dfc = frontier_count(succ, n) - frontier_count(c, n)
                cases[(c[0], d[0], d[n-1], dfc)] += 1
        print(f"  n={n}:")
        for (c0, d0, dn1, dfc), cnt in sorted(cases.items()):
            print(f"    c0={c0} d0={d0} d{{n-1}}={dn1} → Δfc={dfc:+d}: {cnt}")


# ================================================================
# KEY CLAIM 2: After top fires (d_{n-2}=1, d_{n-1}=2),
# the adversarial daemon CANNOT avoid fc decrease for more than
# 2(n-1) steps.
#
# Verify: for each config c where top just fired (d_{n-2}=1, d_{n-1}=2),
# what is the max number of steps (under adversarial daemon) before
# fc drops below fc(c)?
# ================================================================

def max_steps_after_top(n):
    """For each bad config with d_{n-2}=1, d_{n-1}=2 (just after top fired),
    compute worst-case steps before fc decreases."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Find bad configs with d_{n-2}=1, d_{n-1}=2
    post_top = []
    for c in bad_set:
        d = get_d_vector(c, n)
        if d[n-2] == 1 and d[n-1] == 2:
            post_top.append(c)

    if not post_top:
        print(f"  n={n}: no post-top bad configs")
        return

    # For each post-top config, BFS to find max steps before fc drops
    max_delay = 0
    max_config = None

    for c in post_top:
        fc_c = frontier_count(c, n)
        # BFS: how many steps can daemon keep fc >= fc_c?
        # Use iterative deepening or BFS on (config, depth)
        # Track max depth reachable while staying at fc >= fc_c and in bad_set
        visited = {c: 0}
        queue = deque([(c, 0)])
        local_max = 0

        while queue:
            cur, depth = queue.popleft()
            priv = get_privileged(cur, fs, n)
            for p in priv:
                succ = apply_move(cur, p, fs, n)
                if succ in good_set:
                    continue
                fc_s = frontier_count(succ, n)
                if fc_s < fc_c:
                    continue  # fc decreased, don't follow
                new_depth = depth + 1
                if succ not in visited or visited[succ] < new_depth:
                    visited[succ] = new_depth
                    if new_depth > local_max:
                        local_max = new_depth
                    if new_depth < 4 * n:  # bound search
                        queue.append((succ, new_depth))

        if local_max > max_delay:
            max_delay = local_max
            max_config = c

    print(f"  n={n}: max steps to fc decrease after top = {max_delay} "
          f"(out of {len(post_top)} post-top configs)")
    if max_config:
        d = get_d_vector(max_config, n)
        print(f"    worst config: {max_config} d={d} fc={frontier_count(max_config, n)}")


# ================================================================
# KEY CLAIM 3: In a hypothetical cycle where ALL middle moves are
# shifts (Δfc=0), the d-vector dynamics are too constrained.
#
# Specifically: in shift-only regime, define the "frontier position set"
# F = {i : d_i ≠ 0}. Each shift moves one frontier by one position.
# Boundary moves can change frontier types at positions {0, n-2, n-1}.
#
# Claim: the shift-only + boundary graph restricted to bad configs
# with a FIXED fc value has no cycles.
# ================================================================

def check_shift_only_cycles(n):
    """Build the graph of shift-only + boundary (Δfc=0) bad→bad transitions
    and check for cycles."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Build Δfc=0 bad→bad graph
    graph = defaultdict(list)
    for c in bad_set:
        fc_c = frontier_count(c, n)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set and frontier_count(succ, n) == fc_c:
                graph[c].append(succ)

    # Check for cycles using iterative Tarjan
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    nontrivial_sccs = []

    def strongconnect(v):
        work = [(v, 0)]
        index[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        while work:
            node, ni = work[-1]
            neighbors = graph[node]
            if ni < len(neighbors):
                work[-1] = (node, ni + 1)
                w = neighbors[ni]
                if w not in index:
                    index[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index[w])
            else:
                if lowlink[node] == index[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1:
                        nontrivial_sccs.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    for v in bad_set:
        if v not in index:
            strongconnect(v)

    has_cycles = len(nontrivial_sccs) > 0
    print(f"  n={n}: Δfc=0 bad→bad graph: {'CYCLES EXIST!' if has_cycles else 'NO CYCLES ✓'}"
          f" ({len(nontrivial_sccs)} non-trivial SCCs)")
    if has_cycles:
        for scc in nontrivial_sccs[:3]:
            print(f"    SCC size {len(scc)}: {scc[:3]}...")


# ================================================================
# KEY CLAIM 4 (THE PROOF): After top fires, the type-1 at d_{n-2}
# propagates left. When it reaches d_0, bottom fires.
# Case c_0=0: annihilation (Δfc=-2). DONE.
# Case c_0=1: type swap, c_0→0. Type-2 propagates right.
# Top fires again. Type-1 propagates left. At d_0: c_0=0. Annihilation.
#
# Verify: does c_0 stay 0 during phase 2+3 (no bottom re-enable)?
# ================================================================

def verify_c0_persistence(n):
    """After top fires and type-1 propagates to d_0 with c_0=1 (type swap),
    c_0 toggles to 0. Verify: during subsequent right propagation and
    second left propagation, bottom is NOT privileged (c_0 stays 0)."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Find configs just after type swap: c_0=0, d_0=2, d_{n-1}=1,
    # all interior d's are 0 except possibly d_0.
    # Actually, after full type-1 propagation + bottom type swap:
    # d = (2, 0, 0, ..., 0, 0, 1) and c_0=0.
    # But interior d's might not all be 0 if there were other frontiers.

    # Let's just check: for ALL bad configs with c_0=0, is bottom unprivileged?
    violations = 0
    for c in bad_set:
        if c[0] != 0:
            continue
        priv = get_privileged(c, fs, n)
        if 0 in priv:
            violations += 1

    # Also count: bad configs with c_0=0 where bottom IS privileged
    # These are the cases where the argument might break
    bot_priv_c0_0 = []
    for c in bad_set:
        if c[0] == 0:
            priv = get_privileged(c, fs, n)
            if 0 in priv:
                bot_priv_c0_0.append(c)

    print(f"  n={n}: bad configs with c_0=0: {sum(1 for c in bad_set if c[0]==0)}, "
          f"of which bottom privileged: {len(bot_priv_c0_0)}")
    if bot_priv_c0_0 and n <= 6:
        for c in sorted(bot_priv_c0_0)[:5]:
            d = get_d_vector(c, n)
            print(f"    {c} d={d}")


def verify_propagation_argument(n):
    """Verify the 2-round propagation argument:
    After top fires, if no other frontier interferes,
    the type-1 propagates to d_0 and bottom annihilates within 2 rounds.

    Key check: when type-1 reaches d_0 with d_{n-1}=2,
    does bottom ALWAYS give Δfc ≤ 0?
    """
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Check: for every config with d_0=1, d_{n-1}=2, bottom privileged:
    # what is Δfc after bottom fires?
    cases = defaultdict(int)
    for c in configs:
        d = get_d_vector(c, n)
        if d[0] != 1 or d[n-1] != 2:
            continue
        priv = get_privileged(c, fs, n)
        if 0 not in priv:
            continue
        succ = apply_move(c, 0, fs, n)
        dfc = frontier_count(succ, n) - frontier_count(c, n)
        cases[(c[0], dfc)] += 1

    print(f"  n={n}: bottom fires with d_0=1, d_{{n-1}}=2:")
    for (c0, dfc), cnt in sorted(cases.items()):
        print(f"    c_0={c0}: Δfc={dfc:+d} ({cnt} cases)")


if __name__ == "__main__":
    print("CLAIM 0: Top privilege d-values")
    verify_top_privilege_d_values(8)

    print("\nCLAIM 0b: Bottom privilege cases")
    verify_bottom_privilege_cases(6)

    print("\n" + "=" * 60)
    print("CLAIM 2: Max steps after top before fc decrease")
    print("=" * 60)
    for nv in range(3, 9):
        max_steps_after_top(nv)

    print("\n" + "=" * 60)
    print("CLAIM 3: Δfc=0 bad→bad graph acyclicity")
    print("=" * 60)
    for nv in range(3, 11):
        check_shift_only_cycles(nv)

    print("\n" + "=" * 60)
    print("CLAIM 4a: c_0=0 bottom privilege in bad configs")
    print("=" * 60)
    for nv in range(3, 8):
        verify_c0_persistence(nv)

    print("\n" + "=" * 60)
    print("CLAIM 4b: Propagation annihilation")
    print("=" * 60)
    for nv in range(3, 8):
        verify_propagation_argument(nv)
