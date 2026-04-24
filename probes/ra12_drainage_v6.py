"""
RA12 v6: Clean final analysis — what actually differentiates valid from invalid.

CORRECTED FINDINGS:
- Sol1 K=3 n=5 is NOT valid (verify_system confirms)
- Sol1 K=4 n=5 IS valid (product 1024 >> threshold 108)
- M_5=96 IS valid (at threshold)

The comparison table shows:
- Valid systems: InCycle = 0
- Invalid systems: InCycle > 0 (always)

The drainage basin idea doesn't yield a simpler argument because:
1. The basin is always = P (both valid and invalid via reachability)
2. The differentiator is nondeterministic bad cycles
3. Binary flip doesn't create shadow traps

But let's extract what IS useful from this investigation.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
from collections import defaultdict, deque, Counter
from verifier import all_configs, privileged_set, apply_move, verify_system


def build_m5_96_witness():
    ms = [2, 2, 2, 3, 4]
    tables = [
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,
         (1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,
         (3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,0,3):0,
         (0,1,0):1,(0,1,1):2,(0,1,2):1,(0,1,3):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):2,(0,2,3):2,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,
         (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,1,3):1,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):1,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):1,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):0,(1,3,0):3,(1,3,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):0,(2,3,0):3,(2,3,1):0},
    ]
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R): return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return ms, fs


def build_sol1(n, K):
    ms = [K]*n
    def f_dist(L, S, R):
        if L == S: return (S+1)%K
        return S
    def f_other(L, S, R):
        if L != S: return L
        return S
    return ms, [f_dist] + [f_other]*(n-1)


def full_stats(ms, fs, label):
    """Complete statistics for one system."""
    n = len(ms)
    P = 1
    for m in ms: P *= m

    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}

    # Verify
    result = verify_system(ms, fs)
    valid = result['valid']

    # Find good cycle
    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        s = apply_move(c, priv_map[c][0], fs, ms)
        succ[c] = (s, priv_map[c][0])

    gc = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_rm = {c for c in gc if succ.get(c,(None,))[0] not in gc}
        if to_rm:
            gc -= to_rm
            changed = True

    visited = set()
    cycle_set = set()
    for c in gc:
        if c in visited: continue
        path, ps = [], set()
        node = c
        while node not in visited and node not in ps:
            path.append(node); ps.add(node)
            node = succ[node][0]
        if node in ps:
            cycle_set.update(path[path.index(node):])
        visited.update(path)

    CL = len(cycle_set)
    if CL == 0:
        return None

    # Nondeterministic bad graph
    bad = set(configs) - cycle_set
    bad_edges = 0
    escape_edges = 0
    bad_succs = defaultdict(set)
    for c in bad:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            if s in bad:
                bad_edges += 1
                bad_succs[c].add(s)
            else:
                escape_edges += 1

    trapped = sum(1 for c in bad if all(apply_move(c, p, fs, ms) in bad for p in priv_map[c]))

    in_cycle = set()
    for c in bad:
        if not bad_succs[c]: continue
        reachable = set(bad_succs[c])
        queue = deque(bad_succs[c])
        while queue:
            node = queue.popleft()
            if node == c:
                in_cycle.add(c)
                break
            for s in bad_succs[node]:
                if s not in reachable:
                    reachable.add(s)
                    queue.append(s)

    threshold = 4 * 3**(n-2)
    below = P < threshold

    return {
        'label': label, 'ms': list(ms), 'P': P, 'n': n,
        'valid': valid, 'below_threshold': below,
        'CL': CL, 'single_priv': len(single_priv),
        'bad': len(bad), 'bad_edges': bad_edges,
        'escape_edges': escape_edges,
        'trapped': trapped, 'in_cycle': len(in_cycle),
        'escape_ratio': escape_edges/(bad_edges+escape_edges) if bad_edges+escape_edges > 0 else 1.0,
    }


def main():
    print("=" * 70)
    print("RA12: DRAINAGE BASIN ANALYSIS — FINAL RESULTS")
    print("=" * 70)

    results = []

    # Valid systems
    ms96, fs96 = build_m5_96_witness()
    results.append(full_stats(ms96, fs96, "M_5=96 witness"))

    ms_s4, fs_s4 = build_sol1(5, 4)
    results.append(full_stats(ms_s4, fs_s4, "Sol1 K=4 n=5"))

    # Dijkstra Sol3 n=5
    ms_d3 = [3]*5
    def f_bot(L,S,R): return (S-1)%3 if (S+1)%3==R else S
    def f_top(L,S,R): return (L+1)%3 if L==R and (L+1)%3!=S else S
    def f_mid(L,S,R):
        if (S+1)%3==L: return L
        if (S+1)%3==R: return R
        return S
    fs_d3 = [f_bot]+[f_mid]*3+[f_top]
    results.append(full_stats(ms_d3, fs_d3, "Sol3 n=5"))

    # Invalid systems (Sol1-style on various sub-threshold)
    for ms_test in [[2]*5, [2,2,2,2,3], [2,2,2,3,3], [2,2,2,3,4]]:
        n_t = len(ms_test)
        fs_t = []
        for i in range(n_t):
            m = ms_test[i]
            if i == 0:
                def f(L,S,R,m=m):
                    if L==S: return (S+1)%m
                    return S
            else:
                def f(L,S,R,m=m):
                    if L!=S: return L%m
                    return S
            fs_t.append(f)
        r = full_stats(ms_test, fs_t, f"Sol1 {ms_test}")
        if r:
            results.append(r)

    # Sol1 K=3 n=5 (invalid)
    ms_s3, fs_s3 = build_sol1(5, 3)
    results.append(full_stats(ms_s3, fs_s3, "Sol1 K=3 n=5"))

    # Print comparison table
    print(f"\n{'Label':<25} {'ms':>18} {'P':>5} {'Valid':>5} {'<Thr':>4} {'CL':>4} {'SP%':>5} {'Bad':>5} {'Trap':>5} {'InCyc':>5} {'EscR':>5}")
    print("-" * 112)
    for r in results:
        if r is None: continue
        sp_pct = 100*r['single_priv']/r['P']
        print(f"{r['label']:<25} {str(r['ms']):>18} {r['P']:>5} {str(r['valid']):>5} {str(r['below_threshold']):>4} "
              f"{r['CL']:>4} {sp_pct:>4.1f}% {r['bad']:>5} {r['trapped']:>5} {r['in_cycle']:>5} {r['escape_ratio']:>5.3f}")

    print(f"""
KEY FINDINGS:
=============

1. VALID systems have InCycle = 0 (no bad cycles in nondeterministic graph)
   INVALID systems have InCycle > 0

2. The single-privilege fraction (SP%) is always small (5-31%).
   The vast majority of configs are multi-privileged.
   This is NOT what distinguishes valid from invalid.

3. The Trapped count (configs with ALL successors staying in bad region)
   is nonzero even for VALID systems (44 for M_5=96, 832 for Sol1 K=4).
   Being "trapped" (all moves stay in bad) doesn't prevent convergence
   because there may be NO CYCLE among the trapped configs — they're
   on a DAG that eventually reaches configs WITH an escape.

4. The escape ratio (fraction of edges going from bad to good) is low
   for all systems (5-43%). Even valid systems have most bad-to-bad edges.

5. CRITICAL DIFFERENCE: InCycle = 0 for valid, InCycle > 0 for invalid.
   This is literally the definition of convergence.
   The drainage basin / capacity bound approach was trying to find a
   STRUCTURAL REASON why InCycle must be > 0 for sub-threshold systems.

6. The binary flip / parallel sheet idea fails because:
   a) Fairness => no position always far from all movers
   b) Even for ONE step, flipping a binary proc can change privilege
      at positions whose context includes the flipped proc
   c) The transition function values (not just structure) change with flip

NEGATIVE RESULT:
================
The drainage basin capacity bound does NOT provide a simpler proof.
The reason is that the basin is always = P (full reachability) for both
valid and invalid systems. The differentiator is the CYCLIC structure
within the nondeterministic bad graph, which is exactly what the existing
proof approaches (entry conflict, shadow cycles, etc.) already address.

The existing proof strategy (entry conflict + shadow cycles) is attacking
the problem at the right level: it shows that any good cycle must have
structural properties that force bad cycles in the nondeterministic graph.
A capacity bound would need to show "not enough room for all configs to
drain" — but there IS enough room (full basin = P), the issue is that
the daemon can CHOOSE to cycle.
""")


if __name__ == "__main__":
    main()
