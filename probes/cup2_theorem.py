#!/usr/bin/env python3
"""Clean statement and verification of the CUP-2 Theorem.

THEOREM (CUP-2 Universal Rules):
For all n >= 5, there exists a self-stabilizing token ring with
  ms = (2, 3, 3, ..., 3, 2)  (n processors, product 4·3^{n-2})
defined by 5 fixed lookup tables (87 entries total) that are
completely n-independent.

The system satisfies all 5 Dijkstra properties:
  (L) Liveness: every configuration has ≥1 privileged processor
  (ME) Mutual Exclusion: every good config has exactly 1 privilege
  (CL) Closure: the good set is closed under transitions
  (CV) Convergence: the bad-config graph is acyclic (DAG)
  (F) Fairness: every processor fires in the good cycle

Formulas (n ≥ 5):
  Cycle length       = 3n - 2
  Good configs       = (n+2)(n+3)/2 - 5  =  (n² + 5n - 4)/2
  Tail configs       = n(n-1)/2
  Determined entries  = 9n - 6
  Free entries        = 18n - 42
  Privileged entries  = 13n - 21
  DAG depth           ~ O(n²)

STATUS: Computationally verified for n = 5, 6, 7, ..., 13.
        Properties L, ME, CL, F are provable analytically from table structure.
        Property CV (convergence) is verified but open for analytical proof.
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque
from verifier import verify_system

# ================================================================
# THE 5 UNIVERSAL LOOKUP TABLES (87 entries total)
# ================================================================

# T_bot: P_0, bottom binary (m_L=2, m_S=2, m_R=3) — 12 entries
T_bot = {
    (0,0,0): 1,  (0,0,1): 1,  (0,0,2): 0,
    (0,1,0): 1,  (0,1,1): 1,  (0,1,2): 1,
    (1,0,0): 0,  (1,0,1): 1,  (1,0,2): 0,
    (1,1,0): 0,  (1,1,1): 1,  (1,1,2): 0,
}

# T_low: P_1, lower boundary ternary (m_L=2, m_S=3, m_R=3) — 18 entries
T_low = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
}

# T_mid: interior ternary (m_L=3, m_S=3, m_R=3) — 27 entries
# NOTE: entry (2,1,1) = 0 is the liveness fix
T_mid = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
    (2,0,0): 0,  (2,0,1): 0,  (2,0,2): 2,
    (2,1,0): 1,  (2,1,1): 0,  (2,1,2): 2,
    (2,2,0): 0,  (2,2,1): 2,  (2,2,2): 2,
}

# T_high: P_{n-2}, upper boundary ternary (m_L=3, m_S=3, m_R=2) — 18 entries
# NOTE: entry (2,1,0) = 0 is the n=4 liveness fix
T_high = {
    (0,0,0): 0,  (0,0,1): 0,
    (0,1,0): 0,  (0,1,1): 0,
    (0,2,0): 0,  (0,2,1): 0,
    (1,0,0): 1,  (1,0,1): 1,
    (1,1,0): 1,  (1,1,1): 2,
    (1,2,0): 0,  (1,2,1): 2,
    (2,0,0): 0,  (2,0,1): 2,
    (2,1,0): 0,  (2,1,1): 2,
    (2,2,0): 2,  (2,2,1): 2,
}

# T_top: P_{n-1}, top binary (m_L=3, m_S=2, m_R=2) — 12 entries
T_top = {
    (0,0,0): 0,  (0,0,1): 0,
    (0,1,0): 0,  (0,1,1): 0,
    (1,0,0): 0,  (1,0,1): 1,
    (1,1,0): 1,  (1,1,1): 1,
    (2,0,0): 1,  (2,0,1): 1,
    (2,1,0): 1,  (2,1,1): 1,
}


def build_system(n):
    """Build transition functions from universal tables for given n."""
    assert n >= 4
    ms = [2] + [3] * (n - 2) + [2]

    def make_f(table):
        def f(L, S, R):
            return table[(L, S, R)]
        return f

    if n == 4:
        fs = [make_f(T_bot), make_f(T_low), make_f(T_high), make_f(T_top)]
    elif n == 5:
        fs = [make_f(T_bot), make_f(T_low), make_f(T_mid),
              make_f(T_high), make_f(T_top)]
    else:
        fs = [make_f(T_bot), make_f(T_low)]
        for _ in range(2, n - 2):
            fs.append(make_f(T_mid))
        fs.append(make_f(T_high))
        fs.append(make_f(T_top))

    return ms, fs


def dag_analysis(ms, fs, good_set, n):
    """Check DAG property and compute depth."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    in_deg = {c: 0 for c in bad_set}
    adj = {c: [] for c in bad_set}
    for c in bad_set:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            if fs[i](L, S, R) != S:
                lst = list(c)
                lst[i] = fs[i](L, S, R)
                succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    in_deg[succ] += 1

    q = deque(c for c in bad_set if in_deg[c] == 0)
    processed = 0
    topo = []
    while q:
        c = q.popleft()
        processed += 1
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    is_dag = (processed == len(bad_set))
    max_depth = 0
    if is_dag:
        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
        max_depth = max(rank.values()) if rank else 0

    return is_dag, max_depth, len(bad_set)


def count_structural(ms, fs, n):
    """Count determined, free, privileged entries."""
    # Build bounce cycle
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (3 * n)
    movers = []
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            break
        visited.add(nc)
        cycle.append(nc)

    # Count determined entries (those exercised by the cycle)
    det = set()
    for idx in range(len(cycle)):
        c = cycle[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            det.add((p, L, S, R))

    # Count total entries
    total = 0
    priv = 0
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    total += 1
                    if fs[p](L, S, R) != S:
                        priv += 1

    n_det = len(det)
    n_free = total - n_det

    return len(cycle), n_det, n_free, priv


def main():
    print("=" * 95)
    print("CUP-2 THEOREM: Universal Self-Stabilizing Token Ring")
    print("ms = (2, 3, ..., 3, 2),  product = 4·3^(n-2)")
    print("5 lookup tables, 87 entries, completely n-independent")
    print("=" * 95)

    print(f"\n{'n':>3} {'prod':>8} {'dead':>5} {'valid':>5} {'cycle':>5} "
          f"{'good':>5} {'tails':>5} {'det':>5} {'free':>5} {'priv':>5} "
          f"{'DAG':>4} {'depth':>5} {'time':>6}")
    print("-" * 95)

    all_pass = True
    for nv in range(4, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 1000000:
            print(f"{nv:>3} {prod:>8}  SKIP")
            continue

        t0 = time.time()
        ms, fs = build_system(nv)
        n = nv

        # Count dead configs
        all_configs = list(cartesian(*(range(m) for m in ms)))
        dead_count = sum(1 for c in all_configs if not any(
            fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i] for i in range(n)))

        # Full verification
        result = verify_system(ms, fs)
        valid = result['valid']
        if not valid:
            all_pass = False

        n_good = len(result.get('good_configs', set())) if valid else 0
        cyc_len, n_det, n_free, n_priv = count_structural(ms, fs, n)
        n_tails = n_good - cyc_len

        # DAG analysis
        is_dag = False
        depth = 0
        n_bad = 0
        if valid:
            good_set = result['good_configs']
            is_dag, depth, n_bad = dag_analysis(ms, fs, good_set, n)

        elapsed = time.time() - t0

        print(f"{nv:>3} {prod:>8} {dead_count:>5} "
              f"{'Y' if valid else 'N':>5} {cyc_len:>5} {n_good:>5} {n_tails:>5} "
              f"{n_det:>5} {n_free:>5} {n_priv:>5} "
              f"{'Y' if is_dag else 'N':>4} {depth:>5} {elapsed:>6.1f}")

    # Verify formulas
    print("\n" + "=" * 95)
    print("FORMULA VERIFICATION (n >= 5)")
    print("-" * 95)
    print(f"{'n':>3} {'cycle':>7} {'exp':>5} {'good':>7} {'exp':>7} "
          f"{'tails':>7} {'exp':>5} {'det':>5} {'exp':>5} "
          f"{'free':>5} {'exp':>5} {'priv':>5} {'exp':>5}")
    print("-" * 95)

    for nv in range(5, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 1000000:
            break

        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        if not result['valid']:
            continue

        n_good = len(result['good_configs'])
        cyc_len, n_det, n_free, n_priv = count_structural(ms, fs, n)
        n_tails = n_good - cyc_len

        # Expected formulas
        e_cyc = 3 * n - 2
        e_good = (n + 2) * (n + 3) // 2 - 5
        e_tails = n * (n - 1) // 2
        e_det = 9 * n - 6
        e_free = 18 * n - 42
        e_priv = 13 * n - 21

        def check(actual, expected):
            return "." if actual == expected else "X"

        print(f"{nv:>3} {cyc_len:>5}{check(cyc_len,e_cyc):>2} {e_cyc:>5} "
              f"{n_good:>5}{check(n_good,e_good):>2} {e_good:>7} "
              f"{n_tails:>5}{check(n_tails,e_tails):>2} {e_tails:>5} "
              f"{n_det:>5}{check(n_det,e_det)}{e_det:>5} "
              f"{n_free:>5}{check(n_free,e_free)}{e_free:>5} "
              f"{n_priv:>5}{check(n_priv,e_priv)}{e_priv:>5}")

    print("\n" + "=" * 95)
    if all_pass:
        print("ALL n=4..13 VERIFIED SUCCESSFULLY")
    else:
        print("SOME FAILURES")

    # Print the tables in a compact format for the paper
    print("\n" + "=" * 95)
    print("LOOKUP TABLES (paper format)")
    print("=" * 95)

    tables = [
        ("T_bot", T_bot, 2, 2, 3, "P_0 (binary, left=binary, right=ternary)"),
        ("T_low", T_low, 2, 3, 3, "P_1 (ternary, left=binary, right=ternary)"),
        ("T_mid", T_mid, 3, 3, 3, "P_i for 2 ≤ i ≤ n-3 (all ternary neighbors)"),
        ("T_high", T_high, 3, 3, 2, "P_{n-2} (ternary, left=ternary, right=binary)"),
        ("T_top", T_top, 3, 2, 2, "P_{n-1} (binary, left=ternary, right=binary)"),
    ]

    for name, table, m_L, m_S, m_R, desc in tables:
        n_priv_t = sum(1 for k, v in table.items() if v != k[1])
        print(f"\n{name}: {desc}")
        print(f"  {m_L}×{m_S}×{m_R} = {m_L*m_S*m_R} entries, {n_priv_t} privileged")
        # Print as a matrix: rows are (L,S), columns are R
        header = "    (L,S)\\R  " + "  ".join(f"{r:>2}" for r in range(m_R))
        print(header)
        for L in range(m_L):
            for S in range(m_S):
                entries = []
                for R in range(m_R):
                    out = table[(L, S, R)]
                    mark = "*" if out != S else " "
                    entries.append(f"{out}{mark}")
                print(f"    ({L},{S})    {'  '.join(entries)}")


if __name__ == "__main__":
    main()
