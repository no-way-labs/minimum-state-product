#!/usr/bin/env python3
"""Final verification of the TRULY universal rules for ms=(2,3,...,3,2).

The system is defined by 5 lookup tables (87 entries total) that are
COMPLETELY n-independent. No per-n adjustment needed.

Two liveness fixes (both n-independent):
  T_mid(2,1,1)  = 0  (fixes dead config (0,2,1,...,1,0) for n>=5)
  T_high(2,1,0) = 0  (fixes dead config (0,2,1,0) for n=4)
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque
from verifier import verify_system

# ================================================================
# THE 5 UNIVERSAL LOOKUP TABLES
# ================================================================

# T_bot: P0, bottom binary (m_L=2, m_S=2, m_R=3)
T_bot = {
    (0,0,0): 1,  (0,0,1): 1,  (0,0,2): 0,
    (0,1,0): 1,  (0,1,1): 1,  (0,1,2): 1,
    (1,0,0): 0,  (1,0,1): 1,  (1,0,2): 0,
    (1,1,0): 0,  (1,1,1): 1,  (1,1,2): 0,
}

# T_low: P1, lower boundary ternary (m_L=2, m_S=3, m_R=3)
T_low = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
}

# T_mid: interior ternary (m_L=3, m_S=3, m_R=3)
# NOTE: entry (2,1,1) = 0 is the liveness fix (was 1 in greedy n≥6)
T_mid = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
    (2,0,0): 0,  (2,0,1): 0,  (2,0,2): 2,
    (2,1,0): 1,  (2,1,1): 0,  (2,1,2): 2,  # ← (2,1,1)=0 is the fix
    (2,2,0): 0,  (2,2,1): 2,  (2,2,2): 2,
}

# T_high: P_{n-2}, upper boundary ternary (m_L=3, m_S=3, m_R=2)
T_high = {
    (0,0,0): 0,  (0,0,1): 0,
    (0,1,0): 0,  (0,1,1): 0,
    (0,2,0): 0,  (0,2,1): 0,
    (1,0,0): 1,  (1,0,1): 1,
    (1,1,0): 1,  (1,1,1): 2,
    (1,2,0): 0,  (1,2,1): 2,
    (2,0,0): 0,  (2,0,1): 2,
    (2,1,0): 0,  (2,1,1): 2,  # ← (2,1,0)=0 is the n=4 liveness fix
    (2,2,0): 2,  (2,2,1): 2,
}

# T_top: P_{n-1}, top binary (m_L=3, m_S=2, m_R=2)
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
        # No T_mid procs: P0=T_bot, P1=T_low, P2=T_high, P3=T_top
        fs = [make_f(T_bot), make_f(T_low), make_f(T_high), make_f(T_top)]
    elif n == 5:
        # One T_mid proc: P0=T_bot, P1=T_low, P2=T_mid, P3=T_high, P4=T_top
        fs = [make_f(T_bot), make_f(T_low), make_f(T_mid),
              make_f(T_high), make_f(T_top)]
    else:
        # General: P0=T_bot, P1=T_low, P2..P_{n-3}=T_mid, P_{n-2}=T_high, P_{n-1}=T_top
        fs = [make_f(T_bot), make_f(T_low)]
        for _ in range(2, n - 2):
            fs.append(make_f(T_mid))
        fs.append(make_f(T_high))
        fs.append(make_f(T_top))

    return ms, fs


def dag_depth(ms, fs, good_set, n):
    """Compute DAG depth of bad-config graph."""
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

    return is_dag, max_depth


def main():
    print("TRULY UNIVERSAL RULES FOR ms=(2,3,...,3,2)")
    print("5 lookup tables, 87 entries total, NO per-n adjustments")
    print("=" * 90)
    print(f"{'n':>3} {'prod':>8} {'dead':>5} {'valid':>6} {'good':>6} "
          f"{'cycle':>6} {'DAG':>4} {'depth':>6} {'time':>6}")
    print("-" * 90)

    all_valid = True
    for nv in range(4, 15):
        prod = 4 * 3 ** (nv - 2)
        if prod > 1000000:
            print(f"{nv:>3} {prod:>8} SKIP (too large)")
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
            all_valid = False

        n_good = len(result.get('good_configs', set())) if valid else 0
        cyc_len = result.get('cycle_length', 0) if valid else 0

        # DAG analysis
        is_dag = False
        depth = 0
        if valid:
            good_set = result['good_configs']
            is_dag, depth = dag_depth(ms, fs, good_set, n)

        elapsed = time.time() - t0
        print(f"{nv:>3} {prod:>8} {dead_count:>5} "
              f"{'Y' if valid else 'N':>6} {n_good:>6} {cyc_len:>6} "
              f"{'Y' if is_dag else 'N':>4} {depth:>6} {elapsed:>6.1f}")

    print()
    if all_valid:
        print("ALL VERIFIED: The universal rules produce valid systems for all tested n!")
    else:
        print("SOME FAILURES DETECTED")

    # Print good config formula
    print("\nGood config sequence:")
    for nv in range(4, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 1000000:
            break
        ms, fs = build_system(nv)
        result = verify_system(ms, fs)
        if result['valid']:
            g = len(result['good_configs'])
            formula = (nv + 2) * (nv + 3) // 2 - 5
            print(f"  n={nv}: good={g}, (n+2)(n+3)/2-5={formula}, "
                  f"{'MATCH' if g == formula else 'MISMATCH'}")


if __name__ == "__main__":
    main()
