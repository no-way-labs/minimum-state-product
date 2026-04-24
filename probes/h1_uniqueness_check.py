"""
Check H-1 Uniqueness: do consecutive firings at same proc happen in good cycles?
If so, is the stated theorem false?
"""
import sys
sys.path.insert(0, './claude')
from verifier import verify_system, verify_dijkstra_solution1, verify_dijkstra_solution3

def get_good_cycle_info(ms, tables):
    """Get good cycle configs and movers from a valid system."""
    n = len(ms)

    # Build transition function
    def fire(config, p):
        L = config[(p - 1) % n]
        S = config[p]
        R = config[(p + 1) % n]
        new_val = tables[p][(L, S, R)]
        new_config = list(config)
        new_config[p] = new_val
        return tuple(new_config)

    def is_good(config):
        """A config is good if exactly one proc is privileged (would change on firing)."""
        n_priv = 0
        priv_proc = -1
        for p in range(n):
            L = config[(p - 1) % n]
            S = config[p]
            R = config[(p + 1) % n]
            if tables[p][(L, S, R)] != S:
                n_priv += 1
                priv_proc = p
        if n_priv == 1:
            return True, priv_proc
        return False, -1

    # Find all good configs
    from itertools import product as iprod
    ranges = [range(m) for m in ms]

    good_configs = {}
    for config in iprod(*ranges):
        ok, priv = is_good(config)
        if ok:
            good_configs[config] = priv

    # Build good cycle: start from any good config, follow transitions
    if not good_configs:
        return None, None, None

    start = next(iter(good_configs))
    cycle = [start]
    movers = [good_configs[start]]

    current = start
    while True:
        priv = good_configs[current]
        nxt = fire(current, priv)
        if nxt == start:
            break
        if nxt not in good_configs:
            # Not a good config - this shouldn't happen in a valid system's good cycle
            return None, None, None
        cycle.append(nxt)
        movers.append(good_configs[nxt])
        current = nxt
        if len(cycle) > 10000:
            return None, None, None

    return cycle, movers, good_configs


def check_h1_uniqueness(ms, tables, label=""):
    """Check H-1 uniqueness for a system."""
    cycle, movers, good_configs = get_good_cycle_info(ms, tables)
    if cycle is None:
        print(f"  {label}: could not extract good cycle")
        return

    CL = len(cycle)
    n = len(ms)
    print(f"  {label}: n={n}, ms={ms}, CL={CL}, #good={len(good_configs)}")

    # Check for consecutive same-mover
    consec_same = []
    for i in range(CL):
        if movers[i] == movers[(i+1) % CL]:
            consec_same.append((i, movers[i]))
    if consec_same:
        print(f"    Consecutive same-mover: {consec_same[:10]}")
    else:
        print(f"    No consecutive same-mover firings")

    # Check ALL pairs for Hamming-1
    h1_pairs = []
    for j in range(CL):
        for k in range(j+1, CL):
            diff_positions = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff_positions) == 1:
                dist = min(k - j, CL - (k - j))
                h1_pairs.append((j, k, diff_positions[0], dist))

    # Adjacent pairs should all be Hamming-1
    adj_h1 = [(j, k, p, d) for j, k, p, d in h1_pairs if d == 1]
    nonadj_h1 = [(j, k, p, d) for j, k, p, d in h1_pairs if d > 1]

    print(f"    Total H-1 pairs: {len(h1_pairs)}, adjacent: {len(adj_h1)}, non-adjacent: {len(nonadj_h1)}")
    if nonadj_h1:
        print(f"    *** COUNTEREXAMPLE! Non-adjacent H-1 pairs: ***")
        for j, k, p, d in nonadj_h1[:5]:
            print(f"      j={j}, k={k}, pos={p}, dist={d}")
            print(f"        g_j = {cycle[j]}, mover_j = {movers[j]}")
            print(f"        g_k = {cycle[k]}, mover_k = {movers[k]}")
    else:
        print(f"    H-1 Uniqueness HOLDS")


# Test Sol3 at n=5
print("=== Sol3 n=5 ===")
ms_sol3 = [3,3,3,3,3]
n = 5
tables_sol3 = []
for p in range(n):
    t = {}
    for L in range(3):
        for S in range(3):
            for R in range(3):
                if p == 0:
                    t[(L, S, R)] = R if S == L else S
                else:
                    t[(L, S, R)] = L if S != L else S
    tables_sol3.append(t)
check_h1_uniqueness(ms_sol3, tables_sol3, "Sol3")

# Test CUP-2 at various n
print("\n=== CUP-2 ===")
# CUP-2 tables from cup2_theorem.py
T_low = {}
T_mid = {}
T_high = {}
T_left = {}
T_right = {}

# T_left (proc 0): binary, ms[0]=2
for L in range(2):
    for S in range(2):
        for R in range(3):
            T_left[(L,S,R)] = (S+1)%2 if (S+R)%3 != 0 and S == L else S

# Actually let me just load the tables from the existing scripts
# Let me build CUP-2 from scratch based on the known rules

def build_cup2_tables(n):
    """Build CUP-2 tables for ms=(2,3,...,3,2)."""
    ms = [2] + [3]*(n-2) + [2]

    # T_left for proc 0 (binary)
    T_left = {}
    for L in range(2):
        for S in range(2):
            for R in range(3):
                # proc 0: privileged when S != (S+R)%...
                # Actually need to get exact rules
                pass
    return ms, None

# Let me just use verify_dijkstra_solution3 and solution1 for quick tests
# And build systems from the verifier

# Instead, let me test with known valid systems computationally

def build_sol3v1(n):
    """Sol 3 v1: ms=(2,3,...,3), product 2*3^(n-1)."""
    ms = [2] + [3]*(n-1)
    tables = []
    for p in range(n):
        t = {}
        if p == 0:
            # Binary proc: privileged when S == L
            for L in range(ms[(p-1)%n]):
                for S in range(ms[p]):
                    for R in range(ms[(p+1)%n]):
                        if S == L:
                            t[(L,S,R)] = (S+1) % ms[p]
                        else:
                            t[(L,S,R)] = S
        else:
            # Ternary proc: privileged when S != L
            for L in range(ms[(p-1)%n]):
                for S in range(ms[p]):
                    for R in range(ms[(p+1)%n]):
                        if S != L:
                            t[(L,S,R)] = L
                        else:
                            t[(L,S,R)] = S
        tables.append(t)
    return ms, tables

for n in [5, 7, 9]:
    ms, tables = build_sol3v1(n)
    check_h1_uniqueness(ms, tables, f"Sol3v1 n={n}")

print("\n=== M_5 = 96 witness: ms=(2,2,2,3,4) ===")
# Build from verifier
# Actually let me search for M_5 witness
# The M_5=96 system is at ms=(2,2,2,3,4). Let me find it.

# For now, test with Dijkstra's solutions
print("\n=== Dijkstra Sol1 n=5 ===")
ms_d1 = [5,5,5,5,5]  # all K-state
# Sol1: proc 0 privileged when S==L, fires S=(S+1)%K
#        proc i>0 privileged when S!=L, fires S=L
tables_d1 = []
K = 5
for p in range(5):
    t = {}
    for L in range(K):
        for S in range(K):
            for R in range(K):
                if p == 0:
                    t[(L,S,R)] = (S+1)%K if S == L else S
                else:
                    t[(L,S,R)] = L if S != L else S
    tables_d1.append(t)
check_h1_uniqueness(ms_d1, tables_d1, "Dijkstra Sol1 K=5")

print("\n=== Dijkstra Sol1 K=6, n=5 ===")
K = 6
tables_d1_6 = []
for p in range(5):
    t = {}
    for L in range(K):
        for S in range(K):
            for R in range(K):
                if p == 0:
                    t[(L,S,R)] = (S+1)%K if S == L else S
                else:
                    t[(L,S,R)] = L if S != L else S
    tables_d1_6.append(t)
check_h1_uniqueness([K]*5, tables_d1_6, "Dijkstra Sol1 K=6")
