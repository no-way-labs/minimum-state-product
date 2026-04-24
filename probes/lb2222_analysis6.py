"""Trace the Case D chain: under unique_privileged,
if partner(c_k) = c_j with m_j = m_k = m, trace through all steps
until we find a TF conflict or fairness violation."""

def flip(cfg, j):
    return cfg ^ (1 << j)

def get_bit(cfg, j):
    return (cfg >> j) & 1

def left_p(j):
    return (j + 3) % 4

def right_p(j):
    return (j + 1) % 4

def tf_key(cfg, proc):
    return (get_bit(cfg, left_p(proc)), get_bit(cfg, proc), get_bit(cfg, right_p(proc)))

def find_all_fair_cycles():
    cycles = []
    def dfs(start, cur, visited, path, fair_mask):
        for proc in range(4):
            nxt = flip(cur, proc)
            new_fair = fair_mask | (1 << proc)
            new_path = path + [(cur, proc)]
            if nxt == start:
                if new_fair == 15:
                    cycles.append(list(new_path))
            elif nxt not in visited and len(path) < 16:
                dfs(start, nxt, visited | {nxt}, new_path, new_fair)
    for s in range(16):
        dfs(s, s, {s}, [], 0)
    seen_canon = set()
    unique = []
    for cyc in cycles:
        L = len(cyc)
        rotations = [tuple(cyc[(r+i) % L] for i in range(L)) for r in range(L)]
        canon = min(rotations)
        if canon not in seen_canon:
            seen_canon.add(canon)
            unique.append(cyc)
    return unique

cycles = find_all_fair_cycles()

# For cycles where partner(c_0, m_0) IS in the cycle WITH SAME mover m_j = m_0:
# Trace through steps. At each step t:
# c_t and c_{j_t} (the "shadow") differ at some bit(s).
# If they differ at exactly one bit b, and proc m_t is mover at both,
# and b = anti(m_t): we can continue.
# Otherwise: identify the contradiction.

# Actually, under unique_privileged:
# 1. partner(c_k) = c_j, m_j = m (Step 4a)
# 2. c_{k+1} and c_{j+1} differ at anti(m)
# 3. At step k+1: proc m has same TF at c_{k+1} and c_{j+1}
#    - If m_{k+1} = m, m_{j+1} = m: Case A (both same). Continue to step k+2.
#      After enough steps of Case A: only proc m fires. Fairness violated.
#    - If m_{k+1} = m, m_{j+1} ≠ m: Case B. TF conflict at proc m.
#    - If m_{k+1} ≠ m, m_{j+1} = m: Case C. TF conflict at proc m.
#    - If m_{k+1} ≠ m, m_{j+1} ≠ m: Case D.
#      Proc m is non-mover at both, same TF. Consistent.
#      c_{k+2} = flip(c_{k+1}, m_{k+1}), c_{j+2} = flip(c_{j+1}, m_{j+1}).
#      If m_{k+1} = m_{j+1}: c_{k+2} and c_{j+2} still differ at anti(m) only.
#        At step k+2: same analysis with m_t and m_{t+4}.
#      If m_{k+1} ≠ m_{j+1}: c_{k+2} XOR c_{j+2} = e_{anti(m)} XOR e_{m_{k+1}} XOR e_{m_{j+1}}.
#        This is a multi-bit difference. The "partner" structure breaks.
#        But we can still check for TF conflict.

# The question: must we eventually hit Case B, C, or fairness violation?

# Let me trace concretely. For each cycle with partner-in-cycle + same-mover:
count_by_resolution = {"fairness": 0, "tf_conflict": 0, "unknown": 0}
total = 0

for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    cfg_to_idx = {c: i for i, (c, _) in enumerate(cyc)}
    L = len(cyc)

    for k0 in range(L):
        cfg_k0, m0 = cyc[k0]
        anti_m = (m0 + 2) % 4
        partner0 = flip(cfg_k0, anti_m)
        if partner0 not in cfg_set:
            continue
        j0 = cfg_to_idx[partner0]
        _, mj0 = cyc[j0]
        if mj0 != m0:
            continue  # Under unique_privileged this can't happen, skip

        total += 1

        # Trace through steps
        resolution = "unknown"
        only_m_fires = True
        for t in range(L):
            kt = (k0 + t + 1) % L
            jt = (j0 + t + 1) % L
            _, m_kt = cyc[kt]
            _, m_jt = cyc[jt]

            if m_kt != m0 or m_jt != m0:
                only_m_fires = False

            if m_kt == m0 and m_jt != m0:
                resolution = "tf_conflict"
                break
            elif m_kt != m0 and m_jt == m0:
                resolution = "tf_conflict"
                break
            elif m_kt == m0 and m_jt == m0:
                continue  # Case A
            else:
                # Case D: both different from m0
                # Check: do m_kt and m_jt differ?
                if m_kt != m_jt:
                    # Multi-bit difference develops. Check for TF conflict.
                    # At this point, c_{kt} and c_{jt} differ at anti(m0).
                    # c_{kt+1} and c_{jt+1} will differ at anti(m0) XOR e_{m_kt} XOR e_{m_jt}.
                    # Continue tracing...
                    pass
                # If m_kt = m_jt: single-bit difference preserved.
                continue

        if resolution == "unknown":
            if only_m_fires:
                resolution = "fairness"
            # Check if all steps had same mover
            movers_k = [cyc[(k0+t) % L][1] for t in range(L)]
            if all(m == m0 for m in movers_k):
                resolution = "fairness"

        count_by_resolution[resolution] += 1

print(f"Total partner-in-cycle with same mover: {total}")
print(f"Resolution: {count_by_resolution}")

# Let me trace more carefully for the "unknown" cases
print("\n=== Tracing unknown cases ===")
unknown_count = 0
for cyc in cycles:
    cfg_set = {c for c, _ in cyc}
    cfg_to_idx = {c: i for i, (c, _) in enumerate(cyc)}
    L = len(cyc)

    for k0 in range(L):
        cfg_k0, m0 = cyc[k0]
        anti_m = (m0 + 2) % 4
        partner0 = flip(cfg_k0, anti_m)
        if partner0 not in cfg_set:
            continue
        j0 = cfg_to_idx[partner0]
        _, mj0 = cyc[j0]
        if mj0 != m0:
            continue

        # Full trace
        found_conflict = False
        for t in range(L):
            kt = (k0 + t + 1) % L
            jt = (j0 + t + 1) % L
            _, m_kt = cyc[kt]
            _, m_jt = cyc[jt]

            if (m_kt == m0) != (m_jt == m0):
                found_conflict = True
                break

        if not found_conflict:
            # Check if sequence of m_kt and m_jt are always BOTH m0 or BOTH not m0
            # and whether the movers at k and j tracks are identical
            k_movers = [cyc[(k0+t) % L][1] for t in range(L)]
            j_movers = [cyc[(j0+t) % L][1] for t in range(L)]
            if all(m == m0 for m in k_movers):
                pass  # fairness
            else:
                unknown_count += 1
                if unknown_count <= 5:
                    print(f"  L={L}, k0={k0}, j0={j0}, m0={m0}")
                    print(f"    k_movers: {k_movers}")
                    print(f"    j_movers: {j_movers}")
                    # Check: are the movers synchronized?
                    synced = all(k_movers[t] == j_movers[t] for t in range(L))
                    print(f"    Synchronized: {synced}")
                    # Check: does the cycle have period (j0-k0)?
                    d = (j0 - k0) % L
                    periodic = all(k_movers[t] == k_movers[(t+d)%L] for t in range(L))
                    print(f"    Period d={d}: {periodic}")
                    # Count fires of m0
                    fires = sum(1 for m in k_movers if m == m0)
                    print(f"    Proc {m0} fires {fires} times in k-track")

print(f"Unknown cases requiring deeper analysis: {unknown_count}")
