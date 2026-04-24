"""
Binary adjacency constraint for Branch B.

Setup:
- Walker at min-CL with no stays.
- For each binary b, walker has fc[b] = 2 visits.
- Each visit has 2 adjacencies (incoming + outgoing step positions).
- Each adjacency is in one of b's 2 adjacent gaps.
- Total adjacencies at b = 2 * fc[b] = 4 (for binary).

For each gap G_j with boundaries b_j and b_{j+1}:
- T_j := number of G_j traversals.
- Each G_j traversal uses 1 adjacency at b_j and 1 at b_{j+1}.
- # G_j adjacencies at b_j = T_j.

At binary b_j, total adjacencies = (# G_{j-1} adjacencies) + (# G_j adjacencies) = T_{j-1} + T_j = 4.

So T_{j-1} + T_j = 4 for every binary b_j in the cycle.

For ternary mids in G_j, walker's fc[mid] = # G_j traversals = T_j.
Under min-CL, fc[mid] = m[mid] = 3. So T_j = 3 for any gap with ternary mids.
For binary mid, T_j = 2.

Claim: if ANY gap has a ternary mid, then T_j = 3, which combined with T_j + T_{j±1} = 4
forces T_{j±1} = 1. But T = 1 means the adjacent gap has 1 traversal, giving
its mids fc = 1, not a multiple of 2 (binary) or 3 (ternary). Invalid unless the
adjacent gap is empty (no mids).

So: under min-CL no-stay monotone gap runs, any gap with a ternary mid forces its
neighbors to be empty gaps (consecutive binaries with no mid between).
"""

def check_min_cl_feasibility(ms):
    """Check if min-CL no-stay monotone walker is feasible at given ms."""
    n = len(ms)
    binaries = [i for i, m in enumerate(ms) if m == 2]
    if len(binaries) < 3:
        return "insufficient binaries", None
    
    # Gaps are between consecutive binaries
    num_binaries = len(binaries)
    gaps = []  # list of (left_binary_idx, right_binary_idx, mids)
    for k in range(num_binaries):
        b_left = binaries[k]
        b_right = binaries[(k + 1) % num_binaries]
        # Mids strictly between b_left and b_right in cyclic order
        mids = []
        j = (b_left + 1) % n
        while j != b_right:
            mids.append((j, ms[j]))
            j = (j + 1) % n
        gaps.append((b_left, b_right, mids))
    
    # For each gap, determine T_j from its mids
    # T_j must equal fc[mid] for each mid in gap. Under min-CL, fc = m.
    # Binary mid: T_j = 2. Ternary mid: T_j = 3. Empty gap: T_j = any.
    T_required = []
    for (b_l, b_r, mids) in gaps:
        if not mids:
            T_required.append(None)  # any value allowed
        else:
            ms_in_gap = set(m for _, m in mids)
            if len(ms_in_gap) > 1:
                return f"gap ({b_l},{b_r}) has mixed moduli {ms_in_gap}", None
            m = mids[0][1]
            T_required.append(m)  # T_j = m (fc[mid] = m for monotone)
    
    # Solve the system: T_{j-1} + T_j = 4 at each binary
    # Fixed T_j from mids. Flexible (None) gaps get solved by propagation.
    T = list(T_required)
    # Propagate until no change
    for _ in range(num_binaries * 2):
        for k in range(num_binaries):
            # Constraint at binary k: T[k-1] + T[k] = 4
            kp = (k - 1) % num_binaries
            if T[kp] is None and T[k] is not None:
                T[kp] = 4 - T[k]
            elif T[k] is None and T[kp] is not None:
                T[k] = 4 - T[kp]

    # Check all constraints
    issues = []
    for k in range(num_binaries):
        T_prev = T[(k - 1) % num_binaries]
        T_curr = T[k]
        if T_prev is None or T_curr is None:
            issues.append(f"at binary {binaries[k]}: underdetermined")
        elif T_prev + T_curr != 4:
            issues.append(f"at binary {binaries[k]}: T_{(k-1)%num_binaries}={T_prev} + T_{k}={T_curr} = {T_prev+T_curr} != 4")
        elif T_curr < 0:
            issues.append(f"T_{k}={T_curr} negative")

    if issues:
        return "INFEASIBLE: " + "; ".join(issues), T

    return "feasible", T


# Test on representative families
families = [
    ("n=9 all-odd-gap", [2,3,3,2,3,3,2,3,3]),
    ("n=9 3cb", [2,2,2,3,3,3,3,3,3]),
    ("n=9 pivot", [2,3,3,3,2,3,3,3,2]),
    ("n=9 spaced", [2,2,3,2,3,3,3,3,3]),
    ("n=11 all-odd 4binary", [2,3,3,2,3,3,2,3,3,2,3]),
    ("n=5 M5-witness", [2,2,2,3,3]),
]

for name, ms in families:
    status, T = check_min_cl_feasibility(ms)
    print(f"{name}: {ms}")
    print(f"  status: {status}")
    print(f"  T: {T}")
    print()


# Search for feasible family structures
print("\n" + "="*60)
print("Searching for FEASIBLE min-CL no-stay monotone walker families at n=9:")
print("="*60)

from itertools import product as iproduct

feasible = []
n = 9
for ms_tuple in iproduct([2, 3], repeat=n):
    ms = list(ms_tuple)
    binaries = [i for i, m in enumerate(ms) if m == 2]
    if len(binaries) < 3:
        continue
    # Sub-threshold check
    prod = 1
    for m in ms:
        prod *= m
    if prod >= 4 * (3 ** (n-2)):
        continue
    status, T = check_min_cl_feasibility(ms)
    if status == "feasible":
        feasible.append((ms, T, prod))

print(f"Feasible sub-threshold n=9 families with only m ∈ {{2,3}}: {len(feasible)}")
for ms, T, prod in feasible[:20]:
    print(f"  ms={ms}, T={T}, product={prod}")

# Group by binary count
by_bin_count = {}
for ms, T, prod in feasible:
    bcount = ms.count(2)
    by_bin_count[bcount] = by_bin_count.get(bcount, 0) + 1
print(f"\nBy binary count: {by_bin_count}")
