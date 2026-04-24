"""Check deleteConfig_bad_preserved: is it true that
   c not in GoodCycle(n) implies deleteConfig(c,k) not in GoodCycle(n-1)?

   Counterexample candidate: n=9, k=4, c=(1,1,1,1,2,0,0,0,0).
"""

def cup2CycleVal(n, t, j):
    """Exact match of the Lean definition."""
    if t < n:
        return 1 if j < t else 0
    elif t < 2*n - 2:
        if j < 2*n - 1 - t:
            return 1
        elif j < n - 1:
            return 2
        else:
            return 1
    elif t == 2*n - 2:
        if j == 0:
            return 1
        elif j < n - 1:
            return 2
        else:
            return 1
    else:
        k = t - (2*n - 2)
        if k == 0:
            if j == 0:
                return 1
            elif j < n - 1:
                return 2
            else:
                return 1
        else:
            if j < k:
                return 0
            elif j < n - 1:
                return 2
            else:
                return 1

def cycle_config(n, t):
    return tuple(cup2CycleVal(n, t, j) for j in range(n))

def good_cycle_configs(n):
    L = 3*n - 2
    return {cycle_config(n, t) for t in range(L)}

def delete_config(c, k):
    return tuple(c[j] if j < k else c[j+1] for j in range(len(c)-1))

# Counterexample check
n = 9
k = 4
c = (1,1,1,1,2,0,0,0,0)
dc = delete_config(c, k)

gc9 = good_cycle_configs(9)
gc8 = good_cycle_configs(8)

print(f"c = {c}")
print(f"dc = {dc}")
print(f"c in GC(9): {c in gc9}")
print(f"dc in GC(8): {dc in gc8}")

if c not in gc9 and dc in gc8:
    print(">>> COUNTEREXAMPLE FOUND! deleteConfig_bad_preserved is FALSE.")
else:
    print("Not a counterexample.")

# Systematic check: for all good cycle configs at n-1, check all possible preimages
print("\n--- Systematic sweep ---")
for n in range(8, 13):
    gcn = good_cycle_configs(n)
    gcnm1 = good_cycle_configs(n-1)
    for k in range(3, n-3):
        if k + 4 > n:
            continue
        violations = 0
        for dc_tuple in gcnm1:
            # Check if there exists c not in gcn with delete(c,k) = dc
            # c has n positions, c[j] = dc[j] for j < k, c[j] = dc[j-1] for j > k
            # c[k] is free
            for ck in range(3):  # modulus at deep position is 3
                c_list = list(dc_tuple[:k]) + [ck] + list(dc_tuple[k:])
                c_tuple = tuple(c_list)
                if c_tuple not in gcn and delete_config(c_tuple, k) == dc_tuple:
                    violations += 1
        if violations > 0:
            print(f"  n={n}, k={k}: {violations} violations (theorem FALSE)")
        else:
            print(f"  n={n}, k={k}: 0 violations (OK)")
