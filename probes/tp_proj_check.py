"""Verify BitVal condition matching at projected positions."""

def check(n, k, p):
    assert 3 <= k and k + 4 <= n and p != k and p != k-1 and p != k+1
    projP = p if p < k else p - 1
    left_projP = (n - 2) if projP == 0 else (projP - 1)
    left_p = (n - 1) if p == 0 else (p - 1)
    # Self position
    cond_self_new = (2 <= projP) and (projP + 2 < n - 1)
    cond_self_old = (2 <= p) and (p + 2 < n)
    if cond_self_new != cond_self_old:
        print(f'MISMATCH self: n={n}, k={k}, p={p}, projP={projP}')
        return False
    # Left position
    cond_left_new = (2 <= left_projP) and (left_projP + 2 < n - 1)
    cond_left_old = (2 <= left_p) and (left_p + 2 < n)
    if cond_left_new != cond_left_old:
        print(f'MISMATCH left: n={n}, k={k}, p={p}, L_proj={left_projP}, L_orig={left_p}')
        return False
    return True

count = mm = 0
for n in range(8, 25):
    for k in range(3, n - 3):
        if k + 4 > n:
            continue
        for p in range(n):
            if p in (k-1, k, k+1):
                continue
            count += 1
            if not check(n, k, p):
                mm += 1
print(f'Checked {count} cases, {mm} mismatches')

# Also check the Weight shift formula
print("\nWeight shift check:")
for n in range(8, 15):
    for k in range(3, n - 3):
        if k + 4 > n:
            continue
        for p in range(n):
            if p in (k-1, k, k+1):
                continue
            projP = p if p < k else p - 1
            left_projP = (n - 2) if projP == 0 else (projP - 1)
            left_p = (n - 1) if p == 0 else (p - 1)
            # Weight shift: localWeight(n-1) = localWeight(n) - localCount(n)
            # for p > k: multipliers are (left_projP, projP) = (p-2, p-1) vs (p-1, p)
            # shift = -(bit_left + bit_self) = -localCount
            if p > k:
                assert left_projP == p - 2 and projP == p - 1
                assert left_p == p - 1
                # weight_new = (p-2)*bit_L + (p-1)*bit_S
                # weight_old = (p-1)*bit_L + p*bit_S
                # diff = -bit_L - bit_S = -count_local
            elif p < k:
                assert projP == p
                if p > 0:
                    assert left_projP == p - 1 == left_p
                # weight matches directly
print("Weight shift verified conceptually")
