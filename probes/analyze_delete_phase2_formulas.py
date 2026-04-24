
def delete_cycle_time(n,k,t):
    if t <= k:
        return t
    elif t < 2*n - 2:
        if t <= 2*n - k - 2:
            return t - 1
        else:
            return t - 2
    elif t <= 2*n + k - 2:
        return t - 2
    else:
        return t - 3

def cup2_phase2(n,t,j):
    return 1 if j < 2*n - 1 - t else (2 if j < n - 1 else 1)

def rhs(n,k,t,j):
    tp = delete_cycle_time(n,k,t)
    n1 = n - 1
    return 1 if j < 2*n1 - 1 - tp else (2 if j < n1 - 1 else 1)

cases = [
    ("ht3, j<k", lambda n,k,t,j: t > k and t <= 2*n-k-2 and j < k),
    ("ht3, j>=k", lambda n,k,t,j: t > k and t <= 2*n-k-2 and not (j < k)),
    ("!ht3, j<k", lambda n,k,t,j: t > 2*n-k-2 and t < 2*n-2 and j < k),
    ("!ht3, j>=k", lambda n,k,t,j: t > 2*n-k-2 and t < 2*n-2 and not (j < k)),
]

for name, pred in cases:
    mismatches = []
    for n in range(8, 20):
        for k in range(3, n-3):
            for t in range(n, 2*n-2):
                for j in range(0, n-1):
                    if not pred(n,k,t,j):
                        continue
                    x = j if j < k else j + 1
                    lhs = cup2_phase2(n,t,x)
                    rr = rhs(n,k,t,j)
                    if lhs != rr:
                        mismatches.append((n,k,t,j,lhs,rr))
                        if len(mismatches) >= 5:
                            break
                if len(mismatches) >= 5:
                    break
            if len(mismatches) >= 5:
                break
        if len(mismatches) >= 5:
            break
    print(name)
    print('OK' if not mismatches else f'FAIL {mismatches}')
    print()
