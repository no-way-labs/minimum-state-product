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

def cup2_phase3(n,t,j):
    m = t - (2*n - 2)
    if m == 0:
        return 1 if j == 0 else (2 if j < n-1 else 1)
    return 0 if j < m else (2 if j < n-1 else 1)

def lhs(n,k,t,j):
    x = j if j < k else j+1
    return cup2_phase3(n,t,x)

def rhs(n,k,t,j):
    tp = delete_cycle_time(n,k,t)
    return cup2_phase3(n-1,tp,j)

cases = [
    ("m<=k, j<k", lambda n,k,t,j: t > 2*n-2 and t <= 2*n+k-2 and j < k,
        lambda n,k,t,j: 0 if j < t-(2*n-2) else 2),
    ("m<=k, j>=k", lambda n,k,t,j: t > 2*n-2 and t <= 2*n+k-2 and not (j < k),
        lambda n,k,t,j: 0 if j < t-(2*n-2) else (2 if j < n-2 else 1)),
    ("m>k, j<k", lambda n,k,t,j: t > 2*n+k-2 and j < k,
        lambda n,k,t,j: 0),
    ("m>k, j>=k", lambda n,k,t,j: t > 2*n+k-2 and j >= k,
        lambda n,k,t,j: 0 if j < t-(2*n-2)-1 else (2 if j < n-2 else 1)),
]

for name, branch, formula in cases:
    bad = None
    for n in range(8,20):
        for k in range(3,n-3):
            cyclelen = 3*n-2
            for t in range(2*n-1, cyclelen):
                for j in range(0,n-1):
                    if not branch(n,k,t,j):
                        continue
                    l = lhs(n,k,t,j)
                    r = rhs(n,k,t,j)
                    f = formula(n,k,t,j)
                    if l != r or l != f:
                        bad = (n,k,t,j,l,r,f)
                        break
                if bad: break
            if bad: break
        if bad: break
    print(name)
    print('OK' if bad is None else f'FAIL {bad}')
    print()
