def check_formula(pred):
    for n in range(4, 20):
        for k in range(3, n):
            for t in range(0, n):
                for j in range(0, n-1):
                    if not pred['branch'](n,k,t,j):
                        continue
                    lhs = 1 if ((j if j < k else j+1) < t) else 0
                    rhs = 1 if (j < (t if t <= k else t-1)) else 0
                    val = pred['formula'](n,k,t,j)
                    if lhs != rhs or lhs != val:
                        return (n,k,t,j,lhs,rhs,val)
    return None

cases = [
    ("t<=k, j<k => j<t", {
        'branch': lambda n,k,t,j: t <= k and j < k,
        'formula': lambda n,k,t,j: 1 if j < t else 0,
    }),
    ("t<=k, j>=k => 0", {
        'branch': lambda n,k,t,j: t <= k and not (j < k),
        'formula': lambda n,k,t,j: 0,
    }),
    ("t>k, j<k => j<t-1", {
        'branch': lambda n,k,t,j: not (t <= k) and j < k,
        'formula': lambda n,k,t,j: 1 if j < t-1 else 0,
    }),
    ("t>k, j>=k => 0", {
        'branch': lambda n,k,t,j: not (t <= k) and not (j < k),
        'formula': lambda n,k,t,j: 0,
    }),
]

for desc, pred in cases:
    bad = check_formula(pred)
    print(desc)
    print('OK' if bad is None else f'FAIL {bad}')
    print()
