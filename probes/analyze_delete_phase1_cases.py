from collections import defaultdict

def lhs(j,k,t):
    x = j if j < k else j + 1
    return 1 if x < t else 0

def rhs(n,j,k,t):
    # phase1: t < n
    if t <= k:
        tp = t
    else:
        tp = t - 1
    return 1 if j < tp else 0

# gather branch descriptions
for case_htk in [True, False]:
    for case_hjk in [True, False]:
        mismatches = []
        witnesses_true = []
        for n in range(4, 15):
            for k in range(0, n):
                for t in range(0, n):
                    if case_htk != (t <= k):
                        continue
                    for j in range(0, max(0,n-1)):
                        if case_hjk != (j < k):
                            continue
                        l = lhs(j,k,t)
                        r = rhs(n,j,k,t)
                        if l != r:
                            mismatches.append((n,k,t,j,l,r))
                            if len(mismatches) >= 5:
                                break
                    if len(mismatches) >= 5:
                        break
                if len(mismatches) >= 5:
                    break
            if len(mismatches) >= 5:
                break
        print(f"case t<=k={case_htk}, j<k={case_hjk}")
        if mismatches:
            print('mismatches:', mismatches[:5])
        else:
            print('no mismatches')
        print()
