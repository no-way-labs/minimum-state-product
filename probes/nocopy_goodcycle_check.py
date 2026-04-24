"""Check: does every good cycle config have a deep copy pair?
   If yes, noDeepCopyPair implies not in good cycle.
"""

def cup2CycleVal(n, t, j):
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

def has_deep_copy_pair(n, config):
    """Check if config has a copy pair at some deep position k (4 <= k, k+4 <= n)."""
    for k in range(4, n - 3):
        if config[k] == config[k-1] or config[k] == config[k+1]:
            return True
    return False

for n in range(8, 16):
    L = 3*n - 2
    all_have_copy = True
    counterexamples = []
    for t in range(L):
        config = tuple(cup2CycleVal(n, t, j) for j in range(n))
        if not has_deep_copy_pair(n, config):
            all_have_copy = False
            counterexamples.append((t, config))
    if all_have_copy:
        print(f"n={n}: ALL {L} good cycle configs have a deep copy pair")
    else:
        print(f"n={n}: {len(counterexamples)} configs WITHOUT deep copy pair:")
        for t, c in counterexamples[:5]:
            print(f"  t={t}: {c}")
