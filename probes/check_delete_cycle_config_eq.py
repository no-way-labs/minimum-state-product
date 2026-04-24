#!/usr/bin/env python3
"""
Check the mathematical claim of `deleteConfig_cycleConfig_eq` on small n.

For n in {9,10,11}, and all admissible deep deletion sites k, compare:

  deleteConfig(cycle_config(n, t), k)

against

  cycle_config(n-1, deleteCycleTime(n, k, t))

for every cycle time t.
"""


def cup2CycleLen(n):
    return 3 * n - 2


def cup2CycleVal(n, t, j):
    if t < n:
        return 1 if j < t else 0
    if t < 2 * n - 2:
        if j < 2 * n - 1 - t:
            return 1
        if j < n - 1:
            return 2
        return 1
    if t == 2 * n - 2:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    k = t - (2 * n - 2)
    if k == 0:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    if j < k:
        return 0
    if j < n - 1:
        return 2
    return 1


def cycle_config(n, t):
    return tuple(cup2CycleVal(n, t, j) for j in range(n))


def delete_config(c, k):
    return tuple(c[j] if j < k else c[j + 1] for j in range(len(c) - 1))


def deleteCycleTime(n, k, t):
    if t <= k:
        return t
    if t < 2 * n - 2:
        if t <= 2 * n - k - 2:
            return t - 1
        return t - 2
    if t <= 2 * n + k - 2:
        return t - 2
    return t - 3


def check_n(n):
    print(f"n={n}")
    failures = []
    ks = [k for k in range(3, n) if 3 <= k and k + 4 <= n]
    for k in ks:
        total = 0
        for t in range(cup2CycleLen(n)):
            lhs = delete_config(cycle_config(n, t), k)
            t2 = deleteCycleTime(n, k, t)
            rhs = cycle_config(n - 1, t2)
            total += 1
            if lhs != rhs:
                failures.append((k, t, t2, lhs, rhs))
                if len(failures) >= 10:
                    break
        print(f"  k={k}: checked {total}, failures={sum(1 for x in failures if x[0]==k)}")
    if not failures:
        print("  ALL CHECKS PASSED\n")
    else:
        print("  SAMPLE FAILURES:")
        for k, t, t2, lhs, rhs in failures[:10]:
            print(f"    k={k} t={t} t'={t2}")
            print(f"      lhs={lhs}")
            print(f"      rhs={rhs}")
        print()


def main():
    for n in (9, 10, 11):
        check_n(n)


if __name__ == "__main__":
    main()
