#!/usr/bin/env python3
"""THE DECISIVE TEST:
Can we find ANY good cycle satisfying ALL of:
  sub-threshold + ≥3 binary + n≥9 + converges + hno_safe?

If NO: the branch is unreachable. Prove safe proc always exists.
If YES: check if it forces alternating ring / pivot / etc.

Also test at n=5,7 for comparison.
"""
import random

def random_transition(m_left, m_self, m_right):
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f

def privileged(config, sys_f, ms, n, i):
    return sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]

def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    return privs[0] if len(privs) == 1 else None

def apply_move(config, sys_f, ms, n, i):
    nc = list(config)
    nc[i] = sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])]
    return tuple(nc)

def has_safe_proc(movers, n):
    fc = [0] * n
    for m in movers:
        fc[m] += 1
    for q in range(n):
        if fc[q] == 0 and fc[(q-1)%n] == 0 and fc[(q+1)%n] == 0:
            return True
    return False

def check_hno_safe(movers, n):
    for q in range(n):
        if not any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers):
            return False
    return True

def main():
    random.seed(42)

    configs = [
        # Sub-threshold with ≥3 binary
        (5, [2,2,2,3,3]),      # product 72 < 108
        (5, [2,2,2,3,4]),      # product 96 < 108
        (7, [2,2,2,3,3,3,3]),  # product 648 < 972
        (9, [2,2,2,3,3,3,3,3,3]),  # product 5832 < 8748
        (9, [2,3,2,3,3,3,3,3,3]),  # product 8748 = threshold (not sub)
        (9, [2,2,3,2,3,3,3,3,3]),  # product 5832 < 8748
        # Also: ALL ternary (0 binary) — for comparison
        (5, [3,3,3,3,3]),
        (9, [3,3,3,3,3,3,3,3,3]),
    ]

    for n, ms in configs:
        product = 1
        for m in ms:
            product *= m
        num_bin = sum(1 for m in ms if m == 2)
        threshold = 4 * (3 ** (n - 2))
        is_sub = product < threshold

        safe_count = 0
        nosafe_count = 0
        total = 0

        for trial in range(1000000 if n <= 7 else 200000):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            visited = {}
            for step in range(3000):
                if config in visited:
                    start = visited[config]
                    cycle = []
                    c = config
                    ok = True
                    for _ in range(step - start):
                        p = find_unique_privileged(c, sys_f, ms, n)
                        if p is None: ok = False; break
                        cycle.append(p)
                        c = apply_move(c, sys_f, ms, n, p)
                    if ok and cycle:
                        total += 1
                        movers = cycle
                        safe = has_safe_proc(movers, n)
                        nosafe = check_hno_safe(movers, n)
                        if safe:
                            safe_count += 1
                        if nosafe:
                            nosafe_count += 1
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

        print(f"n={n} ms={ms} prod={product} sub={is_sub} bin={num_bin}: "
              f"{total} cycles, {safe_count} safe ({safe_count*100//max(total,1)}%), "
              f"{nosafe_count} hno_safe ({nosafe_count*100//max(total,1)}%)")

    print()
    print("=== CONCLUSION ===")
    print("If hno_safe = 0 for ALL sub-threshold configs with ≥3 binary:")
    print("  → The sorry branch is UNREACHABLE")
    print("  → Prove: sub-threshold + ≥3 binary + n≥5 → safe proc exists")
    print()
    print("If hno_safe > 0 for some config:")
    print("  → The sorry branch IS reachable")
    print("  → Need the paper's proof (Ring Alternation etc)")

if __name__ == '__main__':
    main()
