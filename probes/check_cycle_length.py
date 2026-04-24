#!/usr/bin/env python3
"""Check cycle lengths for sub-threshold systems with ≥3 binary."""
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

def main():
    random.seed(42)
    for n, ms in [(5, [2,2,2,3,3]), (7, [2,2,2,3,3,3,3]),
                  (9, [2,2,2,3,3,3,3,3,3])]:
        lengths = []
        for trial in range(500000 if n <= 7 else 100000):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            visited = {}
            for step in range(3000):
                if config in visited:
                    start = visited[config]
                    L = step - start
                    # Verify it's a valid good cycle
                    c = config
                    ok = True
                    for _ in range(L):
                        p = find_unique_privileged(c, sys_f, ms, n)
                        if p is None: ok = False; break
                        c = apply_move(c, sys_f, ms, n, p)
                    if ok: lengths.append(L)
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

        if lengths:
            print(f"n={n} ms={ms}: {len(lengths)} cycles")
            print(f"  L: min={min(lengths)} max={max(lengths)} avg={sum(lengths)/len(lengths):.1f}")
            from collections import Counter
            dist = Counter(lengths)
            print(f"  distribution: {dict(sorted(dist.items())[:20])}")
            print()

if __name__ == '__main__':
    main()
