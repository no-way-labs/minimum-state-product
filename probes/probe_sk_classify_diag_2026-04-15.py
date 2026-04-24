#!/usr/bin/env python3
"""Diagnose classifier: for a small sub-M_n multiset, dump actual
cycles found with lengths, movers, fire counts. Expected to see
length 2n sweeps; if we don't, the enumerator or fairness check is
off."""
from itertools import product as iproduct
from collections import Counter
import sys

sys.setrecursionlimit(20000)


def enumerate_all_cycles(ms, n, L_max, max_cycles=200):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(path)
            norm = min(tuple(path[i:] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles:
            break
        dfs(start, start, {}, [start], [])
    return found


def main():
    ms = (2, 2, 2, 2, 3)
    n = 5
    L_max = 14
    print(f"ms={ms}  n={n}  L_max={L_max}", flush=True)
    cycles = enumerate_all_cycles(ms, n, L_max, max_cycles=200)
    print(f"found {len(cycles)} cycles", flush=True)
    len_hist = Counter(len(c) for c, _, _ in cycles)
    print(f"length histogram: {dict(sorted(len_hist.items()))}", flush=True)
    for L in sorted(set(len(c) for c, _, _ in cycles)):
        exs = [(c, m) for c, m, _ in cycles if len(c) == L][:2]
        print(f"\n  --- L={L} ---", flush=True)
        for c, m in exs:
            fc = Counter(m)
            print(f"    movers={m} fc={dict(fc)} start={c[0]}", flush=True)


if __name__ == "__main__":
    main()
