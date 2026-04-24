#!/usr/bin/env python3
"""E12 extensions:
(a) n=6 full-axiom violator probe (verify A1' no-go generalizes).
(b) n=5 Nodup-relaxed variant: if violators appear only when Nodup removed,
    Nodup is the load-bearing axiom forcing A1'.
"""
from __future__ import annotations

import time
from itertools import product as iproduct


def enumerate_cycles(ms, n, L_max, tb, pinned, max_cycles, enforce_nodup=True):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time()-t0 > tb: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm); found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if enforce_nodup:
                    if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time()-t0 > tb: break
        dfs(start, start, dict(pinned), [start], [])
    return found


def audit(cyc, movers, n, p, L_val, R_val, S1, S2):
    L = len(movers); firings = []
    for k in range(L):
        if movers[k] != p: continue
        ck = cyc[k]
        if ck[(p-1)%n] == L_val and ck[(p+1)%n] == R_val:
            firings.append((k, ck[p]))
    s_vals = [s for (_, s) in firings]
    if S1 not in s_vals or S2 not in s_vals: return False
    targets = [(s, cyc[(k+1) % L][p]) for k, s in firings]
    t1 = [v for s, v in targets if s == S1]
    t2 = [v for s, v in targets if s == S2]
    return bool(t1) and bool(t2) and t1[0] == t2[0]


def run_trials(label, trials, enforce_nodup):
    print(f"\n{'='*72}")
    print(f"  {label}  (enforce_nodup={enforce_nodup})")
    print(f"{'='*72}")
    total_attempts = 0; total_violators = 0; violator_examples = []
    t0 = time.time()
    for n, ms, L_max, tb in trials:
        print(f"\n  --- n={n}, ms={ms} ---", flush=True)
        for p in range(n):
            if ms[p] < 3: continue
            for L_val in range(ms[(p-1)%n]):
                for R_val in range(ms[(p+1)%n]):
                    for S1 in range(ms[p]):
                        for S2 in range(S1+1, ms[p]):
                            for v in range(ms[p]):
                                if v == S1 or v == S2: continue
                                pinned = {
                                    (p, L_val, S1, R_val): v,
                                    (p, L_val, S2, R_val): v,
                                }
                                total_attempts += 1
                                if time.time() - t0 > 200: return total_attempts, total_violators, violator_examples
                                cycles = enumerate_cycles(ms, n, L_max, tb, pinned, 3, enforce_nodup)
                                for cyc, movers, det in cycles:
                                    if len(movers) < 2*n: continue
                                    if audit(cyc, movers, n, p, L_val, R_val, S1, S2):
                                        total_violators += 1
                                        if len(violator_examples) < 3:
                                            violator_examples.append({
                                                'n': n, 'ms': ms, 'p': p,
                                                'L': L_val, 'R': R_val,
                                                'S1': S1, 'S2': S2, 'v': v,
                                                'cycle': cyc, 'movers': movers,
                                            })
                                        break  # one violator per pinned-det is enough
    return total_attempts, total_violators, violator_examples


if __name__ == "__main__":
    print("=" * 72)
    print("E12 extensions: n=6 verify + n=5 Nodup-relax diagnostic")
    print("=" * 72)

    # (a) n=6 full-axiom — verify no violators at n=6
    trials_n6 = [
        (6, (3, 3, 3, 3, 3, 3), 18, 4.0),
        (6, (2, 3, 3, 3, 3, 3), 18, 4.0),
    ]
    a_att, a_viol, a_ex = run_trials("(a) n=6 full-axiom", trials_n6, True)
    print(f"\n  (a) attempts={a_att}  violators={a_viol}")

    # (b) n=5 Nodup-relaxed — if violators appear, Nodup is load-bearing
    trials_n5 = [
        (5, (3, 3, 3, 3, 3), 15, 3.0),
        (5, (2, 3, 3, 3, 3), 15, 3.0),
    ]
    b_att, b_viol, b_ex = run_trials("(b) n=5 Nodup-RELAXED", trials_n5, False)
    print(f"\n  (b) attempts={b_att}  violators={b_viol}")
    for ex in b_ex[:2]:
        print(f"    VIOLATOR EX: p={ex['p']} (L,R)=({ex['L']},{ex['R']}) "
              f"S1={ex['S1']} S2={ex['S2']} v={ex['v']}")
        print(f"      cycle: {ex['cycle']}")
        print(f"      movers: {ex['movers']}")

    print(f"\n{'='*72}")
    print("VERDICT")
    print(f"{'='*72}")
    if a_viol == 0:
        print(f"  (a) n=6 full-axiom: 0 violators / {a_att} attempts")
        print("      A1' no-go EXTENDS to n=6.")
    else:
        print(f"  (a) n=6 full-axiom: {a_viol} violators found — A1' is NOT universal at n=6.")
    if b_viol == 0:
        print(f"  (b) n=5 Nodup-relaxed: 0 violators / {b_att} attempts")
        print("      Nodup is NOT load-bearing; something else forces A1'.")
    else:
        print(f"  (b) n=5 Nodup-relaxed: {b_viol} violators found")
        print("      Nodup IS load-bearing for A1'. Proof must use Nodup.")
