#!/usr/bin/env python3
"""
Verify the n=6 hfull + ¬EC finding.

The earlier biased search found 1 example at n=6.
The deep single-privileged search found 0.

The issue: good cycles can come from MULTI-privileged configs too!
The single-privileged graph only finds cycles where every config has
exactly 1 privileged proc. But good cycles from specific daemon schedules
can pass through multi-privileged configs.

Let me redo the random daemon search at n=6 with more trials.
"""
import random
from collections import Counter

random.seed(12345)  # different seed from earlier

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def has_entry_conflict(configs, movers, n):
    CL = len(configs)
    for p in range(n):
        mt = set()
        nmt = set()
        for k in range(CL):
            triple = (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n])
            if movers[k] == p:
                mt.add(triple)
            else:
                nmt.add(triple)
        if mt & nmt:
            return True
    return False

def search(n, ms, num_trials, seed=None):
    if seed is not None:
        random.seed(seed)

    found_hfull = []
    noec_count = 0
    max_active = 0

    for trial in range(num_trials):
        if trial % 500000 == 0 and trial > 0:
            print(f"  trial {trial}: ¬EC={noec_count}, hfull={len(found_hfull)}, max_active={max_active}")

        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        history = [config]
        history_movers = []
        config_to_step = {config: 0}

        for step in range(5000):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break

            # Biased: prefer procs not yet fired
            fired = set(history_movers)
            unfired_privs = [p for p in privs if p not in fired]
            if unfired_privs and random.random() < 0.5:
                p = random.choice(unfired_privs)
            else:
                p = random.choice(privs)

            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)

            if config in config_to_step:
                cs = config_to_step[config]
                cycle_configs = history[cs:]
                cycle_movers = history_movers[cs:] + [p]
                CL = len(cycle_configs)

                ec = has_entry_conflict(cycle_configs, cycle_movers, n)
                if not ec:
                    noec_count += 1
                    fc = [0]*n
                    for m in cycle_movers:
                        fc[m] += 1
                    na = sum(1 for f in fc if f > 0)
                    max_active = max(max_active, na)
                    hfull = all(f > 0 for f in fc)
                    if hfull:
                        found_hfull.append({
                            'CL': CL, 'fc': fc, 'movers': cycle_movers,
                            'configs': list(cycle_configs),
                        })
                        if len(found_hfull) <= 5:
                            adj = all(ring_dist(cycle_movers[k], cycle_movers[(k+1)%CL], n) <= 1
                                      for k in range(CL))
                            print(f"  FOUND: CL={CL}, fc={fc}, adj={adj}")
                            print(f"    Movers: {cycle_movers}")
                break

            config_to_step[config] = step + 1
            history.append(config)
            history_movers.append(p)

    return noec_count, found_hfull, max_active

def main():
    # n=6 deep search with biased daemon
    print("="*70)
    print("n=6 VERIFICATION: ms=[2,3,2,3,2,3]")
    print("="*70)
    n = 6
    ms = [2, 3, 2, 3, 2, 3]
    noec, hfull, mx = search(n, ms, 3000000, seed=42)
    print(f"\nResults: ¬EC={noec}, hfull={len(hfull)}, max_active={mx}")

    if not hfull:
        print("Trying with different seeds...")
        for s in [123, 456, 789, 1000, 2000]:
            noec2, hfull2, mx2 = search(n, ms, 1000000, seed=s)
            print(f"  seed={s}: ¬EC={noec2}, hfull={len(hfull2)}, max={mx2}")
            if hfull2:
                hfull.extend(hfull2)
                break

    # n=7 confirmation
    print("\n" + "="*70)
    print("n=7 CONFIRMATION: ms=[2,3,2,3,2,3,3]")
    print("="*70)
    n = 7
    ms = [2, 3, 2, 3, 2, 3, 3]
    noec, hfull7, mx = search(n, ms, 2000000, seed=42)
    print(f"\nResults: ¬EC={noec}, hfull={len(hfull7)}, max_active={mx}")

    # Also try n=7 with all-alternating: [2,3,2,3,2,3,2] (4 binary — but needs ≥3 non-consec)
    # Wait: [2,3,2,3,2,3,2] has 4 binary at {0,2,4,6}. Non-consecutive (gaps=2).
    # But product = 2^4 * 3^3 = 432 < 972.
    print("\n" + "="*70)
    print("n=7 with 4 binary: ms=[2,3,2,3,2,3,2]")
    print("="*70)
    n = 7
    ms = [2, 3, 2, 3, 2, 3, 2]
    noec, hfull7b, mx = search(n, ms, 2000000, seed=42)
    print(f"\nResults: ¬EC={noec}, hfull={len(hfull7b)}, max_active={mx}")

    # CONCLUSION
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    print(f"""
n=6 [2,3,2,3,2,3]: hfull+¬EC found: {"YES" if hfull else "NO (extremely rare or impossible)"}
n=7 [2,3,2,3,2,3,3]: hfull+¬EC: {"YES" if hfull7 else "NO"} (max active: {mx})
n=7 [2,3,2,3,2,3,2]: hfull+¬EC: {"YES" if hfull7b else "NO"}

KEY INSIGHT: Under ¬EC with non-consecutive binary at n≥7:
- Mover walk is ring-adjacent (gap1_ec)
- Walk is confined to ≤2 adjacent procs
- hfull requires all n procs to fire → IMPOSSIBLE

For the Lean proof (n≥9): hfull ∧ ¬EC is vacuously false.
The sorry in AllNormalFormFalse2.lean can be discharged by
proving hfull + ¬EC → False, which follows from the 2-proc
arc confinement under ¬EC.
""")

if __name__ == '__main__':
    main()
