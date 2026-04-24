#!/usr/bin/env python3
"""
At n=9, find all-adjacent cycles and identify WHERE the EC comes from.
This tells us what construction closes the sorry.
"""
import random
from collections import defaultdict

random.seed(42)

def find_alladj_cycles_with_ec(n, ms, num_trials=5000000):
    results = []
    stats = defaultdict(int)

    for trial in range(num_trials):
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L,S,R)] = random.randint(0, ms[i]-1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        history = [config]; hm = []; cs_map = {config: 0}

        for step in range(5000):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n],config[i],config[(i+1)%n])]!=config[i]]
            if not privs: break
            p = random.choice(privs)
            nc = list(config); nc[p] = sys_f[p][(config[(p-1)%n],config[p],config[(p+1)%n])]
            config = tuple(nc)
            if config in cs_map:
                cs = cs_map[config]
                cc = history[cs:]; cm = hm[cs:] + [p]; CL = len(cc)
                if CL >= n:
                    aa = all(min((cm[k]-cm[(k+1)%CL])%n,(cm[(k+1)%CL]-cm[k])%n)<=1 for k in range(CL))
                    if aa:
                        stats['all_adj'] += 1
                        # Find EC source
                        for p2 in range(n):
                            mt_set = {}
                            nmt_set = {}
                            for k in range(CL):
                                tr = (cc[k][(p2-1)%n], cc[k][p2], cc[k][(p2+1)%n])
                                if cm[k] == p2:
                                    mt_set[tr] = mt_set.get(tr, []) + [k]
                                else:
                                    nmt_set[tr] = nmt_set.get(tr, []) + [k]
                            overlap = set(mt_set.keys()) & set(nmt_set.keys())
                            if overlap:
                                for tr in overlap:
                                    results.append({
                                        'proc': p2, 'triple': tr,
                                        'mover_steps': mt_set[tr],
                                        'nonmover_steps': nmt_set[tr],
                                        'movers': cm, 'configs': cc,
                                    })
                                    stats[f'ec_at_{p2}'] += 1
                                break  # one EC per cycle is enough

                        if len(results) >= 50:
                            return stats, results
                break
            history.append(config); hm.append(p); cs_map[config] = step+1

        if trial % 1000000 == 999999:
            print(f"  Trial {trial+1}: {dict(stats)}")

    return stats, results


def main():
    n = 9
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]

    print(f"n={n}, ms={ms}")
    print("Finding all-adjacent cycles with EC source identification...")

    stats, results = find_alladj_cycles_with_ec(n, ms, num_trials=10000000)
    print(f"\nStats: {dict(stats)}")
    print(f"EC examples: {len(results)}")

    if results:
        print("\nEC source analysis:")
        proc_counts = defaultdict(int)
        for r in results:
            proc_counts[r['proc']] += 1
        for p in sorted(proc_counts):
            print(f"  Proc {p} (m={ms[p]}): {proc_counts[p]} times")

        print("\nDetailed examples:")
        for i, r in enumerate(results[:10]):
            p = r['proc']
            CL = len(r['movers'])
            ms_step = r['mover_steps'][0]
            nms_step = r['nonmover_steps'][0]
            print(f"\n  Example {i+1}: EC at proc {p} (m={ms[p]})")
            print(f"    Cycle len: {CL}")
            print(f"    Movers: {r['movers']}")
            print(f"    Mover step {ms_step}: mover={r['movers'][ms_step]}, triple={r['triple']}")
            print(f"    Non-mover step {nms_step}: mover={r['movers'][nms_step]}, triple={r['triple']}")

            # Check if the EC is at a binary processor
            if ms[p] == 2:
                print(f"    ** EC at BINARY processor {p} **")

            # Check relationship to t=1
            t = 1
            if p == t:
                print(f"    ** EC at t={t} itself **")
            elif p == (t-1)%n:
                print(f"    ** EC at left(t) **")
            elif p == (t+1)%n:
                print(f"    ** EC at right(t) **")
            elif p == (t-2)%n:
                print(f"    ** EC at left²(t) **")
            elif p == (t+2)%n:
                print(f"    ** EC at right²(t) **")

    # Also check: which construction COULD have found this EC?
    # gap1_ec: already ruled out (all-adjacent)
    # mk_ec_left/right: boundary triple match at L or R between mover and non-mover
    # ec_caseC: cross-neighbor pair


if __name__ == '__main__':
    main()
