#!/usr/bin/env python3
"""
WHY does ¬EC limit the mover walk to at most 2 active processors for n≥7?

HYPOTHESIS: Under ¬EC, the ring-adjacent walk is confined to a short arc.
The walk cannot "pass through" a binary processor and continue.

Structural argument:
When the mover walk reaches a binary proc p, it must eventually leave.
"Leaving" means the next mover is left(p) or right(p).
When the mover moves FROM p TO a neighbor q, the config changes at p,
and the triple at p becomes a non-mover triple.

KEY INSIGHT: At a binary proc, the triple space is small. After the
walk visits p twice (minimum for hfull), the "used up" triples may
prevent the walk from passing through p again. More importantly,
the walk being ring-adjacent means it must pass through p to go from
one side of the ring to the other.

Let me verify this with detailed analysis of what happens when the
mover walk tries to traverse past a binary proc.

REFINED ANALYSIS:
The walk is on the ring. Binary procs at non-consecutive positions
partition the ring into "arcs" between binary procs. To visit all
procs, the walk must cross at least 2 binary procs.

When the walk crosses a binary proc p (entering from left, exiting right):
- Step k-1: mover = left(p), then step k: mover = p, then step k+1: mover = right(p).
- At step k: p fires. Triple (L, v, R) at p is a mover triple.
- At step k-1: mover is left(p). Triple at p is non-mover: (L', v, R) where
  L' may differ from L (since left(p) just changed).
  Actually at step k-1, left(p) fires, changing L. So BEFORE step k-1,
  triple at p is (L_old, v, R). After step k-1, triple is (L_new, v, R).
  Step k: mover = p. Triple at p is (L_new, v, R) — this is the mover triple.
  BUT step k-1's non-mover triple at p is (L_old, v, R) (the triple BEFORE
  the step, which is what the step sees as its config).

Wait, I need to be precise about timing.

In a good cycle: configs[0], configs[1], ..., configs[CL-1].
At step k: mover = movers[k]. The CONFIG at step k is configs[k].
The mover changes configs[k] to configs[(k+1)%CL].

Entry conflict at p: exists k (mover) and k' (non-mover) such that
the BOUNDARY TRIPLE at p in configs[k] equals that in configs[k'].

So the triple at p at step k is: (configs[k][left(p)], configs[k][p], configs[k][right(p)]).

When movers[k-1] = left(p) and movers[k] = p:
- configs[k][left(p)] = new value of left(p) after it fired at step k-1.
- configs[k][p] = same as configs[k-1][p] (p didn't fire at step k-1).

So the mover triple at p for step k: (configs[k][left(p)], configs[k][p], configs[k][right(p)]).
This triple must not appear as a non-mover triple at p at any other step.

Now I want to check: if the walk goes left(p) → p → right(p),
how constrained are the triples?

Let me just empirically look at the ¬EC cycles that DO have 2 active procs
and see what the walk looks like.
"""
import random
from collections import Counter

random.seed(42)

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

def search_and_analyze(n, ms, num_trials=300000):
    """Find ¬EC cycles and analyze the ones with max active procs."""
    max_active = 0
    best_examples = []

    for trial in range(num_trials):
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

        for step in range(3000):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break
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
                    fc = [0]*n
                    for m in cycle_movers:
                        fc[m] += 1
                    active = [i for i in range(n) if fc[i] > 0]
                    na = len(active)
                    if na > max_active:
                        max_active = na
                        best_examples = []
                    if na == max_active and len(best_examples) < 20:
                        best_examples.append({
                            'CL': CL,
                            'fc': fc,
                            'active': active,
                            'movers': cycle_movers,
                            'configs': cycle_configs,
                            'sys_f': sys_f,
                        })
                break

            config_to_step[config] = step + 1
            history.append(config)
            history_movers.append(p)

    return max_active, best_examples

def analyze_crossing(example, n, ms):
    """Analyze if/how the mover walk crosses binary procs."""
    movers = example['movers']
    configs = example['configs']
    CL = len(movers)
    fc = example['fc']
    active = example['active']

    binary_pos = [i for i in range(n) if ms[i] == 2]

    print(f"  CL={CL}, active={active}, fc={fc}")
    print(f"  Binary procs: {binary_pos}")
    print(f"  Mover sequence: {movers}")

    # Check if any binary proc is in the active set
    active_binary = [p for p in active if ms[p] == 2]
    active_ternary = [p for p in active if ms[p] >= 3]
    print(f"  Active binary: {active_binary}, active ternary: {active_ternary}")

    # Show boundary triples at each active proc
    for p in active:
        mover_triples = []
        nonmover_triples = []
        for k in range(CL):
            triple = (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n])
            if movers[k] == p:
                mover_triples.append((k, triple))
            else:
                nonmover_triples.append((k, triple))
        print(f"  P{p} (m={ms[p]}): mover triples = {[t for _,t in mover_triples]}")
        print(f"    Non-mover triple set: {set(t for _,t in nonmover_triples)}")
        print(f"    Disjoint: {not (set(t for _,t in mover_triples) & set(t for _,t in nonmover_triples))}")

    # Walk direction analysis
    dirs = []
    for k in range(CL):
        m_now = movers[k]
        m_next = movers[(k+1)%CL]
        d = (m_next - m_now) % n
        if d == 0:
            dirs.append('STAY')
        elif d == 1:
            dirs.append('CW')
        elif d == n-1:
            dirs.append('CCW')
        else:
            dirs.append(f'JUMP({d})')
    print(f"  Walk directions: {dirs}")

def main():
    print("ARC BOUND ANALYSIS: Why ¬EC limits active procs")
    print("="*70)

    # First, let's check n=5 with NON-CONSECUTIVE binary (if possible)
    # At n=5 with 3 non-consecutive binary: impossible (n=5, ≥3 binary,
    # non-consecutive means gaps ≥2 between each pair, 3*2=6 > 5).
    # So n=5 with 3 binary is always consecutive.

    # n=6 with 3 non-consecutive binary: [2,3,2,3,2,3] — gaps = 2 each.
    # Let's check n=6!
    print("\n--- n=6, first non-consecutive case ---")
    n = 6
    ms = [2, 3, 2, 3, 2, 3]
    max_a, examples = search_and_analyze(n, ms, num_trials=500000)
    print(f"Max active procs: {max_a}")
    for ex in examples[:5]:
        analyze_crossing(ex, n, ms)

    # n=7
    print("\n--- n=7, non-consecutive binary ---")
    n = 7
    ms = [2, 3, 2, 3, 2, 3, 3]
    max_a, examples = search_and_analyze(n, ms, num_trials=500000)
    print(f"Max active procs: {max_a}")
    for ex in examples[:5]:
        analyze_crossing(ex, n, ms)

    # n=9
    print("\n--- n=9, non-consecutive binary ---")
    n = 9
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
    max_a, examples = search_and_analyze(n, ms, num_trials=500000)
    print(f"Max active procs: {max_a}")
    for ex in examples[:5]:
        analyze_crossing(ex, n, ms)

    # KEY QUESTION: What about n=5 with consecutive binary?
    # There hfull WAS found. The walk crossed all 5 procs.
    # The difference: consecutive binary = binary procs are adjacent.
    # The walk can go through consecutive binary procs easily.
    # Non-consecutive binary = binary procs are separated by ternary.
    # The walk must cross a binary proc to get from one arc to another.
    # But crossing seems impossible for ¬EC.

    # Let's check: do any ¬EC cycles have a binary proc in the active set
    # at n=7+ with non-consecutive binary?
    print("\n\n--- BINARY PROC ACTIVITY CHECK ---")
    for n, ms in [(7, [2,3,2,3,2,3,3]), (9, [2,3,2,3,2,3,3,3,3])]:
        binary_pos = [i for i in range(n) if ms[i] == 2]
        max_a, examples = search_and_analyze(n, ms, num_trials=300000)
        binary_active = sum(1 for ex in examples if any(ms[p]==2 for p in ex['active']))
        total = len(examples)
        print(f"n={n}: max_active={max_a}, examples with active binary: {binary_active}/{total}")
        for ex in examples[:3]:
            print(f"  active={ex['active']}, types={[ms[p] for p in ex['active']]}")

if __name__ == '__main__':
    main()
