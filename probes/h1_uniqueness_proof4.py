"""
Analyze the counterexamples to understand when H-1 Uniqueness fails.

Key observation from counterexamples:
- ms=[2,3,4], CL=4: cycle (0,0,0)->(0,0,1)->(0,0,3)->(0,0,2)->...
  Only proc 2 fires. It's a single-proc cycle! g_0=(0,0,0) and g_2=(0,0,3) differ at p=2.
  The cycle visits values 0->1->3->2->0 at proc 2. Between j=0 and k=2,
  proc 2 fires twice: 0->1->3. Since no other proc fires, everything else stays fixed.

- ms=[2,2,2,3], CL=5: movers are [0,3,0,3,3].
  g_0=(0,0,0,0) and g_3=(0,0,0,2): differ at p=3, dist=2.
  Between j=0 and k=3: movers 0,3,0. Only procs 0 and 3 fire.
  Proc 0: fires at j=0 (0->1) and j=2 (1->0). Returns to 0!
  Proc 3: fires at j=1 (0->2). Changes from 0 to 2.
  So after 3 steps: proc 0 returns, proc 3 changes. Hamming-1 at p=3.

The "return" property: for procs q != p, the total effect of firings between
j and k must be ZERO (return to original value). This CAN happen with short
distances when some procs fire an even number of times.

Key question: does this happen in SWEEP cycles? In a sweep, each proc fires
exactly once in sequence. No proc returns to its original value mid-sweep.

Let me check: in the failing systems, is the mover word a sweep?
"""
from itertools import product as iprod
import random

def get_good_cycle(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        privs = []
        for p in range(n):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            if tables[p][(L,S,R)] != S:
                privs.append(p)
        if len(privs) == 1:
            good[config] = privs[0]
    if not good: return None, None
    start = next(iter(good))
    cycle = [start]; movers = [good[start]]; cur = start
    for _ in range(100000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None, None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None, None
    return cycle, movers

def is_sweep(movers, n):
    """Check if mover word is a sweep (each proc fires once per sweep period)."""
    CL = len(movers)
    # fire count of each proc
    fc = [0]*n
    for m in movers:
        fc[m] += 1
    # In a sweep, fc[p] = m_p for all p. But we just check if all distinct in a contiguous block.
    # Actually "sweep" means the mover visits each proc in sequence.
    # Let's check if the mover word is a permutation repeated.
    return False  # placeholder

def analyze_violations(ms, max_systems=100000):
    n = len(ms)
    random.seed(42)
    found = 0
    sweep_violations = 0
    nonsweep_violations = 0

    for trial in range(max_systems):
        tables = []
        for p in range(n):
            t = {}
            mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms, tables)
        if not cycle or len(cycle) <= 2:
            continue
        found += 1
        CL = len(cycle)

        # Check for violations
        has_violation = False
        for j in range(CL):
            for k in range(j+1, CL):
                diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
                if len(diff) == 1:
                    cdist = min(k-j, CL-(k-j))
                    if cdist != 1:
                        has_violation = True
                        break
            if has_violation:
                break

        if has_violation:
            # Analyze mover word: is it a sweep?
            # fire counts
            fc = [0]*n
            for m in movers:
                fc[m] += 1
            # Check: does each proc fire m_p times?
            fc_match = all(fc[p] == ms[p] for p in range(n))
            # Check: is the mover word a uniform sweep (each proc appears in consecutive blocks)?
            # Actually for the LB proof context: "sweep" = uniform sweep where mover visits
            # 0,1,...,n-1,n-1,...,1,0 or similar pattern

            # Simple check: is CL = sum(m_p)?
            expected_CL = sum(ms)
            is_minimal = (CL == expected_CL)

            # Check if fire count matches
            if not fc_match:
                nonsweep_violations += 1
            else:
                sweep_violations += 1
                print(f"  SWEEP-type violation! CL={CL}, movers={movers}, fc={fc}, ms={ms}")
                for i in range(CL):
                    print(f"    [{i}] {cycle[i]} mover={movers[i]}")

    return found, sweep_violations, nonsweep_violations


print("=== Analyzing violations ===")
for ms in [[2,3,4], [2,2,2,3], [2,3,3,3], [3,3,3,3], [2,2,3,3], [2,3,3], [2,2,3]]:
    found, sweep_v, nonsweep_v = analyze_violations(ms, 50000)
    print(f"ms={ms}: {found} valid, sweep_violations={sweep_v}, nonsweep_violations={nonsweep_v}")

# Now focus: for systems where fc[p]=m_p for all p (minimal good cycle),
# are there violations?
print("\n=== Minimal cycle check ===")
def check_minimal_violations(ms, max_systems=100000):
    """Only check systems where good cycle has CL = sum(ms)."""
    n = len(ms)
    random.seed(42)
    expected_CL = sum(ms)
    found_minimal = 0
    violations = 0

    for trial in range(max_systems):
        tables = []
        for p in range(n):
            t = {}
            mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms, tables)
        if not cycle: continue
        CL = len(cycle)

        fc = [0]*n
        for m in movers:
            fc[m] += 1
        if not all(fc[p] == ms[p] for p in range(n)):
            continue

        found_minimal += 1

        for j in range(CL):
            for k in range(j+1, CL):
                diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
                if len(diff) == 1:
                    cdist = min(k-j, CL-(k-j))
                    if cdist != 1:
                        violations += 1
                        p = diff[0]
                        print(f"  VIOLATION in minimal: CL={CL}, j={j}, k={k}, p={p}, dist={cdist}")
                        print(f"    movers={movers}")
                        for i in range(CL):
                            marker = " <--" if i in [j,k] else ""
                            print(f"    [{i}] {cycle[i]} m={movers[i]}{marker}")
                        return found_minimal, violations

    return found_minimal, violations

for ms in [[2,3,3], [2,2,3], [2,3,4], [2,2,2,3], [3,3,3,3], [2,3,3,3], [2,2,3,3]]:
    fm, v = check_minimal_violations(ms, 100000)
    print(f"ms={ms}: {fm} minimal-cycle systems, {v} violations")
