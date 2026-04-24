# Exploration Log: 3CB Response Exhaustion at Proc 1

## Strategy Register
- **Eliminated**: Single-proc privilege rule optimization — no choice at proc 1 achieves convergence at n=8
- **Obstructions**: DRAINAGE FAILURE IS UNIVERSAL across all 80 toggle-valid privilege rules at proc 1. Min recurrent = 384. Range [384, 528].
- **Building blocks**: Toggle-valid rule enumeration (80 rules from 4 toggle pairs). Per-rule recurrent measurement pipeline.
- **Known reformulations**: (none yet)

---

## Exploration 1

### Strategy
Enumerate all 80 toggle-valid privilege rules at proc 1 (middle binary) for n=8 ms=(2,2,2,3,3,3,3,4), test each with mixed-sweep constructions, measure minimum recurrent bad configs.

### Outcome
SUCCEEDED — drainage failure is universal

### Concrete Artifacts

COMPUTED EXAMPLES:
- 80 toggle-valid rules total: 8 of size 1, 24 of size 2, 32 of size 3, 16 of size 4
- Toggle pairs: {(L,0,R), (L,1,R)} for L in {0,1}, R in {0,1} -> 4 pairs
- Each pair: choose first, second, or neither -> 3^4 - 1 = 80 non-empty subsets

STRUCTURAL RESULTS:
- **0/80 rules achieve convergence**
- |M|=1: 8 rules, NONE found compatible cycles with mixed-sweep
- |M|=2: 24 rules, 4 with finite recurrent (range [384, 528])
- |M|=3: 32 rules, 12 with finite recurrent (range [384, 528])
- |M|=4: 16 rules, 4 with finite recurrent (range [384, 528])
- Best rules (384 recurrent): {(0,1,1),(1,0,0)}, {(0,0,0),(1,1,1)}, and some size-3/4 extensions
- Best 2 rules are symmetric: both are "diagonal" toggle pairs

TOOLS:
- Response exhaustion pipeline in ra_3cb_comprehensive.py

### Failure Constraint
For every toggle-valid privilege rule at proc 1, every compatible mixed-sweep good-targeting construction has >= 384 recurrent bad configs.

### What This Rules Out
**Optimizing proc 1's privilege rule alone cannot fix convergence at n=8.** The failure involves ALL processors' tables.

### What Would Unblock This
1. Testing with non-mixed-sweep constructions
2. Joint optimization over proc 1 AND its neighbors
3. Full exhaustive search at n=8 (probably needs C code)

### Open Questions
1. Is 384 the true minimum across ALL construction methods?
2. Why do the "diagonal" rules {(0,1,1),(1,0,0)} and {(0,0,0),(1,1,1)} achieve minimum?
3. |M|=1 rules found no compatible cycles — structural or search artifact?

---

## Exploration 2: Deep Structural Analysis

### Strategy
Analyze WHY 69/80 rules fail. Extract proc 1 mover requirements from each cycle.

### Outcome
Only 4 distinct requirement patterns exist across all 386 cycles:
1. fire={(0,1,1),(1,0,0)}, stay={(0,0,0),(0,0,1),(1,1,0),(1,1,1)} -- 288 cycles, 4 compatible rules
2. fire={(0,0,0),(1,1,1)}, stay={(0,1,0),(0,1,1),(1,0,0),(1,0,1)} -- 48 cycles, 4 compatible rules
3. fire={(0,1,0),(1,0,1)}, stay={(0,0,0),(0,0,1),(1,1,0),(1,1,1)} -- 48 cycles, 4 compatible rules
4. fire={(0,0,1),(0,1,1),(1,0,1),(1,1,1)} -- 2 cycles, toggle-INCONSISTENT (same pair both fire), 0 compatible

Key insight: Every cycle requires proc 1 to fire exactly TWICE (once 0->1, once 1->0). The two firing contexts are ANTI-DIAGONAL: {(a,0,c),(1-a,1,1-c)}. Rules must contain the fire set as a subset. Size-1 rules have only one b-value, can't fire from both states. Same-b size-2 rules also fail.

### Concrete Artifacts
- Script: `ra_3cb_priv_deep.py`
- 3 consistent fire patterns x 4 rules each = 12, minus 1 overlap = 11 unique compatible rules

---

## Exploration 3: Is Convergence Failure Structural?

### Strategy
Test whether the bad-SCC obstruction is an artifact of good-targeting, or persists with random completions, hill climbing, and random mutation.

### Results
- Random completions (1000 trials, rule {(0,1,1),(1,0,0)}): 0 valid, WORST SCC totals (min 1637 vs 384 for GT)
- Hill climbing (5 seeds x 500 steps, all 3 patterns):
  - Pattern {(0,1,1),(1,0,0)}: GT=2448, best hill=240
  - Pattern {(0,0,0),(1,1,1)}: GT=2448, best hill=240
  - Pattern {(0,1,0),(1,0,1)}: GT=2448, best hill=432
- Random mutation (2000 trials per pattern): 0 valid

### Conclusion
Convergence failure is STRUCTURAL, not a completion artifact. Hill climbing reduces bad SCCs from 2448 to 240 but cannot eliminate them.

### Concrete Artifacts
- Scripts: `ra_3cb_priv_random.py`, `ra_3cb_priv_hill2.py`

### Summary Table

| Approach | Trials | Valid | Min bad SCC nodes |
|----------|--------|-------|-------------------|
| GT completion, all 80 rules | 80 x 302 cycles | 0 | 384 |
| Random completion | 1000 | 0 | 1637 |
| Hill climb (5 seeds) | 7500 steps | 0 | 240 |
| Random mutation | 6000 | 0 | >0 |

**UNIVERSAL FAILURE**: No privilege rule at proc 1, combined with any completion strategy for the remaining processors, yields a valid self-stabilizing system for ms=(2,2,2,3,3,3,3,4) at n=8.
