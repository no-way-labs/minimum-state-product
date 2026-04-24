# Exploration Log: 3CB Privilege Graph Structure

## Strategy Register
- **Eliminated**: (none yet)
- **Obstructions**: Mixed-sweep good-targeting fails convergence at ALL n (4-8), not just n≥8. Construction method matters.
- **Building blocks**: Tarjan SCC analysis pipeline. Recurrent SCC context distribution measurement. ra_3cb_comprehensive.py.
- **Known reformulations**: (none yet)

---

## Exploration 1

### Strategy
Map privilege graph structure at n=4..8 with 3CB using mixed-sweep + good-targeting construction, analyze recurrent SCC structure and context distribution at middle binary proc.

### Outcome
SUCCEEDED (data collected, important caveats)

### Surviving Structure

**Key finding**: The mixed-sweep good-targeting construction produces recurrent bad SCCs at ALL n values (4-8), even though valid 3CB systems are known to exist at n=4,5,6,7. This means the construction method is suboptimal — the data shows construction-dependent failures, not structural impossibility (except at n=8 where 768+ constructions fail).

**SCC structure at n=8 (best construction, 384 recurrent):**
- 75 recurrent SCCs total
- 1 dominant SCC of size 112 (all 8 procs privileged ~equally, 42 each)
- 74 small SCCs of size 2
- Recurrent configs spread nearly uniformly across all 8 contexts at proc 1:
  - Corners (0,0,0) and (1,1,1): 44 each
  - All others: 49-50 each
- NOT concentrated at any specific context → bottleneck is NOT localized

**Privileged proc distribution in dominant SCC**: Every proc is privileged ~42 times across 112 configs. Perfectly uniform. The SCC is a "balanced trap" — no proc dominates.

**Cross-n comparison (same construction method):**

| n | product | good | bad | recurrent | SCCs | drain% |
|---|---------|------|-----|-----------|------|--------|
| 4 | 24 | 8 | 16 | 8 | 1 | 25.0% |
| 5 | 96 | 10 | 86 | 20 | 1 | 7.0% |
| 6 | 288 | 12 | 276 | 52 | 2 | 2.9% |
| 7 | 864 | 14 | 850 | 160 | 26 | 1.2% |
| 8 | 2592 | 16 | 2576 | 384 | 75 | 0.5% |

### Concrete Artifacts

COMPUTED EXAMPLES:
- n=8: 75 SCCs (1x112 + 74x2), 384 recurrent, contexts uniform
- n=7: 26 SCCs (1x70 + 25x2), 160 recurrent, contexts uniform
- n=6: 2 SCCs (1x40 + 1x12), 52 recurrent
- n=5: 1 SCC of 20, all 5 procs equally privileged
- n=4: 1 SCC of 8, all 4 procs equally privileged

STRUCTURAL RESULTS:
- Recurrent configs are uniformly distributed across all 8 contexts at middle binary
- Drainage rate decays as ~O(n/product)
- SCC count grows roughly as 3^(n-5): 1, 1, 2, 26, 75
- Dominant SCC has perfectly uniform privilege distribution

TOOLS:
- ra_3cb_comprehensive.py: Self-contained analysis (Tarjan SCC, context distribution, drainage measurement)

### What Would Unblock This
Need to test with VALID system constructions at n=4,5,6,7 to compare valid-system privilege graphs against n=8 failing graphs.

### Open Questions
1. What does the privilege graph look like for a VALID 3CB system at n=7?
2. Is the n=8 dominant SCC (size 112) structurally unavoidable?
3. Uniform context distribution suggests the bottleneck isn't at proc 1 specifically — is it everywhere simultaneously?
