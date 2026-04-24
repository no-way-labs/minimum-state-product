# 3CB Cascade Cycle Investigation Log

## Strategy Register
| # | Strategy | Status | Key Finding |
|---|----------|--------|-------------|
| 1 | Proc-1-locked subgraph | DONE | Only 12 interior-only 2-cycles (proc 6 oscillating). NO cascade cycles. Locking was too restrictive. |
| 2 | Full recurrent SCC analysis | DONE | 75 SCCs: 2x112 + 1x16 + 72x2. All large SCCs have cascade structure. |
| 3 | Cycle enumeration in large SCCs | DONE | ALL cycles are length 16 with exact structure: 6 binary + 4 border + 6 interior fires, 4 boundary switches. |
| 4 | Cascade pattern decomposition | DONE | Clear 8-phase cascade: B-B-B-R-I-R-B-B-B-R-I-I-I-R-I-I (or rotations). Visits all 4 boundary conditions. |

## Exploration 1: Cascade Cycle Search at n=8

**Goal**: Find cascade cycles in the bad-config graph of n=8 3CB systems.

### System Built
- ms=(2,2,2,3,3,3,3,4), product=2592
- Best construction: mixed_sweep, 16 good configs
- Recurrent bad: 384 configs in 75 SCCs
- Binary procs: {0,1,2}, Border procs: {3,7}, Interior procs: {4,5,6}

### Recurrent SCC Structure
- **2 large SCCs**: 112 configs each (SCC0 and SCC1)
- **1 medium SCC**: 16 configs (SCC2, out-degree 1 everywhere = single cycle)
- **72 small SCCs**: 2 configs each (all proc-6 oscillations)
- Total: 2×112 + 16 + 72×2 = 384 recurrent configs

### SCC Characterization

**SCC0 and SCC1 (112 configs each)**:
- All 8 procs fire within the SCC
- 4 boundary conditions: (0,0), (0,1), (1,0), (1,1) — 28 configs each
- 8 interior states, 8 binary states (all combinations present)
- **Interior is DAG under each boundary** — no interior-only cycles
- **No incompatible orderings** between any pair of boundaries
- ALL 60 border transitions are boundary-switching (border procs never fire without changing boundary)
- Out-degree distribution: 1 (16 configs), 2 (64 configs), 3 (32 configs)
- SCC1 can reach SCC0 (320 edges) but not vice versa. Neither connects to 2-cycles.
- SCC0 vs SCC1 distinguished by binary-value distribution: SCC0 overrepresents (0,0,0)/(1,1,1), SCC1 overrepresents (0,1,0)/(1,0,1)

**SCC2 (16 configs)**:
- Unique Hamiltonian cycle (all out-degree 1)
- All 8 procs fire
- 4 boundary conditions, 6 interior states, 6 binary states

**72 two-cycles**:
- ALL involve only proc 6 oscillating
- Boundary conditions: (0,0), (1,0), or (2,0) — 24 each
- Proc 6 oscillates via f6(2,0,0)=1, f6(2,1,0)=0

### The Cascade Cycle Pattern

**ALL cycles in the large SCCs have length exactly 16**, with invariant structure:
- 6 binary fires, 4 border fires, 6 interior fires
- Exactly 4 boundary switches (visiting all 4 boundary conditions (0,0)→(1,0)→(1,1)→(0,1)→(0,0))

**Canonical 16-step cascade (from SCC0):**
```
Phase 1 (Binary sweep up): bin=(0,0,0)→(1,1,1), boundary fixed at (0,0)
  [0] p0(BIN): (0,0,0)→(1,0,0)
  [1] p1(BIN): (1,0,0)→(1,1,0)
  [2] p2(BIN): (1,1,0)→(1,1,1)

Phase 2 (Border switch 1): boundary (0,0)→(1,0)
  [3] p3(BRD): c[3]: 0→1

Phase 3 (Interior adjust): one interior step
  [4] p4(INT): int=(0,0,2)→(1,0,2)

Phase 4 (Border switch 2): boundary (1,0)→(1,1)
  [5] p7(BRD): c[7]: 0→1

Phase 5 (Binary sweep down): bin=(1,1,1)→(0,0,0), boundary fixed at (1,1)
  [6] p0(BIN): (1,1,1)→(0,1,1)
  [7] p1(BIN): (0,1,1)→(0,0,1)
  [8] p2(BIN): (0,0,1)→(0,0,0)

Phase 6 (Border switch 3): boundary (1,1)→(0,1)
  [9] p3(BRD): c[3]: 1→0

Phase 7 (Interior cascade): 3 interior steps
  [10] p6(INT): int=(1,0,2)→(1,0,0)
  [11] p5(INT): int=(1,0,0)→(1,1,0)
  [12] p4(INT): int=(1,1,0)→(0,1,0)

Phase 8 (Border switch 4): boundary (0,1)→(0,0)
  [13] p7(BRD): c[7]: 1→0

Phase 9 (Interior restore): 2 interior steps
  [14] p6(INT): int=(0,1,0)→(0,1,2)
  [15] p5(INT): int=(0,1,2)→(0,0,2) → back to start
```

**SCC2 has the same 8-phase structure**: B-R-I-R-B-R-I-R (with 3 binary, 1 border, 3 interior in each half).

### The Cascade Mechanism

The cycle works as follows:
1. **Binary sweep** flips all 3 binary procs (0→1→1→1 or vice versa)
2. This makes a **border proc privileged** → boundary condition changes
3. Under the new boundary, **interior procs must adjust** (the interior DAG ordering differs)
4. After interior adjustment, the **other border proc** becomes privileged → second boundary switch
5. Under the second new boundary, the binary sweep reverses
6. This triggers another boundary switch, requiring more interior adjustment
7. The cycle closes after visiting all 4 boundary conditions

### Key Insight: NOT Incompatible Interior Orderings

The interior is a **DAG under each fixed boundary** — no incompatible orderings between boundaries. The cycle is NOT caused by interior ordering reversal. Instead, it's caused by the **coupling between binary sweep and boundary conditions**: the binary sweep forces border procs to fire (changing boundary), which forces interior adjustment, which enables the reverse binary sweep.

### Forced Table Entries

The 16-step cycle forces exactly 16 table entries (0 conflicts). These are spread across all 8 procs. The cascade structure appears to be intrinsic to the topology: with 3 consecutive binary procs, any binary sweep will propagate through the borders and interior.

### n=7 Comparison

At n=7, ms=(2,2,2,3,3,3,4):
- Best system has 160 recurrent bad configs (26 SCCs)
- Same structure: 2 large SCCs (70, 42) + 24 two-cycles
- Interior procs {4,5}, border procs {3,6}
- The 2-cycles are also proc-5 oscillations
- **n=7 also has recurrent bad configs** — but a valid system EXISTS at n=7 via different constructions

This means the cascade cycles are present in BOTH n=7 and n=8 for this particular construction method. The difference is that at n=7, alternative constructions can avoid them, while at n=8 they cannot.

### Proc-1-Locked Analysis (Strategy 1)

- 638 proc-1-locked configs out of 2576 bad
- Only procs {3,4,5,6,7} are privileged in locked configs
- 12 locked recurrent SCCs, all size-2, all interior-only (proc 6 oscillating)
- **Zero cascade cycles in locked subgraph** — the locking condition prevents boundary switches because it requires all binary procs to be non-privileged, but the cascade cycle requires binary procs to fire

### Summary of Answers

1. **Do cascade cycles exist?** YES — ALL large recurrent SCCs are cascade cycles
2. **Are ALL recurrent SCCs cascade cycles?** No — 72 of 75 SCCs are simple proc-6 2-cycles. But the large SCCs (containing 240/384 = 62.5% of recurrent configs) are cascade cycles.
3. **Interior-only vs cascade?** The 72 two-cycles are interior-only. The 3 large SCCs are cascade.
4. **How many boundary conditions?** All 4 are visited in each cascade cycle.
5. **Incompatible ordering?** NO — interior is DAG under each boundary. The cycle is driven by binary-sweep/border coupling, not interior reversal.
6. **n=7 comparison?** Same cascade structure exists but valid systems can be built via other methods.
