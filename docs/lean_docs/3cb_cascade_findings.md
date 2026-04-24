# 3CB Cascade Mechanism — Findings for Future n=7,8 LB Proofs

Date: 2026-04-09
Status: Research complete, not yet formalized. Pick up when n≥9 LB is done.

## What this is

During a session investigating the 3CB open problem (why 3 consecutive binary
procs block convergence at n≥8), we discovered the actual obstruction mechanism:
the **binary-sweep/border cascade cycle**. This document captures the findings
for future use when building the n=7 and n=8 lower bound proofs.

## The mechanism in one paragraph

With 3CB, the adversary can force a 16-step bad cycle: sweep all 3 binary procs
UP (0,0,0)→(1,1,1), which forces a border proc to become privileged (liveness),
border fires and changes boundary condition, interior procs adjust, then the
reverse sweep DOWN (1,1,1)→(0,0,0) forces the other border, interior adjusts
again, and the cycle closes. The system can't escape because good configs are
exponentially rare: O(n) good vs Θ(product/8) total at each binary triple.

## Key results

### Proved unconditionally
- **Toggle constraint**: at most 1 of each toggle pair is mover at binary procs
- **Fiber coupling**: proc 1 moves entire fibers of product/8 configs identically
- **Sibling indistinguishability**: proc 1 can't discriminate far states
- **Interior DAG + sinks**: interior-only dynamics at fixed binary state terminate at non-interior privilege (from convergence + liveness)
- **Non-interior privilege forcing**: adversary always reaches border/binary privilege (from DAG termination + liveness)
- **Exponential drainage deficit**: B/C = Θ(3^(n-2)/n)
- **P1 wall principle**: P1 isolates P0 from P2 during between-segments
- **Parity-to-AD reduction**: anti-diagonal ⟺ both endpoint bounce counts even

### Proved at n=8 computationally
- **0/80 toggle-valid privilege rules** at proc 1 achieve convergence
- **Hill climbing**: reduces bad SCCs from 2448 to 240, never to 0
- **100% cascade rate**: 51/51 random live systems have cascade cycles
- **Anti-diagonal**: 386/386 cycles at n=8 (100%)
- **Fire count = 2**: P1 fires exactly twice in all >2000 tested cycles
- All 13 recurrent SCCs span all 8 binary triples (full cascade structure)

### The critical inequality
A 3CB system can escape the cascade iff:

    good_fraction_at_each_binary_triple > 1/m_border

- n=7 valid system: 30/108 = 27.8% ≈ 1/m_border (barely works)
- n=8 best attempt: 6/324 = 1.9% << 25% (impossible)

### The cascade cycle structure (n=8)
```
Phase 1: Binary sweep UP    (0,0,0)→(1,1,1)     [p0,p1,p2 fire]
Phase 2: Border switch       c[3] changes          [p3 fires]
Phase 3: Interior adjust                           [interior procs]
Phase 4: Border switch       c[7] changes          [p7 fires]
Phase 5: Binary sweep DOWN  (1,1,1)→(0,0,0)     [p0,p1,p2 fire]
Phase 6: Border switch       c[3] changes          [p3 fires]
Phase 7: Interior cascade                          [interior procs]
Phase 8: Border switch       c[7] changes          [p7 fires]
→ return to start
```
16 steps: 6 binary + 4 border + 6 interior fires. Visits all 4 boundary conditions.

### SCC decomposition at n=8 (384 recurrent bad configs)
- 2 large SCCs (112 each): full cascade, all 8 procs active
- 2 medium SCCs (64 each): cascade without P4,P5
- 2 small SCCs (32 each): cascade without P3,P4,P5
- 7 minimal SCCs (16 each): P0,P1 binary + P6,P7 border only

## Gaps to close before formalization

| Gap | Description | Severity | Approach |
|-----|-------------|----------|----------|
| Adversary avoidance | Prove adversary can avoid good configs for ALL sub-threshold multisets | High | Counting: good fraction < 1/m_border from product bound |
| Good cycle length | Prove no good cycle achieves sufficient good fraction at n≥8 | High | P1 fiber coupling limits good to O(n) per binary triple |
| Fire count upper bound | Prove P1 fires exactly 2 (not just ≥2) | Low | ME packing argument, verified >2000 cycles |
| No bounces for n≥6 | Prove AD holds (endpoint bounce counts even) | Low | Verified 900+ cycles, mechanism understood |
| All multisets | Extend from ms=(2,2,2,3,...,3,4) to all sub-threshold 3CB | Medium | The critical inequality is multiset-independent |

## Why this matters for n=7,8 LB (not n≥9)

The n≥9 LB proof uses shadow cycles + entry conflict (already complete). The
cascade work is NOT needed for n≥9.

But n=7,8 have different bounds (M_n = 32·3^(n-4)) and different sub-threshold
multisets. The n≥9 proof machinery doesn't directly apply. The cascade proof
could be the PRIMARY mechanism for the 3CB component:

- n=8 3CB sub-threshold (product < 2592): cascade directly applies
- n=7 3CB sub-threshold (product < 864): cascade with tighter counting
- Non-3CB sub-threshold at n=7,8: needs separate treatment (shadow/EC)

## Files produced

### Proof documents
- `probes/pa_3cb_cascade_proof.md` — cascade unavoidability proof (328 lines)
- `probes/pa_3cb_drainage_proof.md` — fiber coupling + drainage deficit (948 lines)
- `probes/pa_3cb_antidiag_proof.md` — anti-diagonal fire pattern proof

### Exploration logs
- `exploration_logs/exploration_log_3cb_privilege_graph.md` — SCC structure (RA-1)
- `exploration_logs/exploration_log_3cb_response_exhaustion.md` — 80 privilege rules (RA-2)
- `exploration_logs/exploration_log_3cb_context_saturation.md` — saturation curve (RA-3)
- `exploration_logs/exploration_log_3cb_cascade.md` — cascade cycle discovery (RA-cascade)

### Key scripts
- `probes/ra_3cb_comprehensive.py` — main investigation (saturation + exhaustion)
- `probes/ra_3cb_transition.py` — system construction infrastructure
- `probes/cascade_cycle_analysis.py` — canonical cascade decomposition
- `probes/ra_3cb_priv_deep.py` — fire pattern structural analysis
- `probes/pa_cascade_final_verify.py` — adversary simulation + SCC verification

## How to pick this up

1. Read this doc + `pa_3cb_cascade_proof.md` (the proof with gaps marked)
2. Close Gap 1 (adversary avoidance for all multisets) — this is the kill shot
3. Close Gap 2 (good cycle length bound) — probably follows from fiber coupling
4. Decide: formalize in Lean directly, or prove analytically first then formalize
5. Handle non-3CB sub-threshold cases at n=7,8 separately
