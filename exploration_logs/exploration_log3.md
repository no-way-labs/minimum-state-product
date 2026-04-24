# Exploration Log 3: n=9 Witness Construction

## Exploration 10

### Strategy
Construct n=9 witness (M_9 = 7776) via templated algebraic construction,
reusing transition tables from verified n=6 and n=8 witnesses.

### Phase 0: Neighbor Config Analysis

**n=6**: (2, 2, 2, 4, 3, 3)
  P0: m=2, neighbors=(3,2,2)
  P1: m=2, neighbors=(2,2,2)
  P2: m=2, neighbors=(2,2,4)
  P3: m=4, neighbors=(2,4,3)
  P4: m=3, neighbors=(4,3,3)
  P5: m=3, neighbors=(3,3,2)

**n=7**: (3, 2, 2, 2, 3, 4, 3)
  P0: m=3, neighbors=(3,3,2)
  P1: m=2, neighbors=(3,2,2)
  P2: m=2, neighbors=(2,2,2)
  P3: m=2, neighbors=(2,2,3)
  P4: m=3, neighbors=(2,3,4)
  P5: m=4, neighbors=(3,4,3)
  P6: m=3, neighbors=(4,3,3)

**n=8**: (2, 2, 3, 4, 3, 3, 2, 3)
  P0: m=2, neighbors=(3,2,2)
  P1: m=2, neighbors=(2,2,3)
  P2: m=3, neighbors=(2,3,4)
  P3: m=4, neighbors=(3,4,3)
  P4: m=3, neighbors=(4,3,3)
  P5: m=3, neighbors=(3,3,2)
  P6: m=2, neighbors=(3,2,3)
  P7: m=3, neighbors=(2,3,2)

**Key finding:** NO existing witness (n=5..8) has a (3,3,3) processor.
The (3,3,3) triple is genuinely new for n=9.

### Phase 1: n=8 Insertion Compatibility

Insertion at pos 5: (2, 2, 3, 4, 3, 3, 3, 2, 3), product=7776
Neighbor configs:
  P0: (3,2,2) <- n8-P0
  P1: (2,2,3) <- n8-P1
  P2: (2,3,4) <- n8-P2
  P3: (3,4,3) <- n8-P3
  P4: (4,3,3) <- n8-P4
  P5: (3,3,3) <- NEW
  P6: (3,3,2) <- n8-P5
  P7: (3,2,3) <- n8-P6
  P8: (2,3,2) <- n8-P7

All insertion points:
  pos=0: INCOMPATIBLE
  pos=1: INCOMPATIBLE
  pos=2: INCOMPATIBLE
  pos=3: INCOMPATIBLE
  pos=4: INCOMPATIBLE
  pos=5: (2, 2, 3, 4, 3, 3, 3, 2, 3) — new proc config=(3,3,3) ✓ (3,3,3)
  pos=6: INCOMPATIBLE
  pos=7: INCOMPATIBLE
  pos=8: INCOMPATIBLE

### Phase 2: Named Candidates

**Dijkstra Sol 1 interior (copy-left)**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Dijkstra Sol 1 bottom**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Dijkstra Sol 3 middle**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Dijkstra Sol 3 bottom**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Dijkstra Sol 3 top**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Copy-right**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Increment if L!=S**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Decrement if L!=S**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

**Copy-left if R!=S**
  n=8 insertion pos=5 (2, 2, 3, 4, 3, 3, 3, 2, 3): FAIL
  n=6 extension (2, 2, 2, 4, 3, 3, 3, 3, 3): FAIL

### Phase 3: R-independent Enumeration (n=8 insertion at pos 5)

Prefilter: 14 configs need P5 to be privileged for liveness
Distinct (L,S,R) constraint triples: 6

R-independent done: 19683 tested, 2592 liveness pass, 0 full pass, 54.8s

### Phase 4: L-independent Enumeration (n=8 insertion at pos 5)

L-independent done: 19683 tested, 2592 liveness pass, 55.3s

### Phase 5: S-independent Enumeration (n=8 insertion at pos 5)

S-independent done: 19683 tested, 1728 liveness pass, 36.5s

### Phase 6: R-independent Enumeration (n=6 extension)

  ...tested 7000/19683, liveness_pass=207, elapsed=6.5s
  ...tested 8000/19683, liveness_pass=708, elapsed=21.0s
  ...tested 10000/19683, liveness_pass=1261, elapsed=35.9s
  ...tested 11000/19683, liveness_pass=1522, elapsed=42.5s
  ...tested 16000/19683, liveness_pass=3466, elapsed=97.3s
  ...tested 18000/19683, liveness_pass=4094, elapsed=114.1s
  ...tested 19000/19683, liveness_pass=4573, elapsed=128.0s
n=6 extension R-independent done: 19683 tested, 4736 liveness pass, 132.9s

### Phase 7: Other Compatible Insertion Points

### Outcome
FAILED — no valid n=9 witness found in any structured search family.

### What This Rules Out
- R-independent (3,3,3) tables in n=8 insertion at pos 5
- L-independent and S-independent tables at same position
- Same families in n=6 extension framework
- All compatible insertion points in n=8

### What Would Unblock This
- Full 27-entry enumeration with SMT solver constraints
- Derivation of (3,3,3) table from good-cycle structure
- Manual construction using token-flow analysis
