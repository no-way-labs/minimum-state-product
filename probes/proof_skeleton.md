# Proof Skeleton for Sorry 2+3 (Consecutive Binary)

## The Palindromic Entry Conflict

### Setup
- 3 consecutive binary: i, ri = right(i), rri = right(right(i))
- ri fires ≥ 2 times, all isolated (never at consecutive steps)
- Pick the first two firings of ri: at steps t1 and t2 (t1 < t2)

### The Gap [t1+1, t2-1]
- ri doesn't fire in this interval
- The mover visits i and/or rri
- The mover entered from ri (at t1+1: mover = i or rri, since nearest-neighbor and previous mover was ri)

### Key Observation
At step t1: ri fires. Config changes.
At step t1+1: some neighbor of ri fires (i or rri). ri is NONMOVER.

At step t2: ri fires again. ri is MOVER.

### Context at ri
At step t1+1 (nonmover): ri's context = (c[i], c[ri], c[rri]) = (i_val_after_t1, ri_val_after_t1, rri_val_at_t1)
At step t2 (mover): ri's context = (c[i], c[ri], c[rri]) = (i_val_at_t2, ri_val_at_t2, rri_val_at_t2)

### For EC at ri: need these contexts to MATCH
- ri_val: ri fired at t1 (toggled from S to 1-S), doesn't fire again until t2. So ri_val is constant = 1-S throughout [t1+1, t2]. MATCH on S component: ri_val_after_t1 = 1-S = ri_val_at_t2. ✓
- i_val: depends on how many times i fires in [t1+1, t2). If even: returns. If odd: flipped.
- rri_val: same.

### For the specific case where BOTH i and rri fire EVEN times in [t1+1, t2):
- All three components match → EC at ri → False ✓
This is the "BothEven" mechanism (already proved!)

### For the case where i fires ODD times or rri fires ODD times:
This is where the parity walk argument comes in.
The paper proof handles this by looking at DIFFERENT pairs of steps.

### The Paper's Approach (CIC Expl 14)
The paper doesn't compare t1+1 with t2. It compares:
- The nonmover step of proc j when j+1 fires (CW direction)
- The mover step of proc j when j fires (CCW direction)

For the BAF structure, these have matching contexts because:
- R-neighbor = 0 at both steps (hasn't fired / already re-zeroed)
- L-neighbor = x_{j-1} at both (has fired once / not yet re-fired)
- Self = x_j at both

### How to Apply in Lean
The existing BAFWord.lean has:
- BAFArcAdj structure: paired arc with binary right endpoint
- elim_of_binary_right: constructs EC from BAFArcAdj

The bridge: from "3 consecutive binary + isolated ri" → BAFArcAdj

PairedCrossing.lean gives: opposite-direction edge crossings at binary edges
ContextBridge.lean gives: value preservation between steps
BinaryParity.lean gives: even fire count → value preserved

The BAFArcAdj needs specific fields. Read BAFWord.lean to see exactly what.
