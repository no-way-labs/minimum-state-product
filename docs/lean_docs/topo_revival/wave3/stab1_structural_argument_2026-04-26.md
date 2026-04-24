# P4 — Why `stab = 1` is the generic outcome for lifted-defect circulation

**Scope.** One-paragraph structural argument for Wave 3 Priority 4
(`probe_plan_wave3_c1_hardening_2026-04-26.md` §5), with the Wave 3
empirical observation as context: on all 19 feasible sub-threshold
records tested, the cycle-time-shift stabilizer of `supp Φ` is exactly 1.

---

## Claim

For any lifted-defect flow `Φ : E_lift → ℝ≥0` satisfying `B^T Φ = 0`
(incidence-zero), if `supp Φ` is cycle-time-shift invariant
(`supp Φ(s·e) = supp Φ(e)` for every `s ∈ Fin L`), then `Φ` vanishes on
every transport-edge whose time fiber is truncated by the value-
consistent / non-good (VC-NG) conditions. On records where *no* time
fiber is full-length, cycle-time-shift-invariant `Φ` is forced to zero.
Hence stab = 1 is the generic outcome whenever feasibility requires
transport-weight.

## Proof sketch (informal)

Fix a lifted "time fiber" `F_{q,a} := {(k, q, a) : k ∈ Fin L, c_k[q:=a]
∈ T_N1}`. Transport edges out of `(k, q, a)` go to `(k+1, q, a)` when
the cycle's mover `mov_k` is non-adjacent to q; these are the only
edges that live entirely inside `F_{q,a}`. Twist edges (c_self /
c_left / c_right) connect different fibers by the time-adjacency at
the defect position.

- If `F_{q,a}` has length L (i.e., `c_k[q:=a] ∈ T_N1` for every k), the
  transport edges form a closed loop around the fiber, and a
  cycle-time-shift-invariant `Φ` restricted to this fiber can be
  nonzero (a uniform weight on every transport edge satisfies
  incidence-zero on the fiber).
- If `F_{q,a}` has length `< L` (some `k` have `c_k[q:=a]` either
  in `G(C)` — the good cycle — or value-inconsistent, hence not in
  `T_N1` and not in `V_lift`), the transport edges form an open arc
  rather than a closed loop. Cycle-time-shift-invariant `Φ` on an
  open arc requires equal weight on every transport edge in the arc,
  but the arc's endpoints produce unbalanced boundary at the
  terminating vertices of the arc — which forces `Φ = 0` on the arc.

On a record where *every* fiber `F_{q,a}` is truncated, the only
cycle-time-shift-invariant flow compatible with `B^T Φ = 0` is `Φ ≡ 0`,
which is not a *nonzero* circulation. Hence any feasible `Φ` must have
nontrivial (stab < L) stabilizer.

The argument does not require stab = 1 specifically; it says only that
stab < L is forced. The observed uniformity at stab = 1 on 19/19
records is a stronger empirical fact that my sketch does not explain.
One plausible reason: the LP solver returns a vertex-of-polyhedron
optimum, and among feasible flows those at low stabilizer order tend
to be more "localized" (smaller support), which the LP's `min -1^T Φ`
objective with box bound `[0, 1]` favours marginally. This is
heuristic; I did not prove it.

## What this argument does and does not cover

**Covers.** The claim that stab = L (full cycle-time-shift invariance)
implies `Φ ≡ 0` for any record with at least one truncated time fiber.
Records in my corpus have many truncated fibers by construction (VC
restrictions on `a ∈ V_tube[q]` and non-good exclusion via cycle
intersection), so stab = L is excluded across the board.

**Does not cover.** The specific observation stab = 1 (trivial)
uniformly. Stab = 2 or any other proper divisor of L is consistent
with my sketch; ruling those out empirically is what the probe did
but structurally I do not have an argument.

**Operational consequence.** The cycle-time-shift guard in Wave 2
addendum §3.3 — "KILL (RED) if supp Φ is invariant under cycle-time
shift for all s ∈ Fin L on all tested records" — is structurally
satisfied up to the fiber-truncation lemma above. The tighter form
("stab = 1 universally") is empirical, not structural. When reporting
C1/C2 verdicts, cite stab < L as the guaranteed guard and stab = 1
as the observed-but-unproven refinement.

## Status

The sketch above is adequate for the Wave 2 addendum §3.3 guard (which
only requires stab < L, i.e., some non-invariance). The stab = 1
uniform observation remains **empirical only** and should not be
promoted to a pre-commit guarantee in later waves. If C3 or a future
step requires stab = 1 specifically, the argument needs completion —
likely via an LP-polyhedral analysis that I have not attempted here.

---

*End of P4 memo.*
