# Broader BAF Support Theorem

Date: April 6, 2026

This note promotes the broader BAF support formula for the EC bridge object
`chi_conf` from an audited pattern to a theorem with a complete proof in the
simple state-sequence realization.

## 1. Setup

Fix:

- `n >= 5`,
- a non-sweep `fc = 2` BAF mover word on `C_n`,
- a consecutive binary triple `{0,1,2}`,
- and the simple state-sequence realization `[0,1,0]` at every processor.

Let the two turnaround steps of the mover word be `t_1, t_2`.

For each processor `p`, define:

- mover-context set `M_p`,
- non-mover-context set `N_p`,
- overlap set `O_p = M_p ∩ N_p`.

Let `ConfState` be the set of good-cycle states whose local triple at some
processor lies in one of the overlap sets `O_p`.

## 2. Theorem

### Theorem. Broader BAF support formula for `chi_conf`.

On the family above,

`ConfState = {all good-cycle states except g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`.

Equivalently:

- the only non-conflict states are the two turnarounds and their immediate
  successors,
- every other good-cycle state is a conflict state,
- and therefore `|ConfState| = 2n - 4`.

This statement has been audited on every tested non-sweep `fc=2` BAF word
through `n=9`.

## 3. Proof

The proof is most transparent in processorwise form.

Let `j` be any non-turnaround processor, and let its two firing times be

`u_j < v_j`.

Define

`A_j = {u_j, u_j+1, v_j, v_j+1}`  (mod `2n`).

We first identify exactly the steps at which processor `j` witnesses conflict.

### Lemma 3.1. Processorwise conflict-step formula.

For every non-turnaround processor `j`, the processor `j` witnesses conflict
exactly on the four steps in `A_j`.

#### Proof

Because every processor follows the simple state sequence `[0,1,0]`, processor
`j` changes:

- from `0` to `1` at its first firing time `u_j`,
- from `1` to `0` at its second firing time `v_j`.

At step `u_j`, processor `j` is a mover on one directed arc. Its predecessor on
that arc has already fired and is in state `1`, while `j` and its successor are
still in state `0`. So the local triple at `j` is `(1,0,0)`, appearing as a
mover context.

At step `u_j+1`, processor `j` is a non-mover while the next processor on the
same arc fires. Processor `j` is now in state `1`, its predecessor is still in
state `1`, and the successor has not yet fired. So the local triple at `j` is
`(1,1,0)`, appearing as a non-mover context.

On the opposite directed arc, the same two local triples appear with the roles
reversed:

- at step `v_j`, processor `j` is a mover with context `(1,1,0)`,
- at step `v_j+1`, processor `j` is a non-mover with context `(1,0,0)`.

Thus both triples `(1,0,0)` and `(1,1,0)` lie in `M_j ∩ N_j`, and processor
`j` witnesses conflict on every step in `A_j`.

Outside the four steps in `A_j`, processor `j` is not in one of these four
local mover/non-mover situations, so it does not witness conflict there. ∎

### Lemma 3.2. Union formula.

`ConfState = ⋃_j A_j`,

where `j` ranges over all non-turnaround processors.

#### Proof

By Lemma 3.1, each non-turnaround processor contributes exactly the four steps
in `A_j`, and every conflict witness comes from one of those processors. So the
full conflict-state set is exactly the union of the `A_j`. ∎

### Lemma 3.3. Simplification of the union.

`⋃_j A_j = {all good-cycle states except g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`.

#### Proof

Consider one directed arc from one turnaround to the other.

The non-turnaround processors on that arc are exactly the movers strictly after
the immediate successor of the starting turnaround and strictly before the
ending turnaround.

For each such processor `j`, the first two elements of `A_j` are `u_j` and
`u_j+1`. As `j` ranges over the non-turnaround processors on that arc, these
cover every step on that arc except:

- the starting turnaround,
- its immediate successor.

Applying the same argument to the opposite directed arc, the last two elements
of the sets `A_j` cover every step on the opposite arc except:

- the second turnaround,
- its immediate successor.

Hence the full union `⋃_j A_j` is exactly the complement of the four
distinguished steps `t_1, t_1+1, t_2, t_2+1`. ∎

The theorem follows immediately from Lemma 3.2 and Lemma 3.3. ∎

## 4. Audit

`ec_conflict_geometry_probe.py` verifies the support formula on every tested
non-sweep `fc=2` BAF word through `n=9`.

Audit summary:

- `n=5`: 5 non-sweep words, 0 failures
- `n=6`: 10 non-sweep words, 0 failures
- `n=7`: 7 non-sweep words, 0 failures
- `n=8`: 12 non-sweep words, 0 failures
- `n=9`: 9 non-sweep words, 0 failures

## 5. Why this matters

This theorem is the first broader EC-side support theorem whose proof is:

- local,
- geometric,
- and independent of spectral language.

Once it is in place, the weak EC bridge theorem becomes much cleaner, because
the support of `chi_conf` is no longer a mysterious derived set.
