# Reviewer Reply: Review Packet V2

Date: April 6, 2026

## Overall Assessment

The two-track restructuring is the right move. The observation that the EC
overlap scalar is width-3 local (and therefore spectrally invisible to the
forbidden-mass observable) is not a soft design choice — it is a theorem that
forces the program to bifurcate. Any reviewer who suggests collapsing the two
tracks back into one needs to reckon with this fact.

That said, the program now has a harder closing problem than before. A
single-observable program needs one bridge theorem. A two-observable program
needs either two bridges or a disjunction lemma, and the disjunction lemma
requires understanding the space of subthreshold systems well enough to
partition it. This is the central tension in the packet, and the remainder of
this reply focuses on it.

## On the Shadow Track

The shadow-side results are in good shape as an explicit-family package. No
major concerns beyond those raised in the v1 review:

- The floor 71/504 comes from a single class at n=7. Pushing to n=8 would
  strengthen the claim that the floor stabilizes rather than decays.
- The symbolic core (relabeling invariance, equivariance route) is clean for
  the canonical placement but incomplete for the broader classes. This is
  acknowledged honestly in the packet.
- The same-n separation from valid coarse-layer values is compelling and
  appears to widen with n. This is the strongest qualitative feature of the
  shadow track.

No new issues here. The shadow track is ready for a paper modulo the scope
questions already identified.

## On the EC Track

The EC results are newer and deserve closer scrutiny.

### The formula E_conf = 2(n-3)

This is clean and presumably provable for the canonical BAF family by direct
construction. If so, it should be proved and written up — it is a concrete,
quotable theorem independent of all spectral machinery. Linear growth in n is
a strong obstruction signature.

**Question:** Is E_conf = 2(n-3) tight for the canonical BAF family, or is it
a lower bound? That is: are there other good-cycle choices for the same state
vector that yield smaller E_conf? If 2(n-3) is the minimum over all valid
good-cycle choices, that is a much stronger statement than if it holds for a
particular canonical choice.

**Question:** What happens to E_conf for state vectors outside {2,3}^n? If a
processor has 4 states, does the overlap count drop? Understanding this
dependence matters for any bridge argument, because a universal theorem needs
to handle arbitrary state vectors.

### The spectral invisibility of E_conf

The packet correctly identifies that the raw EC overlap scalar is width-3 local
and therefore has ForbidFrac_{n-2} = 0. This is stated as a reason to separate
the tracks. Agreed — but it also raises a deeper question.

The raw overlap count is local, but the *obstruction* it creates is not.
Overlaps at processor p constrain the global reachability structure. There
should be a derived quantity — something measuring the downstream global
consequence of the local overlaps — that is nonlocal and potentially has
nonzero forbidden mass.

Candidates to investigate:

- The indicator of configurations that are reachable from two distinct
  good-cycle states via entry at the same processor. This is a global object
  derived from the local overlaps.
- The mutual information between distant processors conditional on the
  entry-conflict structure. If EC forces long-range correlations in the
  reachability graph, these correlations should appear spectrally.
- The "EC-induced bad set": the set of configurations that cannot be
  unambiguously routed to the good cycle because of entry conflicts. Its
  indicator is a global scalar.

If any of these derived quantities has nonzero forbidden mass, the two tracks
might reunify at a deeper level. The current separation could be an artifact of
measuring the raw witness rather than its global consequence. This is worth
checking computationally before committing fully to the two-track architecture.

## On the Disjunctive Witness Theorem

The packet proposes

> every subthreshold system yields either an EC witness or a shadow witness

as the universal target. This is a reasonable aspiration, but the packet does
not yet contain a candidate for the case-split predicate. Without one, the
disjunction is a hope, not a program.

### What the case split needs to look like

A useful disjunctive theorem requires a property P of subthreshold systems
such that:

- P is decidable from the system description (not from running the full
  convergence analysis),
- P implies positive EC complexity,
- not-P implies positive shadow forbidden mass,
- and the proof of each implication is self-contained.

### Candidate for P

The most natural candidate, given the structure of the two tracks:

> P = "the system's bad-cycle obstruction is locally resolvable"

meaning: the reason the system fails (if it were to fail) can be detected
within width-3 windows. When P holds, the failure mode is EC-type (local
overlaps create contradictions). When P fails, the failure mode is inherently
nonlocal, and the shadow-side forbidden mass should be large because the
obstruction lives in high-order interactions.

This is vague as stated. Making it precise requires defining "locally
resolvable" in terms of the ANOVA decomposition or the reachability graph. But
it suggests the right conceptual axis for the split.

### An alternative to disjunction: a unified functional

Rather than proving "A or B," consider defining a single functional

W(system) = alpha * ForbidFrac_{n-2}(chi_shadow) + beta * E_conf

or more generally some min/max combination, and proving W > 0 for all
subthreshold systems. The proof of W > 0 would go through different cases
internally, but the theorem statement would be a single inequality. This is
cleaner to state, easier to apply, and sidesteps the need for an explicit
case-split predicate.

The challenge is that ForbidFrac and E_conf live in different spaces and have
different units, so combining them requires a normalization. But this is a
technical problem, not a conceptual one.

## On Bridge Routes

The packet lists three: extraction, reduction, direct disjunction.

**Extraction** (define a canonical witness for arbitrary subthreshold systems):
This requires understanding what "the shadow" or "the EC structure" looks like
for a system that was not built from an explicit family. The existing shadow
construction depends on having a canonical sweep cycle, which arbitrary systems
may not have. Unless there is a way to canonically associate a sweep-like
structure to any subthreshold system, extraction will stall.

**Reduction** (reduce arbitrary systems to explicit obstruction-bearing forms):
This is essentially classification of subthreshold systems. If this were easy,
the lower bound would already be proved by other methods. Low probability of
success as a primary strategy.

**Direct disjunction** (prove every subthreshold system has one or the other):
Most promising, but needs the case-split predicate discussed above.

**Fourth route worth considering: spectral transport on the EC side.**
The spectral transport argument from the v1 discussion targeted the shadow
side. But a parallel argument might work for the EC side with a different
observable. If local updates can only reduce E_conf by a bounded amount per
step (an "EC transport lemma"), and subthreshold systems are forced to start
with positive E_conf, then convergence requires enough steps or enough states
to drive E_conf to zero. This would be a purely EC-side lower bound, no shadow
machinery needed. The question is whether such a transport bound exists — can
a single local update eliminate at most one overlap?

## Priorities

1. **Check whether derived EC quantities have forbidden mass.** If yes, the
   two tracks may reunify and the program simplifies dramatically. This is
   the highest-value computation right now.

2. **Prove E_conf = 2(n-3) for the canonical BAF family.** This is likely
   the easiest publishable theorem in the program. Do it.

3. **Investigate EC transport.** Can a single local update step reduce E_conf
   by at most a bounded amount? If so, this gives a purely local-to-global
   argument on the EC side, parallel to the spectral transport idea on the
   shadow side.

4. **Search for a case-split predicate.** Look at subthreshold systems that
   are known to be EC-type vs shadow-type. What property distinguishes them?
   Even an empirical observation on small cases would guide the theory.

5. **Consider the unified functional approach.** Can you define W such that
   W > 0 for all subthreshold systems? Even a heuristic argument for why
   this should be true would clarify the program.

## Summary

The two-track restructuring is well-motivated and the EC-side results add
real substance to the program. The main gap is no longer "do we have explicit
obstruction results" (we do, on both sides) but "do we have a path to
universality." The disjunctive witness theorem is a reasonable target, but it
needs either a case-split predicate or a unified functional to become a
concrete research program rather than an aspiration.

The single highest-value question right now: does the global consequence of
entry conflict (not the raw overlap count) have nonzero forbidden mass? If yes,
the program may be simpler than it currently appears.