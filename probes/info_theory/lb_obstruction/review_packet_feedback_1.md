# Spectral Transport Lower Bound Program

Date: April 6, 2026
Status: Research roadmap — working document

## Goal

Prove a lower bound on the state product M_n of valid self-stabilizing token
rings using purely information-theoretic (ANOVA / spectral) methods. No
combinatorial shadow machinery as a dependency. The explicit-family obstruction
results become corollaries or motivating evidence, not load-bearing components.

## The Three-Piece Argument

The full lower bound has exactly three pieces. All three must be proved cleanly
and all three must stay within the spectral / product-measure framework.

### Piece 1: Target Signature Lemma

**Statement (to be proved):**
For any valid self-stabilizing token ring on n processors with state vector
(m_1, ..., m_n), the indicator of the legitimate good cycle satisfies

ForbidFrac_{w}(chi_good) >= F(n, M_n)

for some explicit function F that is bounded away from zero when M_n is
subthreshold.

**What we need to know:**

- What is the ANOVA decomposition of chi_good for known valid systems? We have
  FutureFc values on the valid side already. Compute chi_good directly for
  CUP-2 and any other known valid families.
- Does the forbidden fraction of chi_good depend primarily on M_n, or does the
  internal structure of the system matter a lot? If it depends heavily on
  structure, this piece is hard. If it's mostly controlled by M_n and n, we have
  a clean target.
- Key test: compute ForbidFrac_{n-2}(chi_good) for every known valid system
  through n = 7. Tabulate alongside M_n. Look for a pattern.

**Risk:** This might be the weakest piece. The good cycle is a very specific
combinatorial object, and its spectral signature might not be tightly controlled
by M_n alone.

**Fallback:** If chi_good itself doesn't work, consider proxies: the privilege
indicator (exactly one processor privileged), or the convergence-time indicator
(number of steps to reach the good cycle from a given configuration). Either
might have a more regular spectral signature.

### Piece 2: Spectral Transport Lemma

**Statement (to be proved):**
Let T_i denote the local transition map induced by processor i's update rule,
acting on scalars over the configuration space. Then for any scalar f,

|ForbidFrac_w(T_i f) - ForbidFrac_w(f)| <= G(m_{i-1}, m_i, m_{i+1}, n)

for some explicit bound G that depends only on the local state sizes and n.

Equivalently: one local update step can shift at most G units of L^2 energy
between forbidden and permitted interaction subspaces.

**This is the core lemma.** Everything else is setup and bookkeeping. This is
where the information-theoretic content actually lives.

**What we need to know:**

- Start with the simplest case. Take n = 5, a single processor with states in
  {0,1,2}, width-3 window. Pick a concrete transition function. Apply T_i to
  several test scalars and compute the before/after ANOVA decomposition. How
  much energy actually moves across the forbidden boundary?
- Is the bound tight or loose? If a single local update can move almost all the
  forbidden energy into permitted subspaces, the lemma is true but useless — the
  bound G is too large to yield a contradiction. We need G to be small relative
  to the target F from Piece 1.
- The key structural reason this should work: T_i acts nontrivially only on
  coordinates {i-1, i, i+1}. On the ANOVA side, this means T_i can only
  redistribute energy among interaction terms whose support intersects
  {i-1, i, i+1}. It cannot create energy on a support S from energy on a
  support S' if S and S' are both disjoint from {i-1, i, i+1}. This gives a
  locality constraint on spectral transport.
- The subtlety: T_i can convert energy on support {i-1, i} into energy on
  support {i-1, i, i+1, j} for any j, because the nonlinearity of the map
  mixes things. So the question is how much energy can leak from low-order to
  high-order interactions through the nonlinearity of a single local step.
- This might factor into: (a) a linear part of T_i that preserves ANOVA
  structure cleanly, and (b) a nonlinear residual that is controlled by the
  local state sizes. If m_i is small, the nonlinear residual is large relative
  to the linear part, meaning more energy can leak — which is the wrong
  direction. Think about this carefully.

**Concrete first computation:**
Take the CUP-2 system at n = 5. Pick a scalar f with known ANOVA decomposition
(e.g., a pure interaction term on a forbidden support). Apply one full round of
local updates. Measure how much forbidden energy survives. Repeat for several
choices of f. This gives an empirical bound on G and tells us whether the lemma
has enough bite.

**Risk:** The nonlinearity of local maps might be too strong — G might scale
badly with local state size, killing the contradiction. This is the make-or-
break question for the entire program.

### Piece 3: Convergence Contradicts Transport

**Statement (to be proved):**
Validity requires that iterated application of local updates drives every
initial configuration to the good cycle. By Piece 1, the good cycle indicator
has forbidden fraction at least F. By Piece 2, each step moves forbidden energy
by at most G. Starting from an initial scalar with known (possibly zero)
forbidden fraction, reaching a target with forbidden fraction F requires at
least F/G steps — or requires the state product to be large enough that G is
not small.

**This piece is mostly bookkeeping once Pieces 1 and 2 are in hand.** The main
work is:

- Making the iteration argument precise. The system is nondeterministic (daemon
  schedules), so we need the transport bound to hold for every schedule, not
  just a specific one.
- Handling the fact that T_i is not a contraction in general. The forbidden
  fraction might oscillate, not decrease monotonically. So the argument might
  need to track total energy flow rather than a monotone potential.
- Getting quantitative control: the final bound on M_n comes from the interplay
  between F and G. We need F/G to grow with n to get a nontrivial asymptotic
  lower bound.

## Immediate Priorities

Ordered by information value, not difficulty.

1. **Compute the spectral transport of a single local update empirically.**
   Take CUP-2 at n = 5. Apply T_i to pure forbidden-support interaction terms.
   Measure energy redistribution. This tells us within a day whether Piece 2
   has any chance of working.

2. **Compute ForbidFrac_{n-2}(chi_good) for all known valid systems through
   n = 7.** We have FutureFc values but not chi_good values. These might differ
   substantially. We need the actual target.

3. **Write down the ANOVA structure of T_i abstractly.** Before trying to prove
   the spectral transport lemma, work out what T_i does to a general ANOVA
   component symbolically. The map is: take f, restrict to the fiber where
   (c_{i-1}, c_i, c_{i+1}) are fixed, apply the transition, extend back. This
   is a conditional expectation composed with a permutation on one coordinate.
   The ANOVA interaction structure of this composition should be computable.

4. **If (1) looks promising:** formalize the transport bound. Aim for a clean
   upper bound on G in terms of m_i and n.

5. **If (1) looks unpromising:** determine whether the failure is fundamental
   (local maps really can move arbitrary amounts of forbidden energy) or an
   artifact of CUP-2 being a small system. Test on a larger system before
   abandoning.

## What the Existing Explicit-Family Results Become

If the transport program works, the explicit-family obstruction results from the
review packet become:

- **Evidence that Piece 1 is plausible.** The shadow indicators have large
  forbidden mass. If the good cycle indicator also has large forbidden mass for
  subthreshold systems (which is related but not identical), the explicit-family
  computations are supporting evidence.
- **Test cases for Piece 2.** The transport lemma should be verifiable on the
  same systems where we already have exact ANOVA data.
- **Not load-bearing.** The 71/504 floor, the class-by-class exact values, the
  assignment-invariance — none of these are needed in the final argument. They
  motivated the program. They don't appear in the proof.

## Key Risks

- **Piece 2 might fail quantitatively.** The spectral transport lemma might be
  true but with a bound G that is too large. This is the most likely failure
  mode. Detect it early via computation.
- **Piece 1 might require combinatorial input.** The forbidden fraction of
  chi_good might depend on structural properties of the good cycle that don't
  reduce to M_n. If so, we'd need at least some combinatorial lemma to feed the
  spectral argument, compromising purity.
- **The daemon nondeterminism in Piece 3 might be hard to handle.** Worst-case
  daemon schedules might be able to game the spectral transport in ways that
  break a naive iteration argument.

## Success Criteria

The program succeeds if it yields a theorem of the form:

> For any valid self-stabilizing token ring on n processors,
> M_n >= h(n)
> where h(n) -> infinity with n.

Even h(n) = Omega(n) would be significant. The exact constant matters less than
getting any superlinear growth purely from spectral methods.

The program partially succeeds if it yields:

> For any valid system with state vector in {2,3}^n, M_n >= h(n).

This would still be new and interesting but would rely on the state-size
restriction to control Piece 1 or Piece 2.