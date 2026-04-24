#!/usr/bin/env python3
"""
PA Domino Exploration 9: The RIGHT proof route.

Key realization: The sorry doesn't need to work with phases at all.
It needs `False` from the hypotheses. The hypotheses include `hconv` (convergence).

The approach: show the cycle can't have a valid transition function.
If ¬hasEntryConflict, then every proc p has disjoint mover/non-mover contexts.
The transition function at p maps (L,S,R) → f_p(L,S,R) where:
  - At mover step: f_p(L,S,R) ≠ S
  - At non-mover step: f_p(L,S,R) = S

Under ¬EC: these sets are disjoint, so f_p is well-defined.
But: does this always give a valid convergent system? NO — that's the gap.
The cycle might not be converging.

Actually, `hconv : converges sys gc` says the system WITH its transition function
converges. The sorry doesn't have `¬hasEntryConflict` — it needs to PRODUCE False.

Let me re-examine: the sorry has access to `entryConflict_impossible` which
maps hasEntryConflict → False. And it has `hconv`. Can it use hconv?

Actually, `entryConflict_impossible` doesn't use convergence. It uses the
transition function: f(L,S,R) ≠ S at mover steps, f(L,S,R) = S at non-mover
steps. If the same (L,S,R) appears at both, contradiction.

So: the sorry MUST show hasEntryConflict gc. Period.

Let me look for the right mechanism. The computational data shows EC is
universal. The question is: what's the clean proof?

Let me think about binary neighbors of ternary procs.

Alternative route: TERNARY NEIGHBOR.
Consider left(i) = ternary proc q with left(q) ternary/binary, right(q) = i (binary).
Context at q: (c_{left(q)}, c_q, c_i).
c_q has 3 values, c_i has 2 values.
c_{left(q)} has m_{left(q)} ≥ 2 values.

q fires fc(q) times (multiple of 3, ≥ 3).
In a sweep: fc(q) ≥ 3. Actually fc(q) could be 3.

Context space at q: m_{left(q)} * 3 * 2 = 6 * m_{left(q)}.
If left(q) is binary (which it's not — q = left(i), left(q) = left(left(i)),
and we have only 3 consecutive binary at {i, t, rr}, so left(i) is ternary,
and left(left(i)) could be anything):

For n ≥ 9 with 3 consecutive binary: n - 3 ≥ 6 ternary.
left(i) is ternary, left(left(i)) is ternary.
So context space at left(i): 3 * 3 * 2 = 18.

Cycle length L ≥ 3*2 + (n-3)*3 = 3n - 3.
For n = 9: L ≥ 24. But there are up to 18 contexts at q.
Not tight enough for direct pigeonhole.

Let me try YET ANOTHER approach.

SWEEP STRUCTURE:
In a sweep cycle, the movers visit processors in ring order.
For a zero-winding sweep: CW passes and CCW passes.
The total displacement is 0 but |displacement| ≥ 2n.

In a sweep, the mover word has a specific structure:
alternating CW and CCW sweeps through the ring.
Each CW pass: ..., i-1, i, t, rr, rr+1, ...
Each CCW pass: ..., rr+1, rr, t, i, i-1, ...

In a CW pass through t:
- i fires, then t fires, then rr fires (consecutive in sweep)
- Context at t when t fires: c_i just changed (i fired), c_rr unchanged

In a CCW pass through t:
- rr fires, then t fires, then i fires
- Context at t when t fires: c_rr just changed, c_i unchanged

NOW: consider the NON-MOVER context at t right BEFORE t fires in a CW pass.
The step right before t fires is when i fires.
At that step (i fires): context at t = (c_i_old, c_t_current, c_rr_current).
Here c_i_old is i's value BEFORE i fires (will change to c_i_new).
c_t_current is t's value (didn't fire yet).

And when t fires (next step): context at t = (c_i_new, c_t_current, c_rr_current).

These differ in L only (c_i_old vs c_i_new). Since i is binary: c_i_new = (c_i_old+1)%2.

So the non-mover context at t (when i fires) is:
  ((c_i_new+1)%2, c_t, c_rr) = (c_i_old, c_t, c_rr)
And the mover context at t (when t fires):
  (c_i_new, c_t, c_rr)

These have complementary L values. So they NEVER match. Good — consistent
with the parity obstruction.

What about the step RIGHT AFTER t fires (next is rr fires in CW)?
After t fires: c_t changes. So at rr's fire step:
  Context at t = (c_i_new, c_t_new, c_rr_old).
Is this ever equal to a mover context at t at some other fire step?

At another t-fire (say in CCW): context = (c_i_at_ccw, c_t_at_ccw, c_rr_at_ccw).
For match: need c_i_new = c_i_at_ccw, c_t_new = c_t_at_ccw, c_rr_old = c_rr_at_ccw.

This is the post-fire observation. And we showed computationally that this
sometimes gives EC at t.

OK let me step way back and think about this differently.
"""

# The fundamental issue: the sorry has n ≥ 9, sub-threshold, 3 consecutive binary,
# isolated t, odd parity, dispatch failure. We need EC at ANY proc.
#
# Maybe the right approach is: DON'T try to find EC at a specific proc.
# Instead, use a GLOBAL argument.
#
# Global pigeonhole: total context observations across ALL procs = n * L.
# Total context space = sum over p of (m_{left(p)} * m_p * m_{right(p)}).
# For sub-threshold: product of m_p < 4 * 3^(n-2).
# Context space at p: m_{left(p)} * m_p * m_{right(p)}.
# Sum of context spaces ≤ n * max context space.
#
# This is getting nowhere. Let me think about what SPECIFIC structural property
# of the sorry branch forces EC.

# OBSERVATION from the data:
# At n=5, ms=[3,2,2,2,3], ALL zero-winding cycles have EC at i and at left(i).
# NOT just the sorry branch — ALL cycles!

# This means: with 3 consecutive binary, EC is forced regardless of the
# isolated/parity/dispatch conditions. The sorry branch is actually a SUBSET
# of a case where EC is always forced.

# Can we prove EC at i (or left(i)) for ANY good cycle with 3 consecutive binary
# and sub-threshold product?

# If yes: the sorry becomes trivial — just apply that theorem.

# Let me check: is EC at i universal for ALL zero-winding cycles
# (not just the sorry branch)?

from collections import Counter

def check_universal_ec(n, ms, proc, max_cycles=5000):
    """Check if EC at proc is universal for all zero-winding cycles."""
    start = tuple(0 for _ in range(n))
    results = []

    def dfs(word, fc, config):
        if len(results) >= max_cycles: return
        if len(word) > 6*n: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                return
        remaining = 6*n - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        for nxt in range(n):
            if abs(nxt - word[-1]) % n not in [1, n-1]: continue
            if len(results) >= max_cycles: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= max_cycles: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if j==p else 0 for j in range(n)], tuple(first))

    def winding(w):
        wd = 0
        for idx in range(len(w)):
            d = (w[(idx+1)%len(w)] - w[idx]) % n
            if d == 1: wd += 1
            elif d == n-1: wd -= 1
        return wd

    zw = [w for w in results if winding(w) == 0]

    has_ec = 0
    no_ec = 0
    no_ec_examples = []
    for word in zw:
        ell = len(word)
        cfgs = [list(start)]
        for idx in range(ell):
            c = list(cfgs[-1])
            c[word[idx]] = (c[word[idx]] + 1) % ms[word[idx]]
            cfgs.append(c)

        m_ctx = set()
        n_ctx = set()
        found = False
        for s in range(ell):
            ctx = (cfgs[s][(proc-1)%n], cfgs[s][proc], cfgs[s][(proc+1)%n])
            if word[s] == proc:
                if ctx in n_ctx: found = True; break
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: found = True; break
                n_ctx.add(ctx)

        if found:
            has_ec += 1
        else:
            no_ec += 1
            if len(no_ec_examples) < 3:
                no_ec_examples.append((word, sorted(m_ctx), sorted(n_ctx)))

    return len(zw), has_ec, no_ec, no_ec_examples

print("="*70)
print("IS EC AT SPECIFIC PROCS UNIVERSAL (ALL ZW CYCLES)?")
print("="*70)

# Check at i, t, rr, left(i), right(rr)
for n, ms, bt in [
    (5, [2,2,2,3,3], (0,1,2)),
    (5, [3,2,2,2,3], (1,2,3)),
    (7, [3,3,2,2,2,3,3], (2,3,4)),
]:
    i_pos, t_pos, rr_pos = bt
    li_pos = (i_pos - 1) % n
    rrr_pos = (rr_pos + 1) % n
    print(f"\nn={n}, ms={ms}, binary={bt}")

    for proc, name in [(i_pos, 'i'), (t_pos, 't'), (rr_pos, 'rr'),
                        (li_pos, 'left(i)'), (rrr_pos, 'right(rr)')]:
        total, ec, no_ec, examples = check_universal_ec(n, ms, proc)
        status = "UNIVERSAL" if no_ec == 0 else f"FAILS ({no_ec} counterexamples)"
        print(f"  EC at {name}={proc} (m={ms[proc]}): {status} [{ec}/{total}]")
        for word, mc, nc in examples[:1]:
            print(f"    Example: len={len(word)}, |mover|={len(mc)}, |nonmover|={len(nc)}")
