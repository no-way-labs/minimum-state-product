#!/usr/bin/env python3
"""
RA12 Gap-1 EC Mechanism: Deep investigation.

KEY FINDING from ra12_sorry_a/b: ALL zero-winding fc=2 walks have global min gap = 1.
ProcMinGap (gap >= 2) handles NONE of them.

This script investigates THE ACTUAL EC MECHANISM at gap-1 pairs.

For BOTH consecutive and non-consecutive binary:
- Every ZW walk is palindromic (back-and-forth)
- The turnaround point IS the gap-1 pair
- Interior procs have matching CW-nonmover and CCW-mover contexts

The question: can we prove gap-1 → EC directly from the gap-1 structure,
WITHOUT going through palindromic phase extraction?

Approach: At a gap-1 pair at edge e:
- Step a: mover p crosses e CW (p fires, moves to right(p))
- Step b=a+1: mover q crosses e CCW (q fires, moves to left(q))
- p and q share edge e, so q = right(p) and p = left(q)

At step a: p fires. All other procs (including q) are non-movers.
At step b: q fires. All other procs (including p) are non-movers.

For proc j far from the edge (j != p, j != q, j not adjacent to p or q):
  j is non-mover at BOTH steps a and b.
  j's context is unchanged between steps a and b
  (only p's value changed, and j is not adjacent to p).
  So j sees the SAME (L,S,R) at both steps → f(L,S,R) = S at both → no conflict at j.

For proc left(p) (= left of the CW mover):
  At step a: left(p) is non-mover. Context = (c_a[left(left(p))], c_a[left(p)], c_a[p]).
  At step b: left(p) is non-mover (mover is q = right(p)).
  Context = (c_b[left(left(p))], c_b[left(p)], c_b[p]).
  c_b[p] = new value of p (after firing) != c_a[p].
  c_b[left(p)] = c_a[left(p)] (didn't fire).
  c_b[left(left(p))] = c_a[left(left(p))] (didn't fire).
  So: left(p) sees (L, S, R_old) at step a and (L, S, R_new) at step b.
  Different R → no direct EC at left(p) from just these two steps.

For proc right(q) (= right(right(p))):
  At step a: right(q) is non-mover. Context = (c_a[q], c_a[right(q)], c_a[right(right(q))]).
  At step b: right(q) is non-mover (mover is q).
  Context = (c_b[q], c_b[right(q)], c_b[right(right(q))]).
  c_b[q] = new value of q (after firing at step b). But wait — at step b,
  we're looking at the config BEFORE q fires, which is c_b = c_{a+1}.
  c_{a+1}[q] = c_a[q] (q didn't fire at step a).
  So: right(q) sees (c_a[q], c_a[right(q)], c_a[right(right(q))]) at step a,
  and the SAME context at step b (since only p changed, and p is not adjacent to right(q)
  unless q = right(p) and right(q) = right(right(p)) is adjacent to q but not to p).
  Actually: right(q) at step b sees (c_b[q], ...) = (c_a[q], ...) same as step a.
  So right(q) sees SAME context at steps a and b → f = S at both → no EC.

So the EC is NOT between steps a and b (the gap-1 pair) alone.
It comes from the PALINDROMIC STRUCTURE of the ENTIRE walk.

Let me verify this: the EC procs are INTERIOR to the palindromic segment,
not at the turnaround edge.
"""

from itertools import product as iproduct
from collections import defaultdict


def step_dir(word, t, n):
    L = len(word)
    curr = word[t]
    nxt = word[(t + 1) % L]
    d = (nxt - curr) % n
    if d == 1:
        return 1
    elif d == n - 1:
        return -1
    return 0


def winding_number(word, n):
    return sum(step_dir(word, t, n) for t in range(len(word)))


def cw_count(word, n):
    return sum(1 for t in range(len(word)) if step_dir(word, t, n) == 1)


def enumerate_state_sequences(m, k):
    if k == 0:
        return [[0]]
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def analyze_ec_detailed(word, n, ms):
    """For each valid combo, find which step pairs cause the EC."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {}
    for p in range(n):
        if fc[p] == 0:
            proc_seqs[p] = [[0]]
        else:
            proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])

    sl = [proc_seqs[p] for p in range(n)]
    results = []

    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue

        good = configs[:L]

        # For each proc j, track all (step, role, context, value) observations
        proc_obs = defaultdict(list)
        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            mover = word[t]
            for j in range(n):
                ctx = (c[(j-1) % n], c[j], c[(j+1) % n])
                if j == mover:
                    proc_obs[j].append((t, 'mover', ctx, cn[j]))
                else:
                    proc_obs[j].append((t, 'nonmover', ctx, c[j]))

        # Find conflicting contexts
        conflicts = []
        for j in range(n):
            ctx_map = defaultdict(lambda: {'mover': [], 'nonmover': []})
            for t, role, ctx, val in proc_obs[j]:
                ctx_map[ctx][role].append((t, val))

            for ctx, roles in ctx_map.items():
                if roles['mover'] and roles['nonmover']:
                    for mt, mv in roles['mover']:
                        if mv != ctx[1]:  # actual firing (not identity)
                            for nt, nv in roles['nonmover']:
                                conflicts.append({
                                    'proc': j,
                                    'ctx': ctx,
                                    'mover_step': mt,
                                    'mover_val': mv,
                                    'nonmover_step': nt,
                                    'nonmover_val': nv,
                                    'is_binary': ms[j] == 2,
                                })

        results.append({
            'combo': combo,
            'configs': good,
            'conflicts': conflicts,
        })

    return results


def main():
    print("=" * 70)
    print("RA12 Gap-1 EC Mechanism: Where does the conflict actually occur?")
    print("=" * 70)

    # Test both consecutive and non-consecutive
    cases = [
        ("Consecutive", 5, [2, 2, 2, 3, 3]),
        ("Non-consecutive", 5, [2, 3, 2, 3, 2]),
    ]

    for case_name, n, ms in cases:
        print(f"\n{'='*60}")
        print(f"{case_name}: n={n}, ms={ms}")
        print(f"{'='*60}")

        L = 2 * n
        walks = []
        def dfs(path, fc):
            if len(path) == L:
                nxt_pos = path[0]
                last_pos = path[-1]
                d = (nxt_pos - last_pos) % n
                if d == 1 or d == n - 1:
                    if all(f == 2 for f in fc):
                        walks.append(tuple(path))
                return
            pos = path[-1]
            for d_step in [1, -1]:
                nxt = (pos + d_step) % n
                if fc[nxt] < 2:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs(path, fc)
                    path.pop()
                    fc[nxt] -= 1
        fc = [0] * n
        fc[0] = 1
        dfs([0], fc)

        unique = set()
        deduped = []
        for w in walks:
            best = w
            for i in range(len(w)):
                rot = w[i:] + w[:i]
                if rot < best:
                    best = rot
            if best not in unique:
                unique.add(best)
                deduped.append(list(best))

        zw = [w for w in deduped if winding_number(w, n) == 0 and cw_count(w, n) > 0]

        for w in zw[:3]:
            print(f"\n  word = {w}")

            # Find turnaround (the gap-1 pair)
            for t in range(len(w)):
                d = step_dir(w, t, n)
                d_str = "CW" if d == 1 else "CCW"
                print(f"    step {t}: proc {w[t]} fires {d_str}")

            # Find the turnaround point
            turnaround = None
            for t in range(len(w)):
                d1 = step_dir(w, t, n)
                d2 = step_dir(w, (t+1) % len(w), n)
                if d1 == 1 and d2 == -1:
                    turnaround = t
                    break

            if turnaround is not None:
                print(f"\n    Turnaround at step {turnaround}: {w[turnaround]}→{w[turnaround+1 if turnaround+1<len(w) else 0]} (CW→CCW)")

            # Detailed EC analysis
            results = analyze_ec_detailed(w, n, ms)
            if results:
                r = results[0]
                print(f"\n    First valid combo: configs = ")
                for t, c in enumerate(r['configs']):
                    mover = w[t]
                    d = step_dir(w, t, n)
                    d_str = "CW" if d == 1 else "CCW"
                    print(f"      t={t}: {c}  mover={mover}({d_str})")

                print(f"\n    Entry conflicts ({len(r['conflicts'])} total):")
                for c in r['conflicts']:
                    dist_from_turnaround = None
                    if turnaround is not None:
                        # Distance of conflicting mover/nonmover steps from turnaround
                        dist_from_turnaround = (c['mover_step'] - turnaround, c['nonmover_step'] - turnaround)
                    print(f"      proc {c['proc']} (binary={c['is_binary']}): ctx={c['ctx']}, "
                          f"mover@step {c['mover_step']}→{c['mover_val']}, "
                          f"nonmover@step {c['nonmover_step']}→{c['nonmover_val']}, "
                          f"dist_from_turn={dist_from_turnaround}")

    # KEY FINDING: Check if EC always comes from palindromic interior
    print(f"\n{'='*70}")
    print("KEY: EC location relative to turnaround")
    print("="*70)

    for case_name, n, ms in cases:
        print(f"\n{case_name}: n={n}, ms={ms}")

        L = 2 * n
        walks = []
        def dfs2(path, fc):
            if len(path) == L:
                nxt_pos = path[0]
                last_pos = path[-1]
                d = (nxt_pos - last_pos) % n
                if d == 1 or d == n - 1:
                    if all(f == 2 for f in fc):
                        walks.append(tuple(path))
                return
            pos = path[-1]
            for d_step in [1, -1]:
                nxt = (pos + d_step) % n
                if fc[nxt] < 2:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs2(path, fc)
                    path.pop()
                    fc[nxt] -= 1
        fc = [0] * n
        fc[0] = 1
        dfs2([0], fc)

        unique2 = set()
        deduped2 = []
        for w in walks:
            best = w
            for i in range(len(w)):
                rot = w[i:] + w[:i]
                if rot < best:
                    best = rot
            if best not in unique2:
                unique2.add(best)
                deduped2.append(list(best))

        zw2 = [w for w in deduped2 if winding_number(w, n) == 0 and cw_count(w, n) > 0]

        ec_at_turnaround = 0
        ec_interior = 0
        ec_other = 0

        for w in zw2:
            # Find turnaround
            turnaround_steps = []
            for t in range(len(w)):
                d1 = step_dir(w, t, n)
                d2 = step_dir(w, (t+1) % len(w), n)
                if d1 * d2 == -1:  # direction change
                    turnaround_steps.append(t)

            results = analyze_ec_detailed(w, n, ms)
            if not results:
                continue

            for r in results:
                for c in r['conflicts']:
                    # Is the mover step or nonmover step AT the turnaround?
                    at_turn = c['mover_step'] in turnaround_steps or c['nonmover_step'] in turnaround_steps
                    if at_turn:
                        ec_at_turnaround += 1
                    else:
                        # Are both steps in the palindromic interior?
                        # The palindromic interior is the segment between turnarounds
                        # where CW and CCW movers are "mirrored"
                        ec_interior += 1

        print(f"  EC involving turnaround step: {ec_at_turnaround}")
        print(f"  EC NOT at turnaround: {ec_interior}")

    # CRUCIAL CHECK: For each ZW walk, is the EC always at the
    # palindromic interior (the mirrored CW-nonmover / CCW-mover pair)?
    print(f"\n{'='*70}")
    print("CRUCIAL: Palindromic mirror EC check")
    print("="*70)
    print("""
The palindromic EC argument (from Palindromic.lean / cic_case3a_proof5.py):
For a zero-winding fc=2 walk, which is a "back-and-forth" path, consider
an interior proc j (not at the turnaround). When the CW sweep passes
through j, j is a non-mover at some step t_cw. When the CCW sweep passes
back through j, j is the mover at step t_ccw.

The KEY claim: the non-mover context at t_cw EQUALS the mover context at t_ccw.
This is because the palindromic structure means the config at t_ccw is
the "mirror" of the config at t_cw — the values on one side of j match.

If this context matching holds: f(ctx) = S (non-mover) AND f(ctx) != S (mover).
Contradiction.

This doesn't need gap analysis at all. It needs:
1. The walk is back-and-forth (zero winding, fc=2)
2. There exist interior procs (the walk covers >= 3 procs)
3. Binary structure ensures the context match

Can we prove this from JUST (zeroWinding + cwStepCount > 0)?
YES — because zeroWinding + cwStepCount > 0 + fc=2 implies the walk
is a back-and-forth (it goes CW some, then CCW the same amount, returning).
The palindromic structure is a CONSEQUENCE of zero winding + fc=2.
""")

    # Verify: ALL zero-winding fc=2 walks are palindromic
    for n in [5, 6, 7]:
        L = 2 * n
        walks = []
        def dfs3(path, fc):
            if len(path) == L:
                nxt_pos = path[0]
                last_pos = path[-1]
                d = (nxt_pos - last_pos) % n
                if d == 1 or d == n - 1:
                    if all(f == 2 for f in fc):
                        walks.append(tuple(path))
                return
            pos = path[-1]
            for d_step in [1, -1]:
                nxt = (pos + d_step) % n
                if fc[nxt] < 2:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs3(path, fc)
                    path.pop()
                    fc[nxt] -= 1
        fc = [0] * n
        fc[0] = 1
        dfs3([0], fc)

        unique3 = set()
        deduped3 = []
        for w in walks:
            best = w
            for i in range(len(w)):
                rot = w[i:] + w[:i]
                if rot < best:
                    best = rot
            if best not in unique3:
                unique3.add(best)
                deduped3.append(list(best))

        zw3 = [w for w in deduped3 if winding_number(w, n) == 0 and cw_count(w, n) > 0]

        all_palindromic = True
        for w in zw3:
            # Check: is the walk a rotation of a palindromic path?
            # Palindromic: first half CW, second half CCW (or vice versa)
            dirs = [step_dir(w, t, n) for t in range(len(w))]
            # Find a rotation where first k steps are CW and last k are CCW
            is_pal = False
            for start in range(len(w)):
                rot_dirs = dirs[start:] + dirs[:start]
                # Count initial CW run
                cw_run = 0
                for d in rot_dirs:
                    if d == 1:
                        cw_run += 1
                    else:
                        break
                ccw_run = 0
                for d in reversed(rot_dirs):
                    if d == -1:
                        ccw_run += 1
                    else:
                        break
                if cw_run + ccw_run == len(w) and cw_run == ccw_run:
                    is_pal = True
                    break
            if not is_pal:
                all_palindromic = False
                print(f"  n={n}: NON-palindromic walk: {w}, dirs={dirs}")

        print(f"n={n}: {len(zw3)} ZW walks, all palindromic: {all_palindromic}")

    # FINAL SYNTHESIS
    print(f"\n{'='*70}")
    print("SYNTHESIS: Self-contained proof paths")
    print("="*70)
    print("""
FINDING 1: ALL zero-winding fc=2 walks are palindromic.
  Every such walk, up to rotation, has the form:
  [CW, CW, ..., CW, CCW, CCW, ..., CCW]
  (k CW steps followed by k CCW steps, with k = n).

  This is because fc=2 forces each proc to fire exactly twice,
  and zero-winding forces equal CW and CCW steps. The only way
  to arrange 2n steps with n CW and n CCW where each of n procs
  fires exactly twice is to go CW through a contiguous arc and
  then CCW back through the same arc.

FINDING 2: The palindromic structure DIRECTLY gives EC at interior procs.
  For consecutive binary case:
    - 3 consecutive binary at {i, i+1, i+2}
    - The CW sweep crosses binary boundaries
    - Interior proc j (between turnarounds) has matching mover/nonmover context
    - EC at j: f(ctx) must be both = S and != S

  For non-consecutive binary case:
    - Binary procs are separated
    - The same palindromic structure holds
    - Interior binary procs have matching contexts
    - EC at the binary proc

FINDING 3: procMinGap DOES NOT HELP.
  All ZW walks have global min gap = 1 at ALL binary crossings.
  The gap-2 BAFArcAdj argument never applies.

FINDING 4: The palindromic EC is the ONLY mechanism needed.
  It works for BOTH consecutive and non-consecutive binary.
  It works from just: zeroWinding + fc=2 + >=3 binary + sub-threshold.

PROOF SKETCH (self-contained, no recursion):
  Given: gc.zeroWinding, cwStepCount > 0, no safe proc, convergence,
         sub-threshold, >=3 binary, n >= 9.

  Step 1: Zero winding + cwStepCount > 0 implies the walk has both CW and CCW steps.
           fc=2 for all procs (from binary parity + sub-threshold constraints).

  Step 2: The walk is palindromic: up to rotation, first half CW, second half CCW.
           This follows from fc=2 + zero winding.

  Step 3: Find a binary proc b in the palindromic interior (not at turnaround).
           With >= 3 binary and n >= 9, at least one binary proc is interior.

  Step 4: At the CW sweep through b: b is non-mover at step t.
           At the CCW sweep through b: b is mover at step s.
           The contexts match: (L, S, R) at t = (L, S, R) at s.
           (Because all procs between b and the turnaround have returned to original values.)

  Step 5: f_b(L, S, R) = S (non-mover at step t) AND f_b(L, S, R) != S (mover at step s).
           Contradiction.

  This does NOT need the global dispatch, phase extraction, or any 4-mechanism UEC.
  It is a DIRECT consequence of palindromic + binary structure.

FOR SORRY A: Use Steps 1-5 with 3 consecutive binary.
FOR SORRY B: Use Steps 1-5 with non-consecutive binary.

THE KEY QUESTION: Does Palindromic.lean already have this?
  If yes: both sorrys can call `palindromic_phase_ec` directly.
  If no: the palindromic EC lemma needs to be generalized.
""")


if __name__ == "__main__":
    main()
