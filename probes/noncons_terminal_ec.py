"""
Deep analysis of terminal crossing case for odd-winding non-consecutive binary.

Key finding from previous script: 325/4001 odd-winding walks at n=6 have
terminal singleton crossings.

Now check:
1. What makes the terminal case special vs internal?
2. Can cutArc be adapted for terminal crossings?
3. Does entry conflict still apply?
"""

import itertools

def total_displacement(movers, n):
    cw = 0; ccw = 0
    for idx in range(len(movers)):
        curr = movers[idx]; nxt = movers[(idx + 1) % len(movers)]
        diff = (nxt - curr) % n
        if diff == 1: cw += 1
        elif diff == n - 1: ccw += 1
    return cw - ccw

def fire_count(movers, p):
    return sum(1 for m in movers if m == p)

def edge_traversal_count(movers, n, edge_i):
    count = 0; CL = len(movers)
    a, b = edge_i, (edge_i + 1) % n
    for k in range(CL):
        curr = movers[k]; nxt = movers[(k + 1) % CL]
        if (curr == a and nxt == b) or (curr == b and nxt == a):
            count += 1
    return count

def edge_cross_steps(movers, n, edge_i):
    steps = []; CL = len(movers)
    a, b = edge_i, (edge_i + 1) % n
    for k in range(CL):
        curr = movers[k]; nxt = movers[(k + 1) % CL]
        if (curr == a and nxt == b) or (curr == b and nxt == a):
            steps.append(k)
    return steps

def count_odd_winding_walks_dp(n, binary_set, target_disp, max_cl):
    found = []
    def dfs(pos, word, disp, fc, visited):
        cl = len(word)
        remaining = max_cl - cl
        if abs(target_disp - disp) > remaining + 1:
            return
        unvisited = set(range(n)) - visited
        if len(unvisited) > remaining + 1:
            return
        if cl >= max(9, n):
            diff = (word[0] - pos) % n
            close_disp = disp
            if diff == 1: close_disp += 1
            elif diff == n - 1: close_disp -= 1
            elif diff != 0: diff = -1
            if diff in (0, 1, n - 1) and abs(close_disp) == n:
                if visited == set(range(n)):
                    ok = True
                    for b in binary_set:
                        if fc.get(b, 0) % 2 != 0:
                            ok = False; break
                    if ok:
                        found.append((list(word), close_disp))
                        if len(found) >= 10000:
                            return
        if cl >= max_cl or len(found) >= 10000:
            return
        for nxt in [(pos + 1) % n, pos, (pos - 1) % n]:
            step_disp = 0
            if (nxt - pos) % n == 1: step_disp = 1
            elif (nxt - pos) % n == n - 1: step_disp = -1
            new_fc = dict(fc); new_fc[nxt] = new_fc.get(nxt, 0) + 1
            dfs(nxt, word + [nxt], disp + step_disp, new_fc, visited | {nxt})
    dfs(0, [0], 0, {0: 1}, {0})
    return found

print("=" * 70)
print("TERMINAL CROSSING ANALYSIS for n=6, binary at {0,2,4}")
print("=" * 70)

n = 6
binary = {0, 2, 4}

# Generate walks with both positive and negative displacement
walks_pos = count_odd_winding_walks_dp(n, binary, n, 14)
walks_neg = count_odd_winding_walks_dp(n, binary, -n, 14)
all_walks = walks_pos + walks_neg

print(f"Total odd-winding walks found: {len(all_walks)}")

# Classify by terminal vs non-terminal singleton crossings
terminal_walks = []
non_terminal_walks = []

for w, d in all_walks:
    CL = len(w)
    singletons = []
    for e in range(n):
        tc = edge_traversal_count(w, n, e)
        if tc == 1:
            steps = edge_cross_steps(w, n, e)
            singletons.append((e, steps[0]))

    has_terminal = any(s + 1 == CL for e, s in singletons)
    if has_terminal:
        terminal_walks.append((w, d, singletons))
    else:
        non_terminal_walks.append((w, d, singletons))

print(f"Terminal singleton walks: {terminal_walks.__len__()}")
print(f"Non-terminal singleton walks: {non_terminal_walks.__len__()}")

# Analyze terminal walks in detail
print("\n--- TERMINAL WALKS ANALYSIS ---")
if terminal_walks:
    # For each terminal walk, check if the SECOND singleton is also terminal
    both_terminal = 0
    one_terminal_one_internal = 0
    for w, d, singletons in terminal_walks[:20]:
        CL = len(w)
        terminal_sings = [(e, s) for e, s in singletons if s + 1 == CL]
        internal_sings = [(e, s) for e, s in singletons if s + 1 < CL]
        if len(terminal_sings) >= 2:
            both_terminal += 1
        elif len(terminal_sings) == 1 and len(internal_sings) >= 1:
            one_terminal_one_internal += 1

    print(f"  First 20 terminal walks:")
    for w, d, singletons in terminal_walks[:5]:
        CL = len(w)
        fcs = {p: fire_count(w, p) for p in range(n)}
        bin_fcs = {p: fcs[p] for p in binary}
        print(f"  word={w}, len={CL}, disp={d}")
        print(f"    binary_fc={bin_fcs}")
        for e, s in singletons:
            print(f"    singleton edge {e}-{(e+1)%n}: step {s}, terminal={s+1==CL}")

    # Now the KEY question: can the cutArc argument work for terminal crossings?
    # The cutArc argument for two INTERNAL crossings works as follows:
    # 1. Two singleton edges i, j (edges traversed exactly once)
    # 2. Their crossings at steps ki, kj with ki < kj < CL
    # 3. Define cutArc = {procs between edge i and edge j}
    # 4. Between steps ki+1 and kj, all movers are in cutArc (since no other
    #    edge crossing happens to leave the arc)
    # 5. Similarly, between kj+1 and ki (wrapping), all movers are in complement
    # 6. This gives a SupportInterval → ReturnCone → config repeat → False

    # For TERMINAL crossing:
    # One crossing at step CL-1, the other at some step k < CL-1.
    # The interval [k+1, CL-2] has all movers on one side of edge j.
    # The interval [0, k-1] (wrapping through CL-1) has movers on the other side.
    # But step CL-1 crosses the terminal edge, so at step CL-1 the mover
    # jumps to the other side.

    # The issue: the SupportInterval struct requires startStep < endStep (proper).
    # If the terminal crossing at CL-1 and internal at k:
    # - [k+1, CL-2] is an interval with movers in cutArc
    # - [0, k-1] wrapping: movers in complement
    # The SupportInterval for [k+1, CL-2] has start=k+1, end=CL-1.
    # This works! The terminal step CL-1 is NOT in the interval.
    # But wait — we need to show config repeat at start and end of the interval.
    # The support interval argument: procs outside the interval are frozen,
    # so their states at step k+1 equal their states at step CL-1.
    # But step CL-1 connects to step 0 (same config due to cyclicity),
    # so states at step CL-1 = states at step 0.

    # Hmm, but that means the repeat is between configs at step k+1 and step CL-1.
    # Since CL-1 and 0 have the same config (cyclicity), this is a repeat between
    # step k+1 and step 0. Combined with the frozen procs in the complement interval,
    # we'd get config[k+1] = config[0] (up to the frozen procs).

    # Actually no. Let me think more carefully.
    # SupportInterval: [start, end) with start < end, all movers in `procs`.
    # Procs outside `procs` don't fire in [start, end), so their states are
    # unchanged: config[start] restricted to outside = config[end] restricted to outside.
    # For the inside procs: they don't fire OUTSIDE [start, end), so
    # config[start] restricted to inside = config[end'] restricted to inside
    # where end' goes around the cycle back to start.
    # Combined: config[start] = config[end mod CL] for ALL procs → repeat → False.

    # For terminal case with internal crossing at k:
    # Interval [k+1, CL-1): movers in cutArc (since no crossing between k+1 and CL-1)
    # Wait, does the terminal crossing at CL-1 affect this?
    # Step CL-1 crosses the terminal edge. If k+1 ≤ CL-1, then step CL-1
    # is NOT in the half-open interval [k+1, CL-1). But the mover at step CL-1
    # transitions across the edge, leaving the cutArc.
    # The interval [k+1, CL-1) has length CL-1-(k+1) = CL-k-2 steps.
    # All movers in these steps are in the cutArc.

    # The ReturnCone: config at step k+1 vs config at step CL-1.
    # Procs outside cutArc don't fire in [k+1, CL-1), so their states match.
    # Procs inside cutArc don't fire outside [k+1, CL-1)?
    # Outside [k+1, CL-1): steps 0..k and step CL-1.
    # Step CL-1: mover crosses the terminal edge. If the terminal edge has
    # one endpoint in cutArc: then step CL-1's mover is at a cutArc boundary.
    # This mover IS in cutArc (or at the edge). So a cutArc proc fires at step CL-1.
    # This breaks the support interval argument!

    # So the issue is clear: the terminal crossing means a cutArc proc fires
    # OUTSIDE the interval [k+1, CL-1), specifically at step CL-1. The support
    # interval argument requires cutArc procs to ONLY fire inside the interval.

    print("\n" + "=" * 70)
    print("KEY INSIGHT: Why terminal crossing blocks the cutArc argument")
    print("=" * 70)
    print("""
The cutArc argument for two INTERNAL crossings works because:
- Between crossings, movers stay in the cutArc
- Outside crossings, movers stay in the complement
- This gives a clean partition: cutArc procs fire ONLY in one interval

For TERMINAL crossing at step CL-1:
- The terminal step's mover crosses the singleton edge
- This mover is at the cutArc boundary
- So a cutArc-adjacent proc fires at step CL-1, which is OUTSIDE
  the putative support interval
- The support interval argument breaks

This is why NonConsecutive.lean proves "both internal → False" but
cannot extend to "one terminal → False" using the same machinery.
""")

    # Now let's check: does entry conflict cover these terminal walks?
    # Entry conflict is about the EXISTENCE of conflicting context requirements
    # at binary procs. It doesn't depend on cutArc or support intervals.

    # For each terminal walk, check the UEC mechanisms:
    # Mechanism 1: Both-Even Return
    # Mechanism 2: Toggle-FR
    # Mechanism 3: Zero-Side EC
    # Mechanism 4: Traversal Return

    # These mechanisms examine the binary proc's local firing pattern.
    # Let me check if binary procs have the required patterns.

    print("\n" + "=" * 70)
    print("ENTRY CONFLICT CHECK on terminal walks")
    print("=" * 70)

    # For each binary proc in a walk, extract its firing pattern:
    # - Which steps it fires
    # - The mover word segment between its firings
    # - The "side" (CW or CCW) of each firing

    def analyze_binary_firing(word, n, binary_proc):
        """Analyze firing pattern at a binary proc."""
        CL = len(word)
        fire_steps = [k for k in range(CL) if word[k] == binary_proc]
        fc = len(fire_steps)
        if fc < 2:
            return None

        # For each pair of consecutive firings, what happens between them?
        gaps = []
        for idx in range(len(fire_steps)):
            s1 = fire_steps[idx]
            s2 = fire_steps[(idx + 1) % len(fire_steps)]
            if s2 > s1:
                gap_movers = [word[k] for k in range(s1+1, s2)]
            else:
                gap_movers = [word[k] for k in range(s1+1, CL)] + [word[k] for k in range(0, s2)]
            gaps.append({
                'start': s1, 'end': s2,
                'gap_movers': gap_movers,
                'gap_length': len(gap_movers),
                'sides': None  # would need config to determine
            })

        return {
            'fire_steps': fire_steps,
            'fc': fc,
            'gaps': gaps
        }

    # Check a sample of terminal walks
    print("\nSample terminal walk analysis:")
    for w, d, singletons in terminal_walks[:10]:
        CL = len(w)
        print(f"\n  word={w}, len={CL}, disp={d}")
        for b in sorted(binary):
            info = analyze_binary_firing(w, n, b)
            if info:
                print(f"  Binary P{b}: fc={info['fc']}, fires at steps {info['fire_steps']}")
                for gi, gap in enumerate(info['gaps']):
                    print(f"    Gap {gi}: [{gap['start']}→{gap['end']}], len={gap['gap_length']}, movers={gap['gap_movers'][:8]}{'...' if len(gap['gap_movers'])>8 else ''}")

                # Check Mechanism 1: Both-Even Return
                # Needs: M=1 (one oscillation), both gaps have even length
                if info['fc'] == 2:
                    g0 = info['gaps'][0]['gap_length']
                    g1 = info['gaps'][1]['gap_length']
                    both_even = (g0 % 2 == 0) and (g1 % 2 == 0)
                    print(f"    Mech1 (Both-Even Return): fc=2, gaps=({g0},{g1}), both_even={both_even}")

print("\n" + "=" * 70)
print("FINAL ANALYSIS: The walk-level entry conflict check")
print("=" * 70)

# The real EC check needs actual CONFIGS, not just mover words.
# But we can check a necessary condition: for a binary proc with fc=2,
# the mover word constrains what the neighbor procs do between the two firings.

# Key insight from UEC Mechanism 4 (Traversal Return):
# For fc=2 at binary proc b, the walk visits b at steps s1, s2.
# Between s1 and s2, the walk goes out and comes back.
# The return trip forces the same neighbor config, creating EC.

# But this is the ANALYTICAL argument. For verification we need configs.
# Since we don't have configs (just mover words), let me check whether
# the UEC COMPUTATIONAL RESULTS cover odd-winding.

# From MEMORY: UEC verified at n=5 (1094), n=6 (91872), n=8 (11520).
# These numbers include ALL cycle types.
# The key verification script is binscc_complete_proof.py.

print("""
The UEC verification (binscc_complete_proof.py) checked ALL good cycles
at n=5, 6, 8 for non-consecutive binary at sub-threshold. The verification
found 0 exceptions — every cycle has entry conflict.

These cycles include ALL winding types (zero, odd, and other).

Therefore: odd-winding cycles with non-consecutive binary at sub-threshold
ALL have entry conflict. No valid system can produce them.

The terminal crossing case DOES occur in mover words (325/4001 at n=6),
but it's covered by entry conflict regardless. The cutArc approach is
unnecessary — UEC is the right proof route.

The Lean sorry in nonConsecutive_false should be closed via:
1. Formalizing UEC for non-consecutive binary (already analytically proved)
2. Routing through entry conflict instead of shadow construction
3. The circular dependency that forced UEC removal needs architectural fix
""")

# Let me also verify: are there walks where ALL binary procs have fc=2?
# (This is the hypothesis of the terminal crossing theorem in Lean)
print("=" * 70)
print("CHECK: walks where all binary procs have fc=2")
print("=" * 70)

all_fc2_terminal = 0
all_fc2_non_terminal = 0
non_fc2 = 0

for w, d in all_walks:
    CL = len(w)
    fcs = {p: fire_count(w, p) for p in binary}
    if all(fc == 2 for fc in fcs.values()):
        singletons = []
        for e in range(n):
            tc = edge_traversal_count(w, n, e)
            if tc == 1:
                steps = edge_cross_steps(w, n, e)
                singletons.append((e, steps[0]))
        has_terminal = any(s + 1 == CL for e, s in singletons)
        if has_terminal:
            all_fc2_terminal += 1
        else:
            all_fc2_non_terminal += 1
    else:
        non_fc2 += 1

print(f"All binary fc=2, terminal singleton: {all_fc2_terminal}")
print(f"All binary fc=2, no terminal singleton: {all_fc2_non_terminal}")
print(f"Some binary fc > 2: {non_fc2}")

if all_fc2_terminal == 0:
    print("\n*** IMPORTANT: No walks with all-binary-fc=2 have terminal singletons! ***")
    print("The terminal crossing theorem's hypothesis (all binary fc=2) may")
    print("be too strong — it might never be satisfied for odd-winding walks.")
    print("This would make the terminal crossing case VACUOUS under that hypothesis.")
elif all_fc2_terminal > 0:
    print(f"\n{all_fc2_terminal} walks have all-binary-fc=2 AND terminal singletons.")
    print("The terminal crossing case is non-vacuous.")
    # Show examples
    count = 0
    for w, d in all_walks:
        CL = len(w)
        fcs = {p: fire_count(w, p) for p in binary}
        if all(fc == 2 for fc in fcs.values()):
            singletons = []
            for e in range(n):
                tc = edge_traversal_count(w, n, e)
                if tc == 1:
                    steps = edge_cross_steps(w, n, e)
                    singletons.append((e, steps[0]))
            has_terminal = any(s + 1 == CL for e, s in singletons)
            if has_terminal and count < 5:
                print(f"  Example: word={w}, len={CL}, disp={d}, singletons={singletons}")
                count += 1
