#!/usr/bin/env python3
"""
RA14c: Interior analysis — which binary procs are truly interior?

Key discovery from RA14b: the Lean pair (cwSteps[rb], ccwSteps[b]) gives 100%
context match ONLY when b is sufficiently far from the turnaround points.

The walk structure: CW from position start to position turn, then CCW back.
Turnaround at position `turn` means: the CW→CCW transition happens there.
"Interior" means b is at least 2 positions from BOTH turnaround points.

For n=5: walks have turnaround at various positions. When binary {0,1,2}
and turnaround at position 1 (walk [0,1,0,...]), procs 0,1,2 are all
within 1 step of the turnaround → no interior binary.

HYPOTHESIS: For n >= 9 with 3 binary, there's ALWAYS a binary proc that's
interior (far from both turnarounds), and for that b, the context match holds.

The Lean `hinterior: True` placeholder needs to be replaced with:
  b is at least 2 CW-steps from the turnaround in both directions
  (i.e., b is not the first, second, or last position in the CW traversal)
"""

from itertools import product as iproduct
from collections import defaultdict


def enumerate_fc2_walks(n):
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == 2 * n:
            nxt = path[0]
            if abs(pos - nxt) == 1 or abs(pos - nxt) == n - 1:
                if all(f == 2 for f in fc):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
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
    result = []
    for w in walks:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def step_dir(word, t, n):
    L = len(word)
    curr = word[t]
    nxt = word[(t + 1) % L]
    d = (nxt - curr) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0


def winding_number(word, n):
    return sum(step_dir(word, t, n) for t in range(len(word)))


def is_sweep(word, n):
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    return all(d == 1 for d in dirs) or all(d == n - 1 for d in dirs)


def enumerate_state_sequences(m, k):
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


def build_configs(word, n, ms, combo):
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    return configs


def get_turnarounds(word, n):
    """Find the two turnaround positions of a palindromic walk.
    Turnaround 1: CW→CCW transition position
    Turnaround 2: CCW→CW transition position"""
    L = len(word)
    dirs = [step_dir(word, t, n) for t in range(L)]
    turns = []
    for t in range(L):
        if dirs[t] != dirs[(t + 1) % L]:
            # Transition at word[t+1] or word[t]
            turns.append((t, word[t], word[(t+1) % L], dirs[t], dirs[(t+1) % L]))
    return turns


def cw_distance(a, b, n):
    """CW distance from a to b on Z_n."""
    return (b - a) % n


def main():
    print("=" * 72)
    print("RA14c: Interior binary analysis")
    print("=" * 72)

    # =====================================================================
    # PART 1: Identify turnaround structure for all ZW walks
    # =====================================================================
    print("\nPART 1: Turnaround structure and interior condition")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            # Find phase transition points
            transitions = []
            for t in range(L):
                if dirs[t] != dirs[(t + 1) % L]:
                    transitions.append(t)

            # CW→CCW transition: dirs[t]=CW, dirs[t+1]=CCW
            # The turnaround proc is word[t+1] (the first CCW mover)
            # Wait, no. The CW→CCW means: step t is CW (word[t]→word[t+1]),
            # step t+1 is CCW (word[t+1]→word[t+2]).
            # The "turnaround" position is the furthest CW point = word[t+1]
            # which is where the walk turns around.

            # Actually: in a clean palindrome [s, s+1, ..., turn, turn-1, ..., s+1, s, s-1]
            # The CW→CCW transition is at step where word[t] = turn
            # because step t fires turn CW (turn→turn+1) and step t+1 fires
            # turn+1 CCW (hmm, or something like that).

            # Let me just identify the turning points from the walk structure.
            # A turning point is where the walk reverses direction.

            # CW phase: word goes increasing (mod n)
            # The CW phase end is at the step where the next step goes backwards.
            # If step t has dir CW and step t+1 has dir CCW:
            #   CW endpoint = word[(t+1) % L]  (the position reached by step t)
            # If step t has dir CCW and step t+1 has dir CW:
            #   CCW endpoint = word[(t+1) % L]

            cw_end = None
            ccw_end = None
            for t in range(L):
                if dirs[t] == 1 and dirs[(t+1) % L] == -1:
                    cw_end = w[(t+1) % L]
                elif dirs[t] == -1 and dirs[(t+1) % L] == 1:
                    ccw_end = w[(t+1) % L]

            # "Interior" = not at CW endpoint, not at CCW endpoint,
            # and not immediately adjacent to them.
            # More precisely: the walk goes from ccw_end CW to cw_end,
            # then CCW back. Interior means ≥ 2 positions from both endpoints
            # in the CW direction.

            # CW arc: ccw_end → ccw_end+1 → ... → cw_end
            arc_len = cw_distance(ccw_end, cw_end, n)
            # Position j is "interior" if its CW distance from ccw_end is in [2, arc_len-2]
            interior_arc = []
            for j in range(n):
                d_from_start = cw_distance(ccw_end, j, n)
                if 2 <= d_from_start <= arc_len - 2:
                    interior_arc.append(j)

            interior_binary = [b for b in binary_pos if b in interior_arc]

            print(f"\n  Walk {w}")
            print(f"  CW endpoint: {cw_end}, CCW endpoint: {ccw_end}")
            print(f"  Arc length: {arc_len} (CW from {ccw_end} to {cw_end})")
            print(f"  Interior positions (≥2 from both ends): {interior_arc}")
            print(f"  Interior binary: {interior_binary}")

            # For interior binary, verify context match
            if interior_binary:
                cw_fire = {}
                ccw_fire = {}
                for t in range(L):
                    p = w[t]
                    if dirs[t] == 1:
                        cw_fire[p] = t
                    elif dirs[t] == -1:
                        ccw_fire[p] = t

                for b in interior_binary:
                    rb = (b + 1) % n
                    lb = (b - 1) % n

                    if b not in ccw_fire or rb not in cw_fire:
                        continue

                    k2 = cw_fire[rb]
                    k1 = ccw_fire[b]

                    # Fires between k2 and k1
                    if k2 < k1:
                        firing_steps = list(range(k2, k1))
                    else:
                        firing_steps = list(range(k2, L)) + list(range(0, k1))

                    firing_movers = [w[t] for t in firing_steps]
                    lb_t = firing_movers.count(lb)
                    b_t = firing_movers.count(b)
                    rb_t = firing_movers.count(rb)

                    print(f"    b={b}: fires in [k2,k1) — lb={lb_t}, b={b_t}, rb={rb_t}")
                    print(f"      lb({lb}, m={ms[lb]}): {'OK' if lb_t == 0 or (ms[lb] == 2 and lb_t == 2) else 'ISSUE'} "
                          f"({'zero' if lb_t == 0 else f'full cycle {lb_t}'})")
                    print(f"      b({b}, m=2): {'OK (zero)' if b_t == 0 else 'ISSUE'}")
                    print(f"      rb({rb}, m={ms[rb]}): {'OK' if rb_t == 2 else 'ISSUE'} "
                          f"({'full cycle' if rb_t == 2 else f'{rb_t} fires'})")
            else:
                print(f"    NO interior binary! (arc too short for binary positions)")

    # =====================================================================
    # PART 2: The CORRECT interior condition
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 2: What makes a binary proc 'interior' for context match?")
    print("=" * 72)

    print("""
    From the data, the pattern is clear:

    For a palindromic walk from start s to turnaround t (CW arc length d):
      CW order:  s, s+1, ..., t
      CCW order: t, t-1, ..., s

    For binary b at CW-distance j from s (so b = s+j mod n):
      k2 = cwSteps[b+1] = the step when proc b+1 fires CW
      k1 = ccwSteps[b] = the step when proc b fires CCW

    Between k2 and k1, the movers are:
      CW phase rest: b+2, b+3, ..., t          (d-j-1 procs)
      CCW phase start: t-1, t-2, ..., b+1, b   (wait, b fires at k1, not between)
      CCW phase from t: t, t-1, ..., b+1        (j procs from the far side)

    Wait, more precisely:
      After cwSteps[b+1] (= step j+1 of CW phase), CW continues:
        b+2, b+3, ..., t  (these are steps j+2 through d)
      Then CCW starts:
        t (turns around), t-1, ..., b+1  (CCW steps, firing in reverse)
      Then b fires CCW (= k1)

    So between k2 and k1:
      CW fires: b+2, b+3, ..., t          → neighbors of b? Only b+2 (= rb+1) if rb=b+1
      CCW fires: t, t-1, ..., b+1         → includes b+1 = rb!

    So rb fires: once at k2 (CW, step j+1) + once in CCW (step d + (d-1-j) = 2d-1-j)
    Total rb fires in [k2, k1) = 2 (CW at k2, CCW between k2 and k1).

    For lb = b-1: between k2 and k1, lb fires in CCW phase at step 2d-1-(j-1) = 2d-j.
    But lb fires CW at step j-1 (BEFORE k2!). So between k2 and k1, lb fires:
      - CW: NO (already fired before k2, since cwSteps[lb] = j-1 < j+1 = k2)
      - CCW: YES, at step 2d-j (which is after k2 and before k1 = 2d-1-j... wait)

    Let me check: k1 = ccwSteps[b] = step (d + something).
    In the walk [s, s+1, ..., t, t-1, ..., s+1, s, t]:
      CW steps 0..d-1: movers s, s+1, ..., t
      CCW steps d..2d-1: movers t-1, t-2, ..., s, t
      Wait, that's not right either. Let me trace carefully.

    For the canonical walk [0, 1, 2, ..., n-1, n-2, ..., 1, 0, n-1]:
      CW: step 0: mover 0 (0→1), ..., step n-2: mover n-2 (n-2→n-1), step n-1: mover n-1 (n-1→...)
      Actually step n-1: word[n-1] = n-1, word[n] = n-2. Dir = CCW.
      So CW phase is steps 0..n-2 (n-1 steps), CCW phase is steps n-1..2n-1 (n steps? no)

    Let me just check: for n=7, canonical walk [0,1,2,3,4,5,6,5,4,3,2,1,0,6]:
      Steps 0-5: CW (movers 0,1,2,3,4,5)
      Step 6: word[6]=6, word[7]=5. dir=CCW.
      Steps 6-12: CCW (movers 6,5,4,3,2,1,0)
      Step 13: word[13]=6, word[0]=0. dir=CW.
      So CW: 0-5 (6 steps), CCW: 6-12 (7 steps), CW: 13 (1 step)

    Actually step 13 wraps: CW phase has 7 steps (0-5 and 13), CCW has 7 steps (6-12).

    For b=2 (interior):
      k2 = cwSteps[3] = 3, k1 = ccwSteps[2] = 10
      Between 3 and 10: steps 3,4,5,6,7,8,9
      Movers: 3,4,5,6,5,4,3
      rb=3 fires: at step 3 (CW) and step 9 (CCW) → 2 fires total
      lb=1 fires: 0 times (lb CW at step 1 < 3, lb CCW at step 11 > 10)
      b=2 fires: 0 times (b CW at step 2 < 3, b fires CCW at step 10 = k1)

    So for b=2: lb fires 0, b fires 0, rb fires 2. PERFECT.

    For b=1 (closer to start):
      k2 = cwSteps[2] = 2, k1 = ccwSteps[1] = 11
      Between 2 and 11: steps 2,3,4,5,6,7,8,9,10
      Movers: 2,3,4,5,6,5,4,3,2
      rb=2 fires: at step 2 (CW) and step 10 (CCW) → 2 fires
      lb=0 fires: CW at step 0 (before k2) but CCW at step 12 (after k1!?)
        Wait, step 12: word[12]=0. dir=CCW. So ccwSteps[0] = 12.
        12 > 11 = k1, so lb=0 fires 0 times between k2 and k1?
        But from the data: lb_fires=0. YES.
      Wait the data says lb_fires=1 for b=1 at this walk. Let me recheck.

    Hmm, for the full-length walk [0,1,2,3,4,5,6,0,6,5,4,3,2,1]:
      This is a different walk than canonical! It has turnaround at 6 (CW end)
      and at 0 (CCW end).
      Steps 0-6: CW (movers 0,1,2,3,4,5,6)
      Step 7: word[7]=0, word[8]=6. Dir = (6-0)%7 = 6 = n-1 = CCW.
      Steps 7-13: CCW (movers 0,6,5,4,3,2,1)

    For b=1:
      k2 = cwSteps[2] = 2, k1 = ccwSteps[1] = 13
      Between steps 2..12 (inclusive k2, exclusive k1):
        Movers: 2,3,4,5,6,0,6,5,4,3,2
        lb=0 fires: step 7 (mover 0). That's 1 fire. → lb_fires=1. Confirmed.

    So the issue is: at the walks where the turnaround WRAPS AROUND past 0,
    proc 0 (binary!) fires in the CCW phase between k2 and k1.

    The interior condition must account for this. Proc b is interior iff:
    - b is at least 2 CW positions from the CW turnaround AND
    - b is at least 2 CW positions from the CCW turnaround
    """)

    # =====================================================================
    # PART 3: For n>=9, does the interior condition always give a valid b?
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 3: Interior condition with distance >= 2 from turnarounds")
    print("=" * 72)

    for n in [5, 7, 9, 11]:
        print(f"\n--- n = {n} ---")

        if n <= 7:
            walks = enumerate_fc2_walks(n)
            nonsweep_zw = [w for w in walks
                           if winding_number(w, n) == 0 and not is_sweep(w, n)]
        else:
            # For n=9,11: generate all possible palindromic walk shapes
            # A palindromic walk on Z_n with turnaround at position t (CW from 0 to t)
            # can be rotated to start at any position. For our purposes, enumerate
            # by arc length d (CW distance from start to turnaround).
            nonsweep_zw = []
            for d in range(2, n):
                # CW from 0 to d, CCW back
                w = list(range(d+1)) + list(range(d-1, 0, -1)) + [0, n-1 if d < n-1 else 0]
                # Actually: the walk starts at 0, goes CW to d, then CCW back to 0,
                # then needs one more step to close.
                # [0, 1, ..., d, d-1, ..., 1, 0, n-1]
                # Length: (d+1) + (d-1) + 1 = 2d+1? No.
                # CW phase: 0→1, 1→2, ..., (d-1)→d: d steps
                # CCW phase: d→(d-1), ..., 1→0: d steps
                # Last step: 0→n-1 or 0→1? For winding 0, needs to close with CW step.
                # Actually: [0, 1, ..., d, d-1, ..., 1, 0, n-1]
                # Steps: n=0→1 CW, ..., d-1→d CW (d steps CW)
                #         d→d-1 CCW, ..., 1→0 CCW (d steps CCW)
                #         0→n-1 CCW (1 step CCW)
                # That's d CW + d+1 CCW = 2d+1. But we need 2n steps.
                # So 2d+1 = 2n → d = n-0.5, not integer. Something's wrong.

                # For fc=2 walks: each proc fires exactly 2 times.
                # Total steps = 2n.
                # CW steps = n, CCW steps = n (since zero winding).
                # The walk visits each edge twice (once CW, once CCW)? No.
                # Each PROC fires twice. CW phase has n firings, CCW phase has n.
                pass

            # Actually, for n >= 9, just generate the canonical shapes
            nonsweep_zw = []
            for d in range(2, n):
                # Turnaround at CW-distance d from start (proc d)
                # Walk: [0, 1, ..., d, d-1, ..., 1, 0, n-1, n-2, ..., d+1, d]
                # No, this goes past. The correct palindromic walk with
                # turnaround at d and n-1:
                # CW: 0→1→...→d (d steps)
                # CCW: d→d-1→...→0→n-1→...→d+1 (n steps)
                # CW: d+1→d (doesn't work)

                # Actually the walk structure is simpler. For a zero-winding BAF:
                # Pick two turnaround points: s and t with CW-distance d.
                # CW from s to t: d steps
                # CCW from t back to s: d steps  → winding = 0
                # But total = 2d. For fc=2, need 2d = 2n, so d = n.
                # CW-distance n = full circle, which is a sweep. Contradiction with non-sweep.

                # Wait, that can't be right. From the n=5 data, there are 5 non-sweep ZW walks.
                # For n=5: walk [0,1,2,3,4,3,2,1,0,4] has 10 steps = 2*5.
                # CW steps: 0→1, 1→2, 2→3, 3→4, 4→(goes to 3, CCW). Actually step 3: mover 3, CW.
                # step 4: mover 4, dir = (3-4)%5 = 4 = CCW. So CW: steps 0-3 (4 steps),
                # CCW: steps 4-8 (5 steps), CW: step 9 (1 step). Total CW=5, CCW=5.

                # The BAF has TWO arcs, not one. The CW arc goes from 0 to 3 (length 4),
                # then CCW from 3 to 0 (length 4), then the remaining 2 steps handle
                # procs 4 and wrap-around.

                # Actually: ALL ZW fc=2 walks on Z_n are determined by their turnaround
                # position. Turnaround at CW-position d means:
                # CW: 0, 1, ..., d
                # CCW: d-1, d-2, ..., 0, n-1, n-2, ..., d+1, d
                # Wait that's 2n movers total but not all firing exactly 2.

                pass

            # For large n, generate walks by turnaround position
            nonsweep_zw = []
            for turn_pos in range(1, n):
                # Walk: CW from 0 to turn_pos, then CCW back to 0, then around the other way
                # This means: CW fires 0, 1, ..., turn_pos (= turn_pos + 1 movers)
                # CCW fires go from turn_pos back, wrapping around
                # For fc=2: each proc fires once CW and once CCW
                # CW firing order: position 0, 1, ..., turn_pos, then wraps to n-1, n-2, ..., turn_pos+1
                # Wait, CW firing order = mover order. If CW from 0 to turn_pos is steps 0..turn_pos-1,
                # and then we continue CW from turn_pos+1 wrapping... no.

                # Let me just construct: first CW sweep from 0 to turn_pos-1,
                # then CCW from turn_pos-1 to 0, then CCW from n-1 down to turn_pos,
                # then CW from turn_pos to 0 (wraps)...

                # This is getting complicated. Let me just enumerate for n=9.
                pass

            if n == 9:
                # Enumerate by generating palindromic words directly
                # Each palindromic word is determined by the CW→CCW turnaround point
                # For n=9: the walk visits all 9 procs, each twice.
                # A BAF walk from position a: goes CW distance d, then CCW distance d,
                # and the remaining procs are covered by a second CW+CCW arc.
                # But with exactly 2 transitions, it's a single BAF.

                # From the enumeration at n=5,7: the walks have turnaround at distance
                # 1, 2, 3, 4 (for n=5) giving 4 walks + the full CW+CCW (distance n-1=4).
                # Actually n=5 has 5 non-sweep ZW walks (excluding 2 sweeps).

                # For computational tractability, just test canonical walks
                nonsweep_zw = []
                for d in range(1, n):  # turnaround CW-distance from start
                    # Canonical BAF: [0, 1, ..., d, d-1, ..., 1, 0, n-1, n-2, ..., d+1, d]
                    # No wait. The correct walk:
                    # Phase 1 (CW): 0→1→...→d: movers 0, 1, ..., d (firing steps 0..d)
                    # Phase 2 (CCW): d→d-1→...→1→0→n-1→...→d+1: movers d, d-1, ..., 1, 0, n-1, ..., d+1
                    # Wait, that's CW d+1 movers + CCW n movers = d+1+n movers.
                    # But total should be 2n. So d+1+n = 2n → d = n-1. That's only the full BAF.

                    # Hmm, I think the BAF structure is:
                    # CW from position a to position b (n CW steps total)
                    # CCW from position b-1 back to a+1, then CCW from a to b (n CCW steps total)
                    # No, that doesn't make sense either.

                    # Let me just look at what n=5 walks look like:
                    # [0,1,2,3,4, 3,2,1,0, 4]:
                    #   CW: 0→1→2→3→4 (5 steps), CCW: 4→3, 3→2, 2→1, 1→0, 0→4 (5 steps)
                    #   Wait, step 9 is 4→0, which is CW! Not CCW.
                    #   Rechecking: word=[0,1,2,3,4,3,2,1,0,4], step 9: 4→0. (0-4)%5 = 1. CW!
                    #   So the directions are: CW,CW,CW,CW, CCW,CCW,CCW,CCW,CCW, CW
                    #   This is a BAF with turnaround at proc 4 (CW end) and 0 (CCW end + CW restart)

                    # [0,1,2,3, 2,1,0,4,3, 4]:
                    #   CW: 0→1→2→3 (4 CW), CCW: 3→2, 2→1, 1→0, 0→4(?), 4→3 (is 0→4 CCW? (4-0)%5 = 4 = n-1 = CCW. Yes.)
                    #   So CCW: 3→2, 2→1, 1→0, 0→4, 4→3 (5 CCW), then CW: 3→4 (1 CW). Total CW=5, CCW=5.

                    # The general pattern for CW-turnaround at distance d from start:
                    #   CW from 0 to d: movers [0,1,...,d] (d+1 CW steps)
                    #   CCW from d back through 0 to -(n-d-1)≡d+1: movers [d-1,d-2,...,0,n-1,...,d+1]
                    #     That's d + (n-d-1) = n-1 CCW steps
                    #   CW closing: mover d (d→d+1? no). Hmm.

                    # Actually from the pattern: total CW steps = n, total CCW = n.
                    # CW at turnaround d: first d+1 steps CW, last n-d-1 steps CW.
                    # CCW: middle n-1 steps CCW? No that only sums to 2n-1.

                    # I think the walk is: [0, 1, ..., d, d-1, ..., 1, 0, n-1, n-2, ..., d+1, d, d+1, ..., n-1]
                    # No. Let me just construct from the pattern at n=5:
                    # d=4 (turn at 4): [0,1,2,3,4, 3,2,1,0, 4]
                    # d=3 (turn at 3): [0,1,2,3, 2,1,0,4,3, 4]
                    # d=2 (turn at 2): [0,1,2, 1,0,4,3,2, 3,4]
                    # d=1 (turn at 1): [0,1, 0,4,3,2,1, 2,3,4]

                    # Pattern: first d+1 movers are 0,1,...,d (CW)
                    # Then n-1 movers going CCW from d back to d+1 (wrapping through 0, n-1, etc.)
                    # Then 1 mover going CW? No.

                    # Let me trace d=3, n=5: [0,1,2,3, 2,1,0,4,3, 4]
                    # Movers: 0,1,2,3, 2,1,0,4,3, 4
                    # Dirs: CW,CW,CW, CCW,CCW,CCW,CCW,CCW, CW,CW
                    # Wait: step 3: mover 3→2. Dir=(2-3)%5=4=CCW. Yes.
                    # step 8: mover 3→4. Dir=(4-3)%5=1=CW.
                    # step 9: mover 4→0. Dir=(0-4)%5=1=CW.
                    # So CW: steps 0,1,2,8,9 (5 steps), CCW: steps 3,4,5,6,7 (5 steps).

                    # General construction for turnaround at d:
                    cw_phase = list(range(d+1))  # 0, 1, ..., d
                    ccw_phase = list(range(d-1, -1, -1))  # d-1, d-2, ..., 0
                    # Then need to wrap: from 0 CCW to n-1, n-2, ..., d+1
                    ccw_wrap = [n-1-i for i in range(n-1-d)]  # n-1, n-2, ..., d+1
                    # Hmm let me check: for d=3, n=5: ccw_phase = [2,1,0], ccw_wrap = [4]
                    # Total movers: [0,1,2,3] + [2,1,0,4] + ???
                    # That's 8 movers but need 10.
                    # Missing: 3 and 4 need another firing each.

                    # OK the wrap continues from d+1 going CCW... no.
                    # Let me just directly construct:
                    # [0, 1, ..., d, d-1, ..., 1, 0, n-1, n-2, ..., d+1]
                    # movers = list(range(d+1)) + list(range(d-1, -1, -1)) + list(range(n-1, d, -1))
                    cw_part = list(range(d+1))  # 0..d
                    ccw_back = list(range(d-1, -1, -1))  # d-1..0
                    ccw_wrap = list(range(n-1, d, -1))  # n-1..d+1

                    if d == n - 1:
                        continue  # skip full sweep

                    movers = cw_part + ccw_back + ccw_wrap
                    # Check length
                    # d+1 + d + (n-1-d) = d+1+d+n-1-d = n+d
                    # Need 2n movers. So n+d = 2n → d = n. Only works for sweep. Wrong.

                    # Let me think differently. From the n=5, d=3 example:
                    # [0,1,2,3, 2,1,0, 4,3, 4]
                    # movers = [0,1,2,3] + [2,1,0] + [4,3] + [4]
                    # = CW arc (d+1=4) + CCW back (d=3, minus start=0..d but first one already counted?)

                    # Actually: [0,1,2,3, 2,1,0,4,3, 4]
                    # = [0,1,2,3] (CW to d=3) + [2,1,0,4,3] (CCW from d through 0 to d+1) + [4] (CW tail)
                    # CCW part: 5 movers = n movers. CW: 4+1 = 5 movers.

                    # So: CW part = [0,1,...,d] + [d+1,...,n-1] (last n-d-1 procs CW)
                    #     CCW part = [d-1,...,0,n-1,...,d+1] (all n procs CCW? No, d procs)

                    # Hmm. For d=3, n=5:
                    # CW movers: 0,1,2,3 (steps 0-3) and 4 (step 9). Total: 5. ✓
                    # CCW movers: 2,1,0,4,3 (steps 4-8). Total: 5. ✓
                    #
                    # The CW order is: 0,1,2,3, then later 4
                    # The CCW order is: 2,1,0, then 4,3 (wrapping around)

                    # For general d and n:
                    # Walk = [0, 1, ..., d] ++ [d-1, ..., 1, 0, n-1, ..., d+1] ++ [d+2, ..., n-1]
                    # Hmm no. Let me just write the correct formula.

                    # From the examples:
                    # d=4,n=5: [0,1,2,3,4, 3,2,1,0, 4]  — CW:0-4, CCW:3,2,1,0, CW:4
                    # d=3,n=5: [0,1,2,3, 2,1,0,4,3, 4]  — CW:0-3, CCW:2,1,0,4,3, CW:4
                    # d=2,n=5: [0,1,2, 1,0,4,3,2, 3,4]  — CW:0-2, CCW:1,0,4,3,2, CW:3,4
                    # d=1,n=5: [0,1, 0,4,3,2,1, 2,3,4]  — CW:0,1, CCW:0,4,3,2,1, CW:2,3,4

                    # Pattern:
                    # Phase 1 (CW): movers 0, 1, ..., d  (d+1 movers)
                    # Phase 2 (CCW): movers d-1, d-2, ..., 0, n-1, n-2, ..., d+1  (n-1 movers)
                    # Phase 3 (CW): movers d+1, d+2, ..., n-1 (n-d-1 movers? For d=4,n=5: 0 movers. For d=3: 1 mover 4. For d=2: 2 movers 3,4.)
                    # Wait d=4,n=5: phase 3 = [4].
                    # Hmm: d+1 + (n-1) + ? = 2n → ? = n - d. But d=4,n=5: ? = 1 = [4]. d=3: ? = 2 = [4]... but pattern shows [4]. That's only 1.

                    # Let me recount from the examples:
                    # d=4: phases [0,1,2,3,4] (5) + [3,2,1,0] (4) + [4] (1) = 10 ✓
                    # d=3: phases [0,1,2,3] (4) + [2,1,0,4,3] (5) + [4] (1) = 10 ✓
                    # d=2: phases [0,1,2] (3) + [1,0,4,3,2] (5) + [3,4] (2) = 10 ✓
                    # d=1: phases [0,1] (2) + [0,4,3,2,1] (5) + [2,3,4] (3) = 10 ✓

                    # Phase 2 has: d + (n-d-1) = n-1 movers for all cases.
                    # Phase 3 has: n-d movers.
                    # Phase 1: d+1 movers.
                    # Total: d+1 + n-1 + n-d = 2n. ✓

                    # So the walk is:
                    phase1 = list(range(d+1))  # 0, 1, ..., d
                    phase2 = list(range(d-1, -1, -1)) + list(range(n-1, d, -1))  # d-1, ..., 0, n-1, ..., d+1
                    phase3 = list(range(d+1, n)) if d < n-1 else [n-1]
                    # Wait d=4,n=5: phase3 = [5..4] = empty. But example has [4].
                    # Hmm. For d=4,n=5: phase1=[0,1,2,3,4], phase2=[3,2,1,0], phase3=[4]?
                    # But range(5,5)=empty, and [n-1]=[4]. OK phase3 = [d] when d=n-1.
                    # Actually d=4 gives: phase2 = [3,2,1,0] + range(4,4,step=-1) = [3,2,1,0] + [] = [3,2,1,0]
                    # phase3: range(5,5) = [] but we need [4].

                    # I think for d=n-1: the walk is the canonical BAF [0,...,n-1,n-2,...,0,n-1]
                    # phase1 = [0,...,n-1], phase2 = [n-2,...,0], phase3 = [n-1]
                    # Hmm phase2 has n-2 elements, not n-1. Let me recheck.
                    # d=n-1=4: phase2 = range(3,-1,-1) + range(4,4,-1) = [3,2,1,0] + [] = [3,2,1,0] (4 elements)
                    # phase1 = [0,1,2,3,4] (5 elements)
                    # 5 + 4 = 9, need 10. Phase 3 must have 1 element.
                    # range(5,5) is empty. So phase3 should be [n-1] = [4].

                    # For d < n-1: phase3 = range(d+1, n). d=3,n=5: [4]. d=2: [3,4]. d=1: [2,3,4]. ✓
                    # For d = n-1: phase3 should be [n-1]. But range(n,n) = []. Need special case.

                    if d < n - 1:
                        phase3 = list(range(d+1, n))
                    else:
                        phase3 = [n-1]

                    movers = phase1 + phase2 + phase3
                    if len(movers) != 2 * n:
                        print(f"  d={d}: wrong length {len(movers)}")
                        continue

                    nonsweep_zw.append(movers)

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            # Find turnaround: the proc that fires CW at step d (last CW before CCW starts)
            transitions = []
            for t in range(L):
                if dirs[t] != dirs[(t+1) % L]:
                    transitions.append(t)

            if len(transitions) != 2:
                continue

            cw_end_step = transitions[0]
            ccw_end_step = transitions[1]
            cw_end_pos = w[(cw_end_step + 1) % L]  # position reached at CW end
            ccw_end_pos = w[(ccw_end_step + 1) % L]  # position reached at CCW end

            # All multisets to test
            test_ms_list = []
            # For n >= 9 with 3 binary: binary at positions 0,1,2
            ms = [2, 2, 2] + [3] * (n - 3)
            test_ms_list.append(ms)

            for ms in test_ms_list:
                binary_pos = [i for i in range(n) if ms[i] == 2]

                for b in binary_pos:
                    rb = (b + 1) % n
                    lb = (b - 1) % n

                    if b not in ccw_fire or rb not in cw_fire:
                        continue

                    k2 = cw_fire[rb]
                    k1 = ccw_fire[b]

                    if k2 < k1:
                        firing_steps = list(range(k2, k1))
                    else:
                        firing_steps = list(range(k2, L)) + list(range(0, k1))

                    firing_movers = [w[t] for t in firing_steps]
                    lb_t = firing_movers.count(lb)
                    b_t = firing_movers.count(b)
                    rb_t = firing_movers.count(rb)

                    # Check: for each of {lb, b, rb}:
                    # If binary: need even fires → value returns
                    # If ternary with fc=2: need fires = 0 or 2 → value returns
                    lb_ok = (lb_t == 0) or (lb_t == 2)  # for both binary and ternary with fc=2
                    b_ok = (b_t == 0)  # binary b, fires 0 between
                    rb_ok = (rb_t == 0) or (rb_t == 2)

                    if not (lb_ok and b_ok and rb_ok):
                        pass  # will print below

                # For each walk: is there at least one b where all three conditions hold?
                good_bs = []
                for b in binary_pos:
                    rb = (b + 1) % n
                    lb = (b - 1) % n
                    if b not in ccw_fire or rb not in cw_fire:
                        continue
                    k2 = cw_fire[rb]
                    k1 = ccw_fire[b]
                    if k2 < k1:
                        firing_steps = list(range(k2, k1))
                    else:
                        firing_steps = list(range(k2, L)) + list(range(0, k1))
                    firing_movers = [w[t] for t in firing_steps]
                    lb_t = firing_movers.count(lb)
                    b_t = firing_movers.count(b)
                    rb_t = firing_movers.count(rb)
                    if (lb_t == 0 or lb_t == 2) and b_t == 0 and (rb_t == 0 or rb_t == 2):
                        good_bs.append((b, lb_t, b_t, rb_t))

                if good_bs:
                    b, lt, bt, rt = good_bs[0]
                    print(f"  n={n} walk starts {w[:5]}...: b={b} works (lb={lt}, b={bt}, rb={rt})")
                else:
                    print(f"  n={n} walk {w}: NO good b!")
                    for b in binary_pos:
                        rb = (b + 1) % n
                        lb = (b - 1) % n
                        if b not in ccw_fire or rb not in cw_fire:
                            continue
                        k2 = cw_fire[rb]
                        k1 = ccw_fire[b]
                        if k2 < k1:
                            firing_steps = list(range(k2, k1))
                        else:
                            firing_steps = list(range(k2, L)) + list(range(0, k1))
                        firing_movers = [w[t] for t in firing_steps]
                        lt = firing_movers.count(lb)
                        bt = firing_movers.count(b)
                        rt = firing_movers.count(rb)
                        print(f"    b={b}: lb({lb})={lt}, b={bt}, rb({rb})={rt}")


if __name__ == "__main__":
    main()
