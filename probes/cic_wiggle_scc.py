#!/usr/bin/env python3
"""
CIC Exploration 12: Forced SCC for single-wiggle words.

Single-wiggle words: two near-sweeps with one bounce.
Structure: sweep direction d, bounce at edge (p, p+1), then sweep again.

Example at n=9, binary at {0,3,6}:
  [0,8,7,6,5,4,3,2,1, 0,8,7,6,5,4,3,2,1, 2,1]
  = sweep CCW + wiggle at (1,2) + tail

Goal: prove these words always produce forced SCC among non-good configs.
"""

from collections import Counter
from itertools import product as iproduct
import sys


def generate_single_wiggle_words(n, binary_positions, max_L=None):
    """
    Generate all single-wiggle fair adjacent cyclic mover words.

    A single-wiggle word has:
    - Winding number W (typically ±2 for the near-sweep structure)
    - All edges even except one edge with +2 extra traversals (the wiggle edge)
    - Exactly one direction reversal pair (bounce)

    More precisely: a single-wiggle word of winding W is a pure sweep of
    winding W with one "wiggle" inserted — the walk deviates from the sweep
    by bouncing once at some processor.

    Canonical form: start at 0, sweep CCW (0, n-1, n-2, ..., 1) for W full
    sweeps, but at one point bounce: ..., p+1, p, p+1, ...
    """
    binary_set = set(binary_positions)
    words = []

    if max_L is None:
        max_L = 4 * n

    # Generate by insertion: take a pure sweep and insert a wiggle
    # Pure sweep CCW of winding -2: [0, n-1, n-2, ..., 1, 0, n-1, ..., 1]
    # Length 2n. Insert wiggle at position t:
    # ..., p+1, p, p+1, ... adds 2 to length.

    # Actually, let me enumerate ALL fair adjacent cyclic words that have
    # exactly one wiggle (one pair of direction reversals).

    # A "wiggle" at processor p means the walk goes:
    #   ..., p+1, p, p+1, ... (bounce going left)
    # or ..., p-1, p, p-1, ... (bounce going right)
    # This adds 2 extra traversals to the edge between p and p±1.

    # For a word with winding W and one wiggle at processor p:
    # Base sweep has |W| * n steps, all same direction.
    # Wiggle adds 2 steps. Total L = |W| * n + 2.
    # All edges get |W| traversals except the wiggle edge gets |W| + 2.

    # For fairness: all procs move >= 2. In base sweep of |W| ≥ 2: all move |W| ≥ 2. ✓
    # Wiggle at p: p gets +1 extra move (the bounce). p+1 (or p-1) gets +1.
    # So moves: p gets |W|+1, the neighbor gets |W|+1, all others get |W|.

    # Binary parity: binary b needs even moves.
    # If b is at the wiggle (p or p±1): |W|+1 must be even → |W| odd.
    # If b is NOT at the wiggle: |W| must be even.
    # Can't have both unless no binary is at the wiggle.
    # So: |W| must be even (for non-wiggle binary), AND wiggle procs
    # must not be binary (since |W|+1 would be odd).

    # WAIT: |W| must be even for non-wiggle binary (they move |W| times).
    # For wiggle procs: they move |W|+1 times. If one is binary: need |W|+1 even → |W| odd.
    # Contradiction! So NO binary proc can be at the wiggle.

    # This means: the wiggle (bounce) must occur between two non-binary procs.
    # This is consistent with our Exploration 11 findings!

    # With |W| = 2 (minimum even): L = 2n + 2.
    # Wiggle at proc p (non-binary): p and one neighbor get 3 moves, rest get 2.
    # Wiggle edge gets 4 traversals, all others get 2.

    # Generate all such words for |W| = 2:
    for direction in [+1, -1]:  # +1 = CW, -1 = CCW
        for wiggle_proc in range(n):
            if wiggle_proc in binary_set:
                continue  # wiggle proc must be non-binary

            # The wiggle is a bounce at wiggle_proc going against the sweep.
            # If sweep is CW (+1): walk goes ..., p-1, p, p-1, ... (bounce going CW then back)
            # Wait, let me be precise.
            # Sweep CW: 0, 1, 2, ..., n-1, 0, 1, ...
            # Wiggle: at some point, instead of going p → p+1, we go p → p-1 → p.
            # This means p-1 gets an extra visit. The bounce point is p.
            # After bounce: p → p-1 → p → p+1 (resume sweep).
            # So the wiggle inserts "p-1, p" into the sequence after p.

            # Neighbor involved in bounce:
            if direction == +1:
                # CW sweep: ..., p-1, p, and instead of p+1, go p-1 then p then p+1
                # Wait no. In CW sweep: ..., p, p+1, p+2, ...
                # Wiggle at p: ..., p, p-1, p, p+1, ...
                # Bounce neighbor: p-1
                bounce_neighbor = (wiggle_proc - 1) % n
            else:
                # CCW sweep: ..., p, p-1, p-2, ...
                # Wiggle at p: ..., p, p+1, p, p-1, ...
                bounce_neighbor = (wiggle_proc + 1) % n

            if bounce_neighbor in binary_set:
                continue  # bounce neighbor must also be non-binary

            # For each position in the sweep to insert the wiggle:
            # In a |W|=2 sweep of length 2n, proc p appears at positions
            # p (first sweep) and p+n (second sweep) for CW.
            # Actually: CW sweep starting at 0: 0,1,2,...,n-1,0,1,...,n-1
            # Proc p appears at positions p and n+p.
            # We can insert the wiggle at either occurrence.

            for wiggle_time in range(2):  # 0 = first sweep, 1 = second sweep
                # Build the word
                word = []
                sweep_pos = 0
                wiggle_inserted = False

                for step in range(2 * n):
                    proc = (step * direction) % n
                    word.append(proc)

                    # Check if this is the wiggle insertion point
                    if (not wiggle_inserted and proc == wiggle_proc
                        and (wiggle_time == 0 and step < n
                             or wiggle_time == 1 and step >= n)):
                        # Insert bounce: go to bounce_neighbor and back
                        word.append(bounce_neighbor)
                        word.append(proc)  # Wait, this would add proc twice
                        # Actually the word already has proc. We insert
                        # bounce_neighbor and then continue with the next step.
                        # But the next step in the sweep is proc's successor.
                        # So: word = [..., proc, bounce_neighbor, proc, next_in_sweep, ...]
                        # But proc appears twice — the second one is the "return."
                        # Actually in the cyclic word, the wiggle means:
                        # Instead of just visiting proc once, we visit proc,
                        # bounce to neighbor, return to proc, then continue.
                        # So the sub-sequence is: ..., proc, bounce_neighbor, proc, ...
                        # The proc at the start is already in the word.
                        # We add: bounce_neighbor, proc (2 extra elements).
                        # Hmm, but this means proc is at positions step and step+2.
                        # That's correct — proc fires twice at the wiggle.
                        wiggle_inserted = True

                if not wiggle_inserted:
                    continue

                L = len(word)
                if L > max_L:
                    continue

                # Verify adjacency
                valid = True
                for i in range(L):
                    d = abs(word[i] - word[(i+1) % L])
                    if d != 1 and d != n - 1:
                        valid = False
                        break
                if not valid:
                    continue

                # Verify fairness
                mc = Counter(word)
                if not all(mc.get(p, 0) >= 2 for p in range(n)):
                    continue

                # Verify binary parity
                if not all(mc.get(b, 0) % 2 == 0 for b in binary_positions):
                    continue

                words.append(word)

    return words


def generate_wiggle_words_v2(n, binary_positions, max_extra=4):
    """
    Generate single-wiggle words more carefully.

    A |W|=2 sweep visits each proc exactly 2 times.
    A single wiggle adds a bounce (p, q, p) at one point,
    giving p 3 visits and q 3 visits (instead of 2 each).
    Length = 2n + 2.

    Multi-wiggle: add more bounces. Each adds 2 to length.
    """
    binary_set = set(binary_positions)
    words = set()  # use set to avoid duplicates

    # Base: CW sweep of winding +2
    # 0, 1, 2, ..., n-1, 0, 1, ..., n-1
    base_cw = [i % n for i in range(2*n)]

    # Base: CCW sweep of winding -2
    # 0, n-1, n-2, ..., 1, 0, n-1, ..., 1
    base_ccw = [(- i) % n for i in range(2*n)]

    for base, d_name in [(base_cw, "CW"), (base_ccw, "CCW")]:
        # Insert one wiggle at each possible position
        for insert_pos in range(2 * n):
            # At position insert_pos, the sweep is at proc p = base[insert_pos]
            # Next proc in sweep: base[(insert_pos + 1) % (2*n)]
            # The wiggle goes backward: p → (p - step_dir) → p
            # where step_dir is the sweep direction at this point
            p = base[insert_pos]
            next_p = base[(insert_pos + 1) % (2*n)]
            step = (next_p - p) % n
            if step == 1:
                # CW step: p → p+1. Wiggle: p → p-1 → p
                bounce = (p - 1) % n
            elif step == n - 1:
                # CCW step: p → p-1. Wiggle: p → p+1 → p
                bounce = (p + 1) % n
            else:
                continue

            # Check: wiggle procs must be non-binary
            if p in binary_set or bounce in binary_set:
                continue

            # Build wiggle word: insert (bounce, p) after position insert_pos
            word = list(base[:insert_pos + 1]) + [bounce, p] + list(base[insert_pos + 1:])

            # Verify adjacency
            L = len(word)
            valid = True
            for i in range(L):
                diff = abs(word[i] - word[(i+1) % L])
                if diff != 1 and diff != n - 1:
                    valid = False
                    break
            if not valid:
                continue

            # Verify fairness
            mc = Counter(word)
            if not all(mc.get(q, 0) >= 2 for q in range(n)):
                continue

            # Verify binary parity
            if not all(mc.get(b, 0) % 2 == 0 for b in binary_positions):
                continue

            # Normalize: rotate so minimum element is first
            # (for deduplication)
            min_idx = word.index(min(word))
            rotated = word[min_idx:] + word[:min_idx]
            words.add(tuple(rotated))

    return [list(w) for w in sorted(words)]


def analyze_wiggle_contexts(word, n, binary_positions):
    """
    For a single-wiggle word, extract the binary (L, R) contexts at each firing.

    In the seeded model (start at all-zeros), track the configuration at each step
    symbolically. For a near-sweep, most configs are determined by the sweep structure.
    """
    L = len(word)
    binary_set = set(binary_positions)

    # Track which procs have fired how many times
    # In seeded model: state of proc p after k firings depends on transition function.
    # For binary: state after k firings alternates 0→1→0→1...
    # For ternary: state after k firings cycles 0→a→b→0→...
    # But we don't know the transition function! We're analyzing the WORD, not a specific system.

    # What we CAN determine: the mover and its position at each time step.
    # From the word, we know WHO fires at each step.
    # The forced mover entries are: at time t, mover w_t fires.
    # The context (L, S, R) at time t is determined by the current config.
    # In the seeded model: config evolves based on transition rules.

    # For a near-sweep, the configs follow a pattern:
    # After the first sweep, each proc has fired once: config = (a_0, a_1, ..., a_{n-1})
    # where a_i = f_i(context at first firing).
    # After the second sweep: each proc has fired twice: back to near-initial.

    # The key insight: binary proc b fires at two specific times in the word.
    # At each firing, b sees some context (L, b_state, R).
    # These contexts are FORCED by the word structure.
    # The mover entry f_b(L, b_state, R) must produce the next state.
    # For binary: f_b(L, 0, R_up) must differ from 0 (fires UP: 0→1).
    #             f_b(L', 1, R_down) must differ from 1 (fires DOWN: 1→0).
    # The UP context has b_state = 0 (hasn't fired yet) and the DOWN context
    # has b_state = 1 (fired once).

    # For a near-sweep, we can determine the relative states of b's neighbors
    # at the time b fires.

    # Let's trace the firing order to determine contexts.

    # Record when each proc fires
    firing_times = {p: [] for p in range(n)}
    for t in range(L):
        firing_times[word[t]].append(t)

    print(f"\nWord: {word}")
    print(f"L={L}, n={n}")
    print(f"Binary: {binary_positions}")

    for b in binary_positions:
        times = firing_times[b]
        print(f"\n  Binary {b}: fires at times {times}")

        for t in times:
            # At time t, b fires. What are the states of b's neighbors?
            left = (b - 1) % n
            right = (b + 1) % n

            # How many times has left fired before time t?
            left_fires_before = sum(1 for tt in firing_times[left] if tt < t)
            right_fires_before = sum(1 for tt in firing_times[right] if tt < t)
            b_fires_before = sum(1 for tt in firing_times[b] if tt < t)

            print(f"    t={t}: b_state={b_fires_before} (binary: {'0' if b_fires_before%2==0 else '1'}), "
                  f"L({left})={left_fires_before} fires, R({right})={right_fires_before} fires")

            # For binary b: state = b_fires_before mod 2 (alternates 0,1,0,1,...)
            # For the neighbors: state depends on their transition function.
            # But we know the NUMBER of firings, which constrains the state.

            # Key fact: in the seeded model (all start at 0),
            # binary proc after k firings: state = k mod 2.
            # Ternary proc after k firings: state = f^k(0) where f is the
            # composed transition (depends on each firing's context).

            # For the forced entry analysis: we don't need the actual state.
            # We need to show that the SAME (L, S, R) context appears twice
            # with different required outputs (mover vs non-mover).
            # Or that the forced entries create a cycle in the non-good config space.

    return firing_times


def compute_forced_entries(word, n, binary_positions):
    """
    Compute the forced transition entries from a single-wiggle word.

    In the seeded model, the mover at time t fires and changes state.
    Non-movers keep their state. The mover entry f_p(L, S, R) at each
    firing is FORCED: it must produce a state different from S (the proc fires).

    The non-mover entries are also constrained: at time t, every non-mover p
    must have f_p(L, S, R) = S (stay).

    The forced entries are:
    - Mover entries: f_{w_t}(L_t, S_t, R_t) ≠ S_t for each time t
    - Non-mover entries: f_p(L_t, S_t, R_t) = S_t for each non-mover p at time t

    For binary procs: S_t ∈ {0, 1}, and f(L, S, R) ∈ {0, 1} with f ≠ S.
    So f(L, 0, R) = 1 (fire UP) and f(L', 1, R') = 0 (fire DOWN).

    The key for forced SCC: do the non-mover entries create cycles among
    non-good configs? A non-good config has ≥ 2 enabled procs or 0 enabled.
    The forced entries constrain the transition function, and some non-good
    configs may be forced into a cycle.
    """
    L = len(word)
    binary_set = set(binary_positions)

    # Track symbolic state: for each proc, track number of firings
    # State of proc p after k firings: depends on transition function
    # but for binary, state = k mod 2.

    # We'll track firing counts and determine which (L_count, S_count, R_count)
    # tuples are seen by each proc at each step.

    fire_count = [0] * n  # how many times each proc has fired so far

    mover_entries = []  # (proc, time, L_fires, S_fires, R_fires, direction)
    nonmover_entries = []  # (proc, time, L_fires, S_fires, R_fires)

    for t in range(L):
        mover = word[t]

        # Record mover entry
        left = (mover - 1) % n
        right = (mover + 1) % n
        mover_entries.append({
            'proc': mover,
            'time': t,
            'L_fires': fire_count[left],
            'S_fires': fire_count[mover],
            'R_fires': fire_count[right],
            'L_proc': left,
            'R_proc': right,
            'is_binary': mover in binary_set,
        })

        # Record non-mover entries (only for binary and their neighbors, for efficiency)
        for p in range(n):
            if p == mover:
                continue
            pl = (p - 1) % n
            pr = (p + 1) % n
            nonmover_entries.append({
                'proc': p,
                'time': t,
                'L_fires': fire_count[pl],
                'S_fires': fire_count[p],
                'R_fires': fire_count[pr],
            })

        # Update fire count
        fire_count[mover] += 1

    return mover_entries, nonmover_entries, fire_count


def analyze_binary_contexts(word, n, binary_positions):
    """
    For each binary proc, determine the (L_fires, R_fires) at UP and DOWN firings.

    Binary proc fires exactly twice (in a |W|=2 wiggle word where binary is not
    at the wiggle). First firing: S_fires=0 (UP). Second: S_fires=1 (DOWN).
    """
    L = len(word)
    binary_set = set(binary_positions)
    fire_count = [0] * n

    binary_contexts = {b: [] for b in binary_positions}

    for t in range(L):
        mover = word[t]
        if mover in binary_set:
            left = (mover - 1) % n
            right = (mover + 1) % n
            ctx = {
                'time': t,
                'S_fires': fire_count[mover],
                'L_fires': fire_count[left],
                'R_fires': fire_count[right],
                'L_proc': left,
                'R_proc': right,
                'direction': 'UP' if fire_count[mover] % 2 == 0 else 'DOWN',
            }
            binary_contexts[mover].append(ctx)
        fire_count[mover] += 1

    return binary_contexts


def check_context_collision(word, n, binary_positions):
    """
    Check if any processor sees the same (L_fires mod m_L, S_fires mod m_S, R_fires mod m_R)
    context both as a mover and as a non-mover.

    For binary proc with m=2: state = fires mod 2.
    For ternary proc with m=3: state = fires mod 3 (in the simplest case).

    A collision means: same (L_state, S_state, R_state) but required to produce
    different outputs (fire vs stay) → determinism contradiction.
    """
    L = len(word)
    binary_set = set(binary_positions)
    fire_count = [0] * n

    # For each proc, record contexts when it's a mover and when not
    mover_contexts = {p: set() for p in range(n)}
    nonmover_contexts = {p: set() for p in range(n)}

    for t in range(L):
        mover = word[t]

        for p in range(n):
            left = (p - 1) % n
            right = (p + 1) % n

            # Determine state moduli
            # Binary: mod 2. Non-binary: mod 3 (assume ternary for now).
            m_l = 2 if left in binary_set else 3
            m_s = 2 if p in binary_set else 3
            m_r = 2 if right in binary_set else 3

            ctx = (fire_count[left] % m_l,
                   fire_count[p] % m_s,
                   fire_count[right] % m_r)

            if p == mover:
                mover_contexts[p].add(ctx)
            else:
                nonmover_contexts[p].add(ctx)

        fire_count[mover] += 1

    # Check for collisions: same context as both mover and non-mover
    collisions = {}
    for p in range(n):
        overlap = mover_contexts[p] & nonmover_contexts[p]
        if overlap:
            collisions[p] = overlap

    return collisions


def analyze_forced_scc(word, n, binary_positions, state_counts=None):
    """
    Build the forced transition graph on non-good configs and check for SCC.

    For a given word and state vector, determine which transition entries are
    forced (mover entries and non-mover stay entries), then build the transition
    graph among all configs, identify good configs (those on the cycle), and
    check for SCCs among non-good configs.
    """
    if state_counts is None:
        # Default: binary=2, rest=3
        state_counts = [2 if i in set(binary_positions) else 3 for i in range(n)]

    L = len(word)
    total_configs = 1
    for m in state_counts:
        total_configs *= m

    # Compute good configs (configs visited by the seeded cycle)
    # Start at all-zeros, fire the word
    config = [0] * n
    good_configs = set()
    good_configs.add(tuple(config))

    configs_sequence = [tuple(config)]

    for t in range(L):
        mover = word[t]
        # Binary: flip 0↔1. Ternary: increment mod 3.
        # Actually, the transition depends on the context.
        # In the seeded model, the transition function is what we're trying to determine.
        # We can't compute good configs without knowing the transition function!

        # Instead: track firing counts and determine states symbolically.
        # For binary: state after k fires = k mod 2.
        # For ternary: state after k fires is UNKNOWN without the transition function.
        pass

    # The issue: we can't compute good configs without the transition function.
    # But we CAN determine the firing count pattern, and show that certain
    # (L_fires, S_fires, R_fires) tuples repeat → forced SCC.

    return None


def main():
    print("CIC Exploration 12: Forced SCC for Single-Wiggle Words")
    print("=" * 60)

    # PART 1: Enumerate single-wiggle words
    print("\nPART 1: Single-Wiggle Word Structure")
    print("-" * 60)

    n = 9
    binary_positions = [0, 3, 6]

    words = generate_wiggle_words_v2(n, binary_positions)
    print(f"n={n}, binary={binary_positions}")
    print(f"Generated {len(words)} single-wiggle words")

    for w in words[:6]:
        mc = Counter(w)
        # Find the wiggle: the edge with count > 2
        ec = Counter()
        for i in range(len(w)):
            a, b = w[i], w[(i+1) % len(w)]
            e = (min(a,b), max(a,b)) if abs(a-b) == 1 else (0, n-1)
            ec[e] += 1
        wiggle_edges = [(e, c) for e, c in ec.items() if c > 2]
        print(f"  {w} L={len(w)} wiggle={wiggle_edges}")

    # PART 2: Analyze binary contexts
    print("\nPART 2: Binary Firing Contexts")
    print("-" * 60)

    for w in words[:3]:
        print(f"\nWord: {w}")
        bc = analyze_binary_contexts(w, n, binary_positions)
        for b in binary_positions:
            print(f"  Binary {b}:")
            for ctx in bc[b]:
                print(f"    {ctx['direction']}: t={ctx['time']}, "
                      f"L({ctx['L_proc']})={ctx['L_fires']} fires, "
                      f"S={ctx['S_fires']}, "
                      f"R({ctx['R_proc']})={ctx['R_fires']} fires")

    # PART 3: Check context collisions
    print("\nPART 3: Context Collisions (Mover vs Non-Mover)")
    print("-" * 60)

    total_collision = 0
    total_words = 0
    collision_details = []

    for w in words:
        total_words += 1
        collisions = check_context_collision(w, n, binary_positions)
        if collisions:
            total_collision += 1
            if len(collision_details) < 5:
                collision_details.append((w, collisions))

    print(f"Words with context collisions: {total_collision}/{total_words}")

    for w, colls in collision_details[:3]:
        print(f"\n  {w}")
        for p, ctxs in colls.items():
            b_or_t = 'B' if p in set(binary_positions) else 'T'
            print(f"    Proc {p} ({b_or_t}): collisions at {ctxs}")

    # If there are collisions: same (L,S,R) as mover AND non-mover
    # → determinism contradiction → word is unrealizable. DONE.

    # PART 4: Analyze the collision mechanism
    print("\nPART 4: Collision Mechanism Analysis")
    print("-" * 60)

    # For words WITHOUT direct collisions, we need the SCC argument.
    # Let's check what the collision rate is.

    no_collision_words = []
    for w in words:
        collisions = check_context_collision(w, n, binary_positions)
        if not collisions:
            no_collision_words.append(w)

    print(f"Words WITHOUT direct collision: {len(no_collision_words)}")
    if no_collision_words:
        print("First few:")
        for w in no_collision_words[:3]:
            bc = analyze_binary_contexts(w, n, binary_positions)
            ec = Counter()
            for i in range(len(w)):
                a, b = w[i], w[(i+1) % len(w)]
                e = (min(a,b), max(a,b)) if abs(a-b) == 1 else (0, n-1)
                ec[e] += 1
            wiggle_edges = [(e, c) for e, c in ec.items() if c > 2]
            print(f"  {w} wiggle={wiggle_edges}")

    # PART 5: Test multiple n values
    print("\nPART 5: Collision universality across n")
    print("-" * 60)

    for n_val in range(6, 13):
        # Find valid binary placements with max_gap <= 2
        # For k=3: positions (0, g1+1, g1+g2+2) with g1,g2 >= 1, g3 >= 1
        # Try balanced: gaps as equal as possible
        k = 3
        g = (n_val - k) // k
        r = (n_val - k) % k
        gaps = [g + (1 if i < r else 0) for i in range(k)]
        bp = []
        pos = 0
        for i in range(k):
            bp.append(pos)
            pos += 1 + gaps[i]
        if pos != n_val:
            continue

        ws = generate_wiggle_words_v2(n_val, bp)
        if not ws:
            print(f"  n={n_val} k={k} gaps={gaps}: 0 wiggle words")
            continue

        ncoll = sum(1 for w in ws
                    if check_context_collision(w, n_val, bp))
        print(f"  n={n_val} k={k} gaps={gaps} binary={bp}: "
              f"{ncoll}/{len(ws)} collision "
              f"({100*ncoll/len(ws):.0f}%)")

    # PART 6: All survivors from Exploration 11 — check collisions
    print("\nPART 6: Check Expl 11 survivors for collisions")
    print("-" * 60)

    # The actual survivors from proof8.py at n=9 gaps=(2,2,2)
    # were at max_L=24. Generate them.
    # Use the DFS approach to find the actual survivors.

    # For speed, just check a few known survivor patterns
    test_survivors = [
        # n=9, binary={0,3,6}, gaps=(2,2,2)
        # Near-sweep CCW with wiggle at different positions
        ([0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,2,1], 9, [0,3,6]),
        ([0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,5,4,3,2,1], 9, [0,3,6]),
        ([0,8,7,6,5,4,3,2,1,0,8,7,8,7,6,5,4,3,2,1], 9, [0,3,6]),
        # n=8, binary={0,3,6}, gaps=(2,2,1)
        ([0,7,6,5,4,3,2,1,0,7,6,5,4,5,4,3,2,1], 8, [0,3,6]),
        # n=7
        ([0,6,5,4,3,2,1,0,6,5,4,3,2,3,2,3,2,1], 7, [0,2,4]),
    ]

    for w, n_val, bp in test_survivors:
        mc = Counter(w)
        fair = all(mc.get(p,0) >= 2 for p in range(n_val))
        bpar = all(mc.get(b,0) % 2 == 0 for b in bp)
        if not (fair and bpar):
            print(f"  {w[:10]}... NOT VALID (fair={fair}, bpar={bpar})")
            continue

        colls = check_context_collision(w, n_val, bp)
        if colls:
            procs = list(colls.keys())
            print(f"  n={n_val} {w[:15]}... COLLISION at procs {procs}")
        else:
            print(f"  n={n_val} {w[:15]}... NO collision")

    # PART 7: Non-binary state count matters!
    print("\nPART 7: Effect of non-binary state count")
    print("-" * 60)

    # The collision check assumes ternary (mod 3) for non-binary.
    # What if some non-binary procs have 4+ states?
    # With more states, there are MORE possible contexts, so FEWER collisions.
    # The collision check with mod 3 is the HARDEST case.
    # If collision works for ternary, it works for any m_i >= 3.

    # Actually wait — with quaternary (m=4), state after k fires = k mod 4 (?)
    # No! State after k fires depends on the transition function, not just k.
    # The mod-m approach assumes the simplest transition: increment mod m.
    # Real transitions could be different.

    # For the FORCED SCC argument: we don't assume a specific transition.
    # We show that the FORCED entries (from mover and non-mover constraints)
    # create an SCC. The collision approach is a special case where the same
    # context forces contradictory outputs.

    # The more general SCC approach: build a graph where each non-good config
    # has a forced successor, and show the graph has a cycle.
    # This requires enumerating configs, which is state-count-dependent.

    # For the analytical proof: we need to show the collision exists
    # for ALL sub-threshold state vectors with ≥3 non-adjacent binary.

    print("The collision check uses firing-count mod m_i.")
    print("For binary: mod 2 (exact). For ternary: mod 3.")
    print("For quaternary: mod 4 (different contexts possible).")
    print("Collision for ternary is the worst case: fewest contexts.")
    print("If collision holds for all-ternary, it holds for any m_i >= 3.")
    print()
    print("BUT: the mod-m approach assumes state = fires mod m.")
    print("Real transitions could differ. Need transition-independent argument.")


if __name__ == "__main__":
    main()
