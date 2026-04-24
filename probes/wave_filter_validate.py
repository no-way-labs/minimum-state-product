"""
Validate the bidirectional wave filter theory across all witnesses.

Key claims to test:
1. In every witness, exactly one processor is bidirectional in the good cycle
2. That processor always has ≥ 4 states
3. Ternary processors between binary neighbors are always unidirectional

Also: analyze the "phase tracking" structure of the quaternary processor.
"""
import itertools
from collections import Counter

# ============================================================
# n=5 witness: ms = [2, 2, 2, 3, 4], product = 96
# ============================================================

def analyze_witness(name, ms, rules_dict, good_cycle=None):
    n = len(ms)

    def f(i, L, S, R):
        return rules_dict[i][(L, S, R)]

    def privileged_set(config):
        priv = []
        for i in range(n):
            L = config[(i-1) % n]
            S = config[i]
            R = config[(i+1) % n]
            if f(i, L, S, R) != S:
                priv.append(i)
        return priv

    def apply_move(config, i):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        lst = list(config)
        lst[i] = f(i, L, S, R)
        return tuple(lst)

    # Find good cycle if not provided
    if good_cycle is None:
        c = tuple([0]*n)
        path = [c]
        seen = {c: 0}
        while True:
            priv = privileged_set(path[-1])
            if len(priv) != 1:
                # Search for single-privilege config
                for c in itertools.product(*(range(m) for m in ms)):
                    if len(privileged_set(c)) == 1:
                        path = [c]
                        seen = {c: 0}
                        break
                continue
            mover = priv[0]
            next_c = apply_move(path[-1], mover)
            if next_c in seen:
                cycle_start = seen[next_c]
                good_cycle = path[cycle_start:]
                break
            seen[next_c] = len(path)
            path.append(next_c)

    # Find movers
    movers = []
    for idx in range(len(good_cycle)):
        c = good_cycle[idx]
        c_next = good_cycle[(idx + 1) % len(good_cycle)]
        for j in range(n):
            if c[j] != c_next[j]:
                movers.append(j)
                break

    print(f"\n{'='*70}")
    print(f"WITNESS: {name}")
    print(f"ms = {ms}, product = {eval('*'.join(str(m) for m in ms))}, cycle length = {len(good_cycle)}")
    print(f"{'='*70}")

    # Directionality analysis for each processor
    print(f"\nDirectionality analysis:")
    bidirectional_procs = []
    for i in range(n):
        enters_from = {'left': False, 'right': False}
        left_nb = (i - 1) % n
        right_nb = (i + 1) % n
        for idx in range(len(good_cycle)):
            if movers[idx] == i:
                prev = movers[(idx - 1) % len(good_cycle)]
                if prev == left_nb:
                    enters_from['left'] = True
                elif prev == right_nb:
                    enters_from['right'] = True

        bidir = enters_from['left'] and enters_from['right']
        nb_types = f"(L=P{left_nb}[m={ms[left_nb]}], R=P{right_nb}[m={ms[right_nb]}])"
        dir_str = "BIDIR" if bidir else ("LEFT" if enters_from['left'] else ("RIGHT" if enters_from['right'] else "SELF"))

        moves = sum(1 for m in movers if m == i)
        print(f"  P{i} (m={ms[i]}): {dir_str:5s} | {moves:2d} moves | neighbors {nb_types}")

        if bidir:
            bidirectional_procs.append(i)

    # Summary
    print(f"\n  Bidirectional processors: {[f'P{i}(m={ms[i]})' for i in bidirectional_procs]}")

    # Check: is any bidirectional processor between two binary neighbors?
    for i in bidirectional_procs:
        left_binary = (ms[(i-1) % n] == 2)
        right_binary = (ms[(i+1) % n] == 2)
        both_binary = left_binary and right_binary
        print(f"  P{i}: both neighbors binary? {both_binary}")

    # Check: is any ternary processor between two binary neighbors bidirectional?
    for i in range(n):
        if ms[i] == 3 and ms[(i-1)%n] == 2 and ms[(i+1)%n] == 2:
            is_bidir = i in bidirectional_procs
            print(f"  P{i} (ternary between two binaries): bidirectional? {is_bidir}")

    # Phase analysis for quaternary processor
    quat_procs = [i for i in range(n) if ms[i] == 4]
    for qi in quat_procs:
        print(f"\n  Quaternary P{qi} phase analysis:")
        for idx in range(len(good_cycle)):
            if movers[idx] == qi:
                c = good_cycle[idx]
                L = c[(qi-1)%n]
                S = c[qi]
                R = c[(qi+1)%n]
                new_S = f(qi, L, S, R)
                prev = movers[(idx-1) % len(good_cycle)]
                nxt = movers[(idx+1) % len(good_cycle)]
                left_nb_state = c[(qi-1)%n]
                right_nb_state = c[(qi+1)%n]
                print(f"    step {idx:2d}: s={S}->{new_S}  L={L} R={R}  "
                      f"(P{prev}->P{qi}->P{nxt})")

        # State decomposition: can quaternary states be decomposed as (left_bit, right_bit)?
        print(f"\n  Quaternary P{qi} state decomposition test:")
        states_in_cycle = [(c[qi], c[(qi-1)%n], c[(qi+1)%n])
                          for c in good_cycle]

        # For each state, what (L, R) contexts does it appear with?
        state_contexts = {}
        for s, L, R in states_in_cycle:
            if s not in state_contexts:
                state_contexts[s] = set()
            state_contexts[s].add((L, R))

        for s in sorted(state_contexts):
            print(f"    state {s}: seen with (L,R) = {sorted(state_contexts[s])}")

    return bidirectional_procs


# ============================================================
# Run analysis on all witnesses
# ============================================================

# n=5 witness
rules_5 = {
    0: {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
        (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,(3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
    1: {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
    2: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
        (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0},
    3: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,0,3):0,(0,1,0):1,(0,1,1):2,(0,1,2):1,(0,1,3):0,
        (0,2,0):0,(0,2,1):2,(0,2,2):2,(0,2,3):2,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,1,3):1,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
    4: {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):1,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):1,
        (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):0,(1,3,0):3,(1,3,1):0,
        (2,0,0):0,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):0,(2,3,0):3,(2,3,1):0},
}

gc_5 = [(0,0,0,0,0),(1,0,0,0,0),(1,1,0,0,0),(1,1,1,0,0),(1,1,1,1,0),(1,1,1,1,1),
        (0,1,1,1,1),(0,0,1,1,1),(0,0,0,1,1),(0,0,0,2,1),(0,0,1,2,1),(0,0,1,0,1),
        (0,0,1,0,2),(0,0,1,2,2),(0,0,1,2,3),(0,0,1,1,3),(0,0,0,1,3),(0,0,0,0,3)]

analyze_witness("n=5, product=96", [2,2,2,3,4], rules_5, gc_5)

# n=8 witness
rules_8 = {
    0: {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
    1: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
    2: {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
    3: {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
    4: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,(3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
    5: {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
    6: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,(2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
    7: {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
}

analyze_witness("n=8, product=2592", [2,2,3,4,3,3,2,3], rules_8)


# ============================================================
# Now the critical test: EQUILIBRIUM analysis
# For each processor, for each state s, which (L, R) pairs
# leave it non-privileged?
# ============================================================

print("\n\n" + "="*70)
print("EQUILIBRIUM ANALYSIS: Non-privileged contexts per state")
print("="*70)

for name, ms, rules_dict in [
    ("n=5", [2,2,2,3,4], rules_5),
    ("n=8", [2,2,3,4,3,3,2,3], rules_8),
]:
    n = len(ms)
    print(f"\n--- {name} ---")

    for i in range(n):
        m_L = ms[(i-1)%n]
        m_S = ms[i]
        m_R = ms[(i+1)%n]

        def fi(L, S, R):
            return rules_dict[i][(L, S, R)]

        print(f"\n  P{i} (m={m_S}, L_range={m_L}, R_range={m_R}):")
        for s in range(m_S):
            non_priv = []
            priv = []
            for L in range(m_L):
                for R in range(m_R):
                    if fi(L, s, R) == s:
                        non_priv.append((L, R))
                    else:
                        priv.append((L, R))
            print(f"    state {s}: non-priv at {non_priv}, priv at {priv}")


# ============================================================
# CRITICAL TEST: For ternary P7 in n=8 (between two binaries),
# can we see why it can be ternary?
# Answer: it only handles ONE direction, so it doesn't need
# to independently track left and right phases.
# ============================================================

print("\n\n" + "="*70)
print("P7 (n=8): WHY TERNARY SUFFICES")
print("="*70)

print("""
P7 sits between P6 (binary) and P0 (binary).
In the good cycle, the token ONLY enters P7 from P6 (unidirectional).
P7 never needs to accept a token from P0.

P7's role: relay the token from P6 through to P0.
It's a one-way conduit, not a bidirectional filter.

The bidirectional filtering is done by P3 (quaternary),
which accepts tokens from both P2 and P4.

P7's state sequence in cycle: 0 -> 1 -> 2 -> 1 -> 0
P7 uses all 3 states, but only for unidirectional relay.
""")

# Verify P7's state trajectory
print("P7 state trajectory in good cycle:")
gc_8_start = tuple([0]*8)
c = gc_8_start
path = [c]
seen = {c: 0}
while True:
    priv = []
    for i in range(8):
        L = c[(i-1)%8]
        S = c[i]
        R = c[(i+1)%8]
        if rules_8[i][(L,S,R)] != S:
            priv.append(i)
    if len(priv) != 1:
        break
    mover = priv[0]
    nc = list(c)
    nc[mover] = rules_8[mover][(c[(mover-1)%8], c[mover], c[(mover+1)%8])]
    nc = tuple(nc)
    if nc in seen:
        cycle = path[seen[nc]:]
        break
    seen[nc] = len(path)
    path.append(nc)
    c = nc

p7_states = [c[7] for c in cycle]
p7_changes = [(idx, cycle[idx][7], cycle[(idx+1)%len(cycle)][7])
              for idx in range(len(cycle))
              if cycle[idx][7] != cycle[(idx+1)%len(cycle)][7]]
print(f"  P7 state sequence: {p7_states}")
print(f"  P7 transitions: {p7_changes}")
print(f"  P7 states used: {sorted(set(p7_states))}")
