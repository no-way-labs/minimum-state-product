#!/usr/bin/env python3
"""
PART 2: Deep analysis of sorry cases 1077 and 1121.

Sorry 1012 (both LL,RR tight with fL > a+1, fR > a+1) is VERIFIED to be 0
across all tested configurations. No proof needed — it never happens.

Sorry 1077 and 1121 DO occur. But the theorem says hasEntryConflict gc,
so these cycles must have entry conflicts SOMEWHERE (not necessarily at the
chain-end proc). Let's verify this and find WHERE the EC is.

Key question: In a sorry-1077/1121 case, where is the actual EC?
Can we find it systematically?

The sorry structure for 1121 (symmetric case of 1077):
  - t = sandwiched ternary, bL = left(t) binary, bR = right(t) binary
  - Phase [a+1, s) between consecutive t-fires
  - moverAt(a+1) = bL (first interior step fires left binary)
  - fR = first bR fire in interior, fR > a+1
  - RR = right(right(t)) fires before fR, last RR is at fR-1 (tight)
  - fRR = first RR in [a+1, fR)
  - RRR = right^3(t) fires in [a+1, fRR)

The Lean proof has already handled the case where there's no RRR fire.
The sorry fires when the chain extends ONE more level: RRR fires before first RR.
"""

import itertools
from collections import Counter, defaultdict


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


def find_all_entry_conflicts(word, cycle, ms, n):
    """Find ALL entry conflicts (processor, mover_step, nonmover_step)."""
    ell = len(word)
    ecs = []
    for p in range(n):
        pL = (p - 1) % n
        pR = (p + 1) % n
        mover_steps = {}  # triple -> step
        nonmover_steps = {}  # triple -> [steps]
        for step in range(ell):
            triple = (cycle[step][pL], cycle[step][p], cycle[step][pR])
            if word[step] == p:
                mover_steps[triple] = step
            else:
                if triple not in nonmover_steps:
                    nonmover_steps[triple] = []
                nonmover_steps[triple].append(step)
        for triple in mover_steps:
            if triple in nonmover_steps:
                for nm_step in nonmover_steps[triple]:
                    ecs.append({
                        'proc': p,
                        'mover_step': mover_steps[triple],
                        'nonmover_step': nm_step,
                        'triple': triple,
                    })
    return ecs


def analyze_sorry_case(word, cycle, ms, n, t, a_step, s_step, sorry_type):
    """Deep analysis of a single sorry case."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    LL = (t - 2) % n
    RR = (t + 2) % n
    LLL = (t - 3) % n
    RRR = (t + 3) % n

    # Interior
    if s_step > a_step:
        interior = list(range(a_step + 1, s_step))
    else:
        interior = list(range(a_step + 1, ell)) + list(range(0, s_step))

    int_movers = [word[st] for st in interior]

    # Find EC in the cycle
    ecs = find_all_entry_conflicts(word, cycle, ms, n)

    # Classify which ECs are "within" or "near" this phase
    phase_steps = set(interior) | {a_step, s_step}
    nearby_ecs = []
    for ec in ecs:
        if ec['mover_step'] in phase_steps or ec['nonmover_step'] in phase_steps:
            nearby_ecs.append(ec)

    # For sorry 1121: chain is bL, LL, LLL going LEFT from t.
    # First interior step fires bL. Then somewhere RR fires before fR.
    # But the sorry is about the RIGHT chain: fR > a+1, RR tight to fR, RRR fires.
    # Actually sorry 1121: fL = a+1 (first step fires bL), then look RIGHT.
    # fR > a+1, last RR before fR is at fR-1, and RRR fires before first RR.

    # The chain goes: bR (at fR), RR (tight, at fR-1), and RRR fires before first RR.
    # So the interior near fR looks like: ..., RRR, ..., RR_first, ..., RR_last=fR-1, fR=bR

    # For sorry 1077: fR = a+1 (first step fires bR), then look LEFT.
    # fL > a+1, last LL before fL is at fL-1, and LLL fires before first LL.

    # Find the EC that resolves this sorry.
    # The Lean code's goal: show hasEntryConflict gc.
    # So we just need to find ANY EC in the cycle.

    # Key insight: the chain-continuation STILL produces EC, just one level deeper.
    # After RRR fires in [a+1, fRR), either:
    # (a) right^4(t) doesn't fire in [a+1, first_RRR) -> EC at RRR
    # (b) right^4(t) fires -> chain extends again. But ring is finite.

    # Let's trace the full chain
    if sorry_type == 1121:
        # Chain goes RIGHT from t: bR -> RR -> RRR -> ...
        chain = []
        current = bR
        fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
        fR_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

        # Build the chain
        search_end = fR_int_idx  # before first bR fire
        prev_fire_idx = fL_int_idx  # bL fires at this interior index (= 0)
        current = RR
        depth = 0

        while depth < n:
            # Find first fire of 'current' in interior[prev_fire_idx+1 : search_end]
            found = None
            for i in range(prev_fire_idx + 1, search_end):
                if word[interior[i]] == current:
                    found = i
                    break
            if found is None:
                chain.append({'proc': current, 'depth': depth, 'found': False})
                break
            chain.append({'proc': current, 'depth': depth, 'found': True, 'idx': found})
            prev_fire_idx = found
            current = (current + 1) % n  # go further right
            depth += 1

        # Find which chain proc has EC
        chain_ec = None
        for ec in ecs:
            for c in chain:
                if ec['proc'] == c['proc']:
                    chain_ec = (ec, c)
                    break
            if chain_ec:
                break

        return {
            'sorry_type': sorry_type,
            'chain': chain,
            'chain_ec': chain_ec,
            'total_ecs': len(ecs),
            'nearby_ecs': len(nearby_ecs),
            'ec_procs': list(set(ec['proc'] for ec in ecs)),
            'int_movers': int_movers,
            't': t, 'a': a_step, 's': s_step,
        }

    elif sorry_type == 1077:
        # Chain goes LEFT from t: bL -> LL -> LLL -> ...
        chain = []
        fR_int_idx = 0  # bR fires at first interior step
        fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)

        search_end = fL_int_idx
        prev_fire_idx = fR_int_idx
        current = LL
        depth = 0

        while depth < n:
            found = None
            for i in range(prev_fire_idx + 1, search_end):
                if word[interior[i]] == current:
                    found = i
                    break
            if found is None:
                chain.append({'proc': current, 'depth': depth, 'found': False})
                break
            chain.append({'proc': current, 'depth': depth, 'found': True, 'idx': found})
            prev_fire_idx = found
            current = (current - 1) % n  # go further left
            depth += 1

        chain_ec = None
        for ec in ecs:
            for c in chain:
                if ec['proc'] == c['proc']:
                    chain_ec = (ec, c)
                    break
            if chain_ec:
                break

        return {
            'sorry_type': sorry_type,
            'chain': chain,
            'chain_ec': chain_ec,
            'total_ecs': len(ecs),
            'nearby_ecs': len(nearby_ecs),
            'ec_procs': list(set(ec['proc'] for ec in ecs)),
            'int_movers': int_movers,
            't': t, 'a': a_step, 's': s_step,
        }


def check_sorry_and_analyze(word, cycle, ms, n, t):
    """Find sorry-hitting phases and analyze them."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    LL = (t - 2) % n
    RR = (t + 2) % n
    LLL = (t - 3) % n
    RRR = (t + 3) % n

    t_fires = sorted(i for i in range(ell) if word[i] == t)
    if len(t_fires) < 2:
        return []

    results = []
    for idx in range(len(t_fires)):
        s_step = t_fires[idx]
        a_step = t_fires[(idx - 1) % len(t_fires)]

        if s_step > a_step:
            interior = list(range(a_step + 1, s_step))
        else:
            interior = list(range(a_step + 1, ell)) + list(range(0, s_step))

        if not interior:
            continue

        J = sum(1 for st in interior if word[st] == bL)
        K = sum(1 for st in interior if word[st] == bR)
        if J < 1 or K < 1:
            continue

        int_movers = [word[st] for st in interior]
        fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
        fR_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

        # Sorry 1121: fL at start (idx 0), fR not at start
        if fL_int_idx == 0 and fR_int_idx > 0:
            # Check RR tight to fR
            steps_before_fR = interior[:fR_int_idx]
            rr_idx = [i for i, st in enumerate(steps_before_fR) if word[st] == RR]
            if rr_idx and rr_idx[-1] == fR_int_idx - 1:
                # RR tight. Check RRR fires before first RR
                first_rr_int_idx = rr_idx[0]
                steps_before_fRR = interior[:first_rr_int_idx]
                if any(word[st] == RRR for st in steps_before_fRR):
                    analysis = analyze_sorry_case(word, cycle, ms, n, t,
                                                  a_step, s_step, 1121)
                    results.append(analysis)

        # Sorry 1077: fR at start (idx 0), fL not at start
        if fR_int_idx == 0 and fL_int_idx > 0:
            steps_before_fL = interior[:fL_int_idx]
            ll_idx = [i for i, st in enumerate(steps_before_fL) if word[st] == LL]
            if ll_idx and ll_idx[-1] == fL_int_idx - 1:
                first_ll_int_idx = ll_idx[0]
                steps_before_fLL = interior[:first_ll_int_idx]
                if any(word[st] == LLL for st in steps_before_fLL):
                    analysis = analyze_sorry_case(word, cycle, ms, n, t,
                                                  a_step, s_step, 1077)
                    results.append(analysis)

    return results


# Run analysis
print("="*70)
print("DEEP ANALYSIS OF SORRY CASES 1077/1121")
print("="*70)

# First, analyze the specific example
# word=(0, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4, 3, 4, 0, 1), t=1
n, ms = 5, [2, 3, 2, 3, 2]
word = (0, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4, 3, 4, 0, 1)
cycle = build_cycle(ms, n, word)
print(f"\nExample: word={word}")
print(f"n={n}, ms={ms}")
print(f"Cycle length: {len(word)}")
print(f"Configs: {cycle is not None}")

# Find ALL entry conflicts
ecs = find_all_entry_conflicts(word, cycle, ms, n)
print(f"\nAll entry conflicts ({len(ecs)}):")
for ec in ecs[:10]:
    print(f"  proc={ec['proc']}, mover_step={ec['mover_step']}, "
          f"nonmover_step={ec['nonmover_step']}, triple={ec['triple']}")

# Analyze sorry cases
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
print(f"\nSandwiched: {sandwiched}")

for t in sandwiched:
    analyses = check_sorry_and_analyze(word, cycle, ms, n, t)
    for a in analyses:
        print(f"\n--- Sorry {a['sorry_type']} at t={a['t']} ---")
        print(f"  Phase: [{a['a']}, {a['s']})")
        print(f"  Interior movers: {a['int_movers']}")
        print(f"  Chain:")
        for c in a['chain']:
            if c['found']:
                print(f"    depth={c['depth']}: proc={c['proc']} fires at int_idx={c['idx']}")
            else:
                print(f"    depth={c['depth']}: proc={c['proc']} NOT FOUND -> EC here")
        print(f"  EC procs in cycle: {a['ec_procs']}")
        if a['chain_ec']:
            ec, ch = a['chain_ec']
            print(f"  Chain-relevant EC: proc={ec['proc']} at steps "
                  f"{ec['mover_step']},{ec['nonmover_step']}")

print("\n" + "="*70)
print("SYSTEMATIC ANALYSIS: Chain termination patterns")
print("="*70)

# Analyze ALL sorry cases for pattern
words = enumerate_mover_words(ms, n, 18)
chain_termination = Counter()
chain_depths = Counter()
always_has_ec = True
no_ec_examples = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    for t in sandwiched:
        analyses = check_sorry_and_analyze(word, cycle, ms, n, t)
        for a in analyses:
            chain = a['chain']
            if chain:
                last = chain[-1]
                depth = last['depth']
                chain_depths[depth] += 1
                if not last['found']:
                    chain_termination['terminates'] += 1
                else:
                    chain_termination['extends'] += 1

            # Check: does the cycle have EC?
            all_ecs = find_all_entry_conflicts(word, cycle, ms, n)
            if not all_ecs:
                always_has_ec = False
                no_ec_examples.append((word, t, a))

print(f"\nChain depths: {dict(sorted(chain_depths.items()))}")
print(f"Chain termination: {dict(chain_termination)}")
print(f"All sorry-case cycles have EC: {always_has_ec}")
if no_ec_examples:
    print(f"NO-EC examples: {len(no_ec_examples)}")
    for w, t, a in no_ec_examples[:3]:
        print(f"  word={w}, t={t}")

# Key insight: since the ring has only n procs, and the chain extends
# one proc at a time, after at most n-4 steps the chain wraps around
# and hits a proc it's already seen — specifically a binary proc.
# At n=5: chain can only extend 1 step (5-4=1) before hitting the
# other side of the ring.

print("\n" + "="*70)
print("PROOF ARGUMENT")
print("="*70)

# Let's trace what happens when the chain hits the ring boundary.
# At n=5, ms=[2,3,2,3,2], sandwiched t:
# If t=1: bL=0(binary), bR=2(binary), LL=4(binary), RR=3(ternary), LLL=3, RRR=4
# Wait: LL = (1-2)%5 = 4 (binary), RR = (1+2)%5 = 3 (ternary)
# LLL = (1-3)%5 = 3 (ternary), RRR = (1+3)%5 = 4 (binary)

for t in sandwiched:
    bL = (t-1) % n
    bR = (t+1) % n
    procs_with_types = []
    for d in range(-4, 5):
        p = (t + d) % n
        ptype = 'B' if ms[p] == 2 else 'T'
        procs_with_types.append(f"{p}({ptype})")
    print(f"\nt={t}: ring from t-4 to t+4: {' '.join(procs_with_types)}")
    print(f"  bL={bL}(m={ms[bL]}), bR={bR}(m={ms[bR]})")
    print(f"  LL={(t-2)%n}(m={ms[(t-2)%n]}), RR={(t+2)%n}(m={ms[(t+2)%n]})")
    print(f"  LLL={(t-3)%n}(m={ms[(t-3)%n]}), RRR={(t+3)%n}(m={ms[(t+3)%n]})")

print("""
KEY OBSERVATION:
For sorry 1121 at t=1, n=5, ms=[2,3,2,3,2]:
  The right chain is: bR=2(B), RR=3(T), RRR=4(B)
  RRR = 4 is BINARY. RRR = left(bL) = left(left(left(t))).

  At n=5 with this state vector, right^3(t) wraps around to left^2(t) = LL!
  Actually (1+3)%5 = 4 = (1-1-1)%5? No. (1-2)%5 = 4.
  So RRR = (t+3)%n = 4 = LL = (t-2)%n = 4. Yes!

  At n=5, the chain from the right hits the proc that's also LL.
  This means the "RRR fires before first RR" is actually
  "LL fires before first RR". And LL also appears in the LEFT chain.

  The left chain (from sorry 1077): bL=0(B) -> then the left chain would
  go to LL=4(B). And the right chain: bR=2(B) -> RR=3(T) -> RRR=4(B).
  So both chains converge on proc 4!
""")

# Let's verify: in sorry 1121 cases, is the "RRR" processor always
# a processor that's also reachable from the other chain?
print("\n" + "="*70)
print("CHAIN CONVERGENCE CHECK")
print("="*70)

for t in sandwiched:
    # Left chain: t -> bL -> LL -> LLL -> ...
    left_chain = []
    p = (t - 1) % n
    for d in range(1, n):
        p = (t - d) % n
        left_chain.append(p)

    # Right chain: t -> bR -> RR -> RRR -> ...
    right_chain = []
    for d in range(1, n):
        p = (t + d) % n
        right_chain.append(p)

    print(f"\nt={t}:")
    print(f"  Left chain:  {left_chain}")
    print(f"  Right chain: {right_chain}")

    # Find convergence point
    for i, lp in enumerate(left_chain):
        for j, rp in enumerate(right_chain):
            if lp == rp:
                print(f"  Converge at proc {lp}: left depth {i}, right depth {j}")
                break
        else:
            continue
        break
