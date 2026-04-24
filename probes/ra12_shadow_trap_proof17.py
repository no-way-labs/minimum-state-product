"""
Shadow Trap Proof — Part 17: Understanding the mover-override forced graph.

KEY REALIZATION: The forced entry table uses MOVER ENTRIES ONLY.
Non-mover entries are identity maps and don't create forced transitions.
A proc p is "forced-privileged" iff its context matches a MOVER entry.

The forced graph: for each config c, find all procs p whose context
matches a mover entry (p, L, S, R) -> S' with S' != S. Fire the
lowest-index such proc.

Questions:
1. Does every non-good config have at least one forced proc?
   (Not necessarily — verified above that some don't.)
2. When a forced proc fires, is the result non-good?
   (Not necessarily with entry conflicts.)
3. Despite (1) and (2), does the forced graph always have a cycle?

From the 512/512 verification: YES, the forced graph always has a
CL-length cycle. But the cycle might not be reachable from all
non-good configs. The claim is just that such a cycle EXISTS.

Let me investigate: what's the structure of the cycle? Is it the
same shadow cycle from the existing proofs?
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

# Use the same setup as ra12_farshift_claims.py
def enumerate_sweep_words(ms, n, max_words=100):
    CL = sum(ms)
    target_fc = {p: ms[p] for p in range(n)}
    results = []
    def dfs(word, fc):
        if len(results) >= max_words: return
        if len(word) == CL:
            d = 0
            for i in range(CL):
                diff = (word[(i+1) % CL] - word[i]) % n
                if diff == 1: d += 1
                elif diff == n-1: d -= 1
            if abs(d) >= 2:
                config = [0] * n
                for p in word: config[p] = (config[p] + 1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return
        last = word[-1]
        for nxt in [(last-1) % n, (last+1) % n]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1; word.append(nxt)
                dfs(word, fc); word.pop(); fc[nxt] -= 1
    for p in range(n):
        fc = {q: 0 for q in range(n)}; fc[p] = 1
        dfs([p], fc)
        if len(results) >= max_words: break
    return results

def enumerate_value_sequences(m):
    seqs = []
    def dfs(seq, rem):
        if rem == 0:
            if seq[-1] == 0: seqs.append(tuple(seq))
            return
        for v in range(m):
            if v != seq[-1]:
                if rem == 1 and v != 0: continue
                seq.append(v); dfs(seq, rem-1); seq.pop()
    dfs([0], m)
    return seqs

def build_cycle(ms, n, word, combo):
    CL = len(word)
    fc = [0]*n
    state = [combo[p][0] for p in range(n)]
    configs = [tuple(state)]
    for s in range(CL):
        p = word[s]; fc[p] += 1; state[p] = combo[p][fc[p]]
        configs.append(tuple(state))
    if configs[-1] != configs[0]: return None
    configs = configs[:-1]
    if len(set(configs)) != CL: return None
    return configs

# ====================================================================
# CLEAN FORCED GRAPH: mover entries only
# ====================================================================

def extract_mover_entries(ms, n, word, configs):
    """Extract ONLY mover entries from the good cycle.
    Returns: dict mapping (proc, L, S, R) -> S' where S' != S.
    """
    CL = len(word)
    mover_entries = {}
    for s in range(CL):
        p = word[s]
        c = configs[s]
        L, S, R = get_context(c, p, n)
        Sp = configs[(s+1) % CL][p]
        key = (p, L, S, R)
        if key in mover_entries:
            if mover_entries[key] != Sp:
                pass  # Duplicate context with different target — shouldn't happen for valid cycle
        mover_entries[key] = Sp
    return mover_entries

def forced_step_mover_only(n, c, mover_entries):
    """Find lowest-index forced-privileged proc using mover entries only."""
    for p in range(n):
        L, S, R = get_context(c, p, n)
        key = (p, L, S, R)
        if key in mover_entries and mover_entries[key] != S:
            nxt = list(c)
            nxt[p] = mover_entries[key]
            return tuple(nxt), p
    return None, None

# ====================================================================
# ANALYSIS: Cycle existence with mover-only forced graph
# ====================================================================

# n=5 non-consecutive
n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)

print(f"n={n}, ms={ms}, CL={CL}")

words = enumerate_sweep_words(ms, n, max_words=50)
val_seqs = {p: enumerate_value_sequences(ms[p]) for p in range(n)}

total = 0
cycle_found = 0
no_cycle = 0
cycle_lengths = defaultdict(int)

for word in words:
    for combo_idx in itertools.product(*[range(len(val_seqs[p])) for p in range(n)]):
        combo = tuple(val_seqs[p][combo_idx[p]] for p in range(n))
        configs = build_cycle(ms, n, word, combo)
        if configs is None: continue
        total += 1

        good_set = set(configs)
        mover_entries = extract_mover_entries(ms, n, word, configs)

        # Check for duplicate mover contexts
        dup = len(mover_entries) < CL
        if dup:
            continue  # Skip instances with duplicate mover contexts

        # Try to find a shadow cycle
        g0 = configs[0]
        found = False
        for q in range(n):
            if found: break
            for d in range(1, ms[q]):
                c = list(g0); c[q] = (c[q]+d) % ms[q]; c = tuple(c)
                if c in good_set: continue
                nxt, p = forced_step_mover_only(n, c, mover_entries)
                if nxt is None: continue

                # Follow orbit
                orbit = [c]; oset = {c}; cur = c
                stuck = False
                for _ in range(CL * 3):
                    nxt, p = forced_step_mover_only(n, cur, mover_entries)
                    if nxt is None:
                        stuck = True; break
                    if nxt in oset:
                        idx = orbit.index(nxt)
                        cycle = orbit[idx:]
                        cycle_found += 1
                        cycle_lengths[len(cycle)] += 1
                        found = True; break
                    orbit.append(nxt); oset.add(nxt); cur = nxt
                if found: break

        if not found:
            no_cycle += 1

print(f"\nTotal instances (no dup contexts): {total}")
print(f"Found shadow cycle: {cycle_found}")
print(f"No shadow cycle: {no_cycle}")
print(f"Cycle lengths: {dict(cycle_lengths)}")

# ====================================================================
# DEEPER: Analyze the orbit structure
# ====================================================================

print("\n\n" + "="*60)
print("ORBIT STRUCTURE ANALYSIS")
print("="*60)

# For one specific instance, trace the full orbit
for word in words[:1]:
    for combo_idx in itertools.product(*[range(len(val_seqs[p])) for p in range(n)]):
        combo = tuple(val_seqs[p][combo_idx[p]] for p in range(n))
        configs = build_cycle(ms, n, word, combo)
        if configs is None: continue

        good_set = set(configs)
        mover_entries = extract_mover_entries(ms, n, word, configs)

        print(f"\nWord: {word}")
        print(f"Good cycle:")
        for k in range(CL):
            p = word[k]
            g = configs[k]
            L, S, R = get_context(g, p, n)
            Sp = configs[(k+1) % CL][p]
            print(f"  g_{k:2d}={g}, mover={p}, ({L},{S},{R})->{Sp}")

        print(f"\nMover entries ({len(mover_entries)}):")
        for (p, L, S, R), Sp in sorted(mover_entries.items()):
            print(f"  proc {p}: ({L},{S},{R}) -> {Sp}")

        # Find ALL non-good configs with forced procs
        all_cfgs = list(itertools.product(*(range(m) for m in ms)))
        non_good = [c for c in all_cfgs if c not in good_set]

        forced_count = 0
        no_forced = 0
        to_good = 0
        for c in non_good:
            nxt, p = forced_step_mover_only(n, c, mover_entries)
            if nxt is not None:
                forced_count += 1
                if nxt in good_set:
                    to_good += 1
            else:
                no_forced += 1

        print(f"\nNon-good: {len(non_good)}")
        print(f"With forced proc: {forced_count}")
        print(f"  Of which go to good: {to_good}")
        print(f"Without forced proc: {no_forced}")

        # Follow orbits from ALL shifted g_0 configs
        print(f"\nOrbits from shifted g_0:")
        g0 = configs[0]
        for q in range(n):
            for d in range(1, ms[q]):
                c = list(g0); c[q] = (c[q]+d) % ms[q]; c = tuple(c)
                if c in good_set:
                    print(f"  Shift proc {q} by {d}: {tuple(c)} -> GOOD")
                    continue

                orbit = [tuple(c)]; oset = {tuple(c)}; cur = tuple(c)
                status = ""
                for step in range(CL * 3):
                    nxt, p = forced_step_mover_only(n, cur, mover_entries)
                    if nxt is None:
                        status = f"stuck after {step} steps"
                        break
                    if nxt in good_set:
                        status = f"reached good g_{list(configs).index(nxt)} after {step+1} steps"
                        break
                    if nxt in oset:
                        idx = orbit.index(nxt)
                        cyc = orbit[idx:]
                        status = f"cycle len {len(cyc)} (tail {idx})"
                        break
                    orbit.append(nxt); oset.add(nxt); cur = nxt

                print(f"  Shift proc {q} by {d}: {tuple(c)} -> {status}")

        break  # Only first combo
    break  # Only first word
