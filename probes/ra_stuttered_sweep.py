#!/usr/bin/env python3
"""
RA: Comprehensive analysis of stuttered sweep cycles.
Investigates what kills them for the lower bound proof.
"""

import sys
import itertools
from collections import Counter, defaultdict

# ============================================================
# Part 0: Core utilities
# ============================================================

def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))

def enumerate_exact_fc_words(ms, n, target_fc):
    """Enumerate mover words with exact fire counts."""
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    total_len = sum(target_fc[p] for p in range(n))
    results = []
    def dfs(word, fc):
        if len(word) == total_len:
            if abs(word[-1] - word[0]) % n in (1, n-1):
                config = [0]*n
                for p in word:
                    config[p] = (config[p]+1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                remaining = total_len - len(word)
                needed = sum(target_fc[p] - fc[p] for p in range(n))
                if needed <= remaining:
                    dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for p in range(n):
        if target_fc[p] > 0:
            fc = {q: 0 for q in range(n)}
            fc[p] = 1
            dfs([p], fc)
    return results

def build_cycle(ms, n, word):
    """Build config cycle from mover word starting at all-zeros."""
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p]+1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]

def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best

def compute_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1:
            total += 1
        elif diff == n-1:
            total -= 1
    return total

def enumerate_state_sequences(m, k):
    """All sequences of length k+1 starting and ending at 0, with consecutive entries different."""
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining-1)
                seq.pop()
    dfs([0], k)
    return seqs

def check_ec_all_combos(word, ms, n):
    """Check entry conflict for all state-sequence combos. Return (all_ec, no_ec_count, total)."""
    ell = len(word)
    fc = Counter(word)
    proc_seqs = {}
    total = 1
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
        total *= len(proc_seqs[p])

    proc_steps = {p: [] for p in range(n)}
    for s in range(ell):
        proc_steps[word[s]].append(s)
    firing_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        firing_num[s] = pc[word[s]]
        pc[word[s]] += 1

    no_ec_count = 0
    no_ec_combos = []
    for combo in itertools.product(*[proc_seqs[p] for p in range(n)]):
        state = [0]*n
        mover_ctx = [set() for _ in range(n)]
        nonmover_ctx = [set() for _ in range(n)]
        for s in range(ell):
            for q in range(n):
                ctx = (state[(q-1)%n], state[q], state[(q+1)%n])
                if word[s] == q:
                    mover_ctx[q].add(ctx)
                else:
                    nonmover_ctx[q].add(ctx)
            p = word[s]
            state[p] = combo[p][firing_num[s]+1]
        if not any(mover_ctx[q] & nonmover_ctx[q] for q in range(n)):
            no_ec_count += 1
            if len(no_ec_combos) < 5:
                no_ec_combos.append(combo)
    return no_ec_count == 0, no_ec_count, total, no_ec_combos


# ============================================================
# Part 1: Characterize stuttered sweeps at n=9
# ============================================================

print("=" * 72)
print("PART 1: STUTTERED SWEEP CHARACTERIZATION")
print("=" * 72)
sys.stdout.flush()

n = 9
ms = [2,3,3,2,3,3,2,3,3]
target_fc = {p: ms[p] for p in range(n)}
words = enumerate_exact_fc_words(ms, n, target_fc)

seen = set()
unique = []
for w in words:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique.append(w)

valid = []
for w in unique:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        valid.append((w, cycle))

sweeps = []
for w, cycle in valid:
    disp = compute_displacement(w, n)
    if abs(disp) == 2*n:
        sweeps.append((w, cycle, disp))

print(f"n={n}, ms={ms}, product={2**3 * 3**6}")
print(f"Total valid cycles: {len(valid)}")
print(f"Sweep cycles (|disp|={2*n}): {len(sweeps)}")

for idx, (w, cycle, disp) in enumerate(sweeps):
    ell = len(w)
    dirs = []
    for i in range(ell):
        diff = (w[(i+1)%ell] - w[i]) % n
        dirs.append('+' if diff == 1 else '-')

    cw = dirs.count('+')
    ccw = dirs.count('-')

    # Find reversals (direction changes)
    reversals = []
    for i in range(ell):
        if dirs[i] != dirs[(i-1)%ell]:
            reversals.append((i, w[i], dirs[(i-1)%ell] + '->' + dirs[i]))

    # Fire positions per proc
    fire_pos = defaultdict(list)
    for s in range(ell):
        fire_pos[w[s]].append(s)

    # Gap analysis for binary procs
    binary_procs = [p for p in range(n) if ms[p] == 2]
    gaps = {}
    for p in binary_procs:
        positions = fire_pos[p]
        if len(positions) == 2:
            gap = positions[1] - positions[0]
            gap2 = ell - gap
            gaps[p] = (gap, gap2)

    print(f"\nSweep #{idx}: disp={disp:+d}, CL={ell}, CW={cw}, CCW={ccw}")
    print(f"  Word: {list(w)}")
    print(f"  Dirs: {''.join(dirs)}")
    print(f"  Reversals: {reversals}")
    print(f"  Fire counts: {dict(Counter(w))}")
    for p in binary_procs:
        print(f"  Binary P{p}: fires at steps {fire_pos[p]}, gaps={gaps.get(p)}")
    for p in range(n):
        if ms[p] == 3:
            print(f"  Ternary P{p}: fires at steps {fire_pos[p]}")
    sys.stdout.flush()

# ============================================================
# Part 1b: EC check on all sweeps
# ============================================================
print("\n" + "=" * 72)
print("PART 1b: ENTRY CONFLICT CHECK ON SWEEPS")
print("=" * 72)
sys.stdout.flush()

noec_sweeps = []
for idx, (w, cycle, disp) in enumerate(sweeps):
    all_ec, noec, total, noec_combos = check_ec_all_combos(w, ms, n)
    print(f"Sweep #{idx}: all_ec={all_ec}, no_ec_count={noec}/{total}")
    if not all_ec:
        noec_sweeps.append((w, cycle, disp, noec_combos))
    sys.stdout.flush()

print(f"\nNo-EC sweeps: {len(noec_sweeps)}")

# ============================================================
# Part 2: Table entry analysis (forced vs free)
# ============================================================
print("\n" + "=" * 72)
print("PART 2: TABLE ENTRY ANALYSIS")
print("=" * 72)
sys.stdout.flush()

# Take first no-EC sweep and first no-EC combo
if noec_sweeps:
    w, cycle, disp, combos = noec_sweeps[0]
    combo = combos[0]
    ell = len(w)

    print(f"\nAnalyzing sweep word: {list(w)}")
    print(f"State sequence combo: {combo}")

    # Build the actual config cycle with this combo
    fc_counter = Counter(w)
    firing_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        firing_num[s] = pc[w[s]]
        pc[w[s]] += 1

    configs = []
    state = [0]*n
    for s in range(ell):
        configs.append(tuple(state))
        p = w[s]
        state[p] = combo[p][firing_num[s]+1]
    configs.append(tuple(state))
    assert configs[-1] == configs[0], f"Cycle doesn't close: {configs[-1]} != {configs[0]}"

    # Determine forced table entries
    # For each step s: proc w[s] fires. Its context is (L, S, R) and it transitions to S'.
    forced_entries = {}  # (proc, L, S, R) -> S'
    for s in range(ell):
        p = w[s]
        L = configs[s][(p-1)%n]
        S = configs[s][p]
        R = configs[s][(p+1)%n]
        S_new = configs[s+1][p]
        key = (p, L, S, R)
        if key in forced_entries:
            assert forced_entries[key] == S_new, f"Conflict! {key}: {forced_entries[key]} vs {S_new}"
        forced_entries[key] = S_new

    # Non-mover entries forced by the good cycle: f(L,S,R) = S (identity)
    nonmover_entries = {}
    for s in range(ell):
        p = w[s]
        for q in range(n):
            if q == p:
                continue
            L = configs[s][(q-1)%n]
            S = configs[s][q]
            R = configs[s][(q+1)%n]
            key = (q, L, S, R)
            if key in nonmover_entries:
                assert nonmover_entries[key] == S
            nonmover_entries[key] = S

    # Total table entries per proc
    total_entries = {}
    forced_mover = {}
    forced_nonmover = {}
    free_entries = {}
    for p in range(n):
        all_ctxs = set()
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    all_ctxs.add((p, L, S, R))
        total_entries[p] = len(all_ctxs)

        fm = {k: v for k, v in forced_entries.items() if k[0] == p}
        fn = {k: v for k, v in nonmover_entries.items() if k[0] == p}
        forced_mover[p] = fm
        forced_nonmover[p] = fn

        free = all_ctxs - set(fm.keys()) - set(fn.keys())
        free_entries[p] = free

    print(f"\nTable entry summary per processor:")
    for p in range(n):
        print(f"  P{p} (m={ms[p]}): total={total_entries[p]}, "
              f"forced_mover={len(forced_mover[p])}, forced_nonmover={len(forced_nonmover[p])}, "
              f"free={len(free_entries[p])}")

    total_all = sum(total_entries[p] for p in range(n))
    total_forced = sum(len(forced_mover[p]) + len(forced_nonmover[p]) for p in range(n))
    total_free = sum(len(free_entries[p]) for p in range(n))
    print(f"\n  TOTAL: {total_all} entries, {total_forced} forced, {total_free} free")
    print(f"  Forced fraction: {total_forced/total_all:.1%}")
    sys.stdout.flush()

# ============================================================
# Part 3: Build system and check convergence
# ============================================================
print("\n" + "=" * 72)
print("PART 3: GAME GRAPH / CONVERGENCE ANALYSIS")
print("=" * 72)
sys.stdout.flush()

def build_system_and_check(w, combo, ms, n, free_fill='identity'):
    """Build transition tables from forced entries + free fill, check convergence."""
    ell = len(w)
    fc_counter = Counter(w)
    firing_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        firing_num[s] = pc[w[s]]
        pc[w[s]] += 1

    configs_seq = []
    state = [0]*n
    for s in range(ell):
        configs_seq.append(tuple(state))
        p = w[s]
        state[p] = combo[p][firing_num[s]+1]

    # Build transition tables
    tables = {}
    for p in range(n):
        tables[p] = {}

    # Forced mover entries
    for s in range(ell):
        p = w[s]
        L = configs_seq[s][(p-1)%n]
        S = configs_seq[s][p]
        R = configs_seq[s][(p+1)%n]
        S_new = combo[p][firing_num[s]+1]
        tables[p][(L, S, R)] = S_new

    # Forced nonmover entries (identity)
    for s in range(ell):
        for q in range(n):
            if q == w[s]:
                continue
            L = configs_seq[s][(q-1)%n]
            S = configs_seq[s][q]
            R = configs_seq[s][(q+1)%n]
            if (L, S, R) not in tables[q]:
                tables[q][(L, S, R)] = S

    # Free entries
    for p in range(n):
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if (L, S, R) not in tables[p]:
                        if free_fill == 'identity':
                            tables[p][(L, S, R)] = S
                        elif free_fill == 'increment':
                            tables[p][(L, S, R)] = (S+1) % ms[p]
                        elif free_fill == 'zero':
                            tables[p][(L, S, R)] = 0
                        elif free_fill == 'random':
                            import random
                            tables[p][(L, S, R)] = random.randint(0, ms[p]-1)

    # Build transition functions
    def make_f(p):
        t = tables[p]
        return lambda L, S, R, _t=t: _t[(L, S, R)]
    fs = [make_f(p) for p in range(n)]

    # Compute privilege + good configs
    all_cfgs = all_configs(ms)
    priv_map = {}
    for c in all_cfgs:
        priv = []
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    good_set = set(configs_seq[:ell])
    bad_set = set(all_cfgs) - good_set

    # Check good configs have exactly 1 privileged
    good_ok = all(len(priv_map[c]) == 1 for c in good_set)

    # Check closure
    closure_ok = True
    for c in good_set:
        p = priv_map[c][0]
        s = list(c)
        s[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
        if tuple(s) not in good_set:
            closure_ok = False
            break

    # Check liveness
    dead = [c for c in all_cfgs if len(priv_map[c]) == 0]

    # Check convergence: find trap in bad configs
    # Trap = set T of bad configs where for each c in T, there exists
    # a privileged proc whose firing leads to another config in T
    # (daemon can stay in T forever)

    # Build bad successor graph
    bad_succs = defaultdict(list)
    for c in bad_set:
        for i in priv_map[c]:
            s = list(c)
            s[i] = fs[i](c[(i-1)%n], c[i], c[(i+1)%n])
            ns = tuple(s)
            if ns in bad_set:
                bad_succs[c].append(ns)

    # Find trap: iteratively remove configs with no bad successor
    trap = set(c for c in bad_set if bad_succs[c])
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in trap:
            if not any(s in trap for s in bad_succs[c]):
                to_remove.add(c)
        if to_remove:
            trap -= to_remove
            changed = True

    # Find cycles in trap
    cycles_in_trap = []
    if trap:
        visited = set()
        for start in trap:
            if start in visited:
                continue
            path = [start]
            path_set = {start}
            current = start
            found_cycle = False
            while True:
                nexts = [s for s in bad_succs[current] if s in trap]
                if not nexts:
                    break
                nxt = nexts[0]
                if nxt in path_set:
                    idx = path.index(nxt)
                    cyc = path[idx:]
                    cycles_in_trap.append(cyc)
                    found_cycle = True
                    break
                path.append(nxt)
                path_set.add(nxt)
                current = nxt
            visited.update(path_set)

    return {
        'good_ok': good_ok,
        'closure_ok': closure_ok,
        'dead_count': len(dead),
        'trap_size': len(trap),
        'bad_count': len(bad_set),
        'trap_cycles': cycles_in_trap,
        'priv_map': priv_map,
        'tables': tables,
        'good_set': good_set,
        'bad_set': bad_set,
        'bad_succs': bad_succs,
        'trap': trap,
        'fs': fs,
    }

if noec_sweeps:
    w, cycle, disp, combos = noec_sweeps[0]
    combo = combos[0]

    for fill_name in ['identity', 'increment', 'zero']:
        print(f"\n--- Free fill: {fill_name} ---")
        result = build_system_and_check(w, combo, ms, n, free_fill=fill_name)
        print(f"  Good ME ok: {result['good_ok']}")
        print(f"  Closure ok: {result['closure_ok']}")
        print(f"  Dead configs: {result['dead_count']}")
        print(f"  Bad configs: {result['bad_count']}")
        print(f"  Trap size: {result['trap_size']}")
        if result['trap_cycles']:
            print(f"  Trap cycles found: {len(result['trap_cycles'])}")
            for ci, cyc in enumerate(result['trap_cycles'][:3]):
                print(f"    Cycle {ci}: length {len(cyc)}")
                if len(cyc) <= 10:
                    for cfg in cyc:
                        priv = result['priv_map'][cfg]
                        print(f"      {cfg} priv={priv}")
        else:
            print(f"  NO trap (convergence OK!)")
        sys.stdout.flush()

# ============================================================
# Part 3b: Try ALL 5 no-EC combos with identity fill
# ============================================================
print("\n" + "=" * 72)
print("PART 3b: ALL NO-EC COMBOS (identity fill)")
print("=" * 72)
sys.stdout.flush()

if noec_sweeps:
    w, cycle, disp, combos = noec_sweeps[0]
    for ci, combo in enumerate(combos):
        result = build_system_and_check(w, combo, ms, n, free_fill='identity')
        trap_ok = result['trap_size'] > 0
        print(f"Combo {ci}: good_ok={result['good_ok']}, closure={result['closure_ok']}, "
              f"dead={result['dead_count']}, trap={result['trap_size']}, converges={result['trap_size']==0}")
        sys.stdout.flush()

# ============================================================
# Part 4: ShadowTrap extraction
# ============================================================
print("\n" + "=" * 72)
print("PART 4: SHADOW TRAP EXTRACTION")
print("=" * 72)
sys.stdout.flush()

if noec_sweeps:
    w, cycle, disp, combos = noec_sweeps[0]
    combo = combos[0]

    # Use identity fill (most natural)
    result = build_system_and_check(w, combo, ms, n, free_fill='identity')

    if result['trap']:
        # Find ALL short cycles in the trap
        trap = result['trap']
        bad_succs = result['bad_succs']
        priv_map = result['priv_map']

        # BFS for shortest cycles
        all_cycles = []
        visited_cycles = set()

        for start in list(trap)[:100]:  # Sample
            # DFS to find cycles through start
            stack = [(start, [start])]
            local_visited = {start}
            while stack and len(all_cycles) < 50:
                current, path = stack.pop()
                for nxt in bad_succs[current]:
                    if nxt not in trap:
                        continue
                    if nxt == start and len(path) >= 2:
                        cyc = tuple(path)
                        canon = min(cyc[i:] + cyc[:i] for i in range(len(cyc)))
                        if canon not in visited_cycles:
                            visited_cycles.add(canon)
                            all_cycles.append(path[:])
                        continue
                    if nxt not in local_visited and len(path) < 20:
                        local_visited.add(nxt)
                        stack.append((nxt, path + [nxt]))

        if all_cycles:
            all_cycles.sort(key=len)
            print(f"Found {len(all_cycles)} distinct trap cycles")
            print(f"Shortest cycle length: {len(all_cycles[0])}")

            for ci, cyc in enumerate(all_cycles[:5]):
                print(f"\n  ShadowTrap #{ci}: length {len(cyc)}")
                for step, cfg in enumerate(cyc):
                    priv = priv_map[cfg]
                    # Which proc fires to get to next?
                    nxt = cyc[(step+1) % len(cyc)]
                    firing_proc = None
                    for p in priv:
                        s = list(cfg)
                        s[p] = result['fs'][p](cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
                        if tuple(s) == nxt:
                            firing_proc = p
                            break
                    print(f"    Step {step}: {cfg} -> fire P{firing_proc} (priv={priv})")
        else:
            print("No short cycles found in trap (trap may be DAG-like?)")
    else:
        print("No trap exists for this fill!")
    sys.stdout.flush()

# ============================================================
# Part 5: Waterfall decomposition
# ============================================================
print("\n" + "=" * 72)
print("PART 5: WATERFALL DECOMPOSITION ATTEMPT")
print("=" * 72)
sys.stdout.flush()

if noec_sweeps:
    w, cycle, disp, combos = noec_sweeps[0]
    ell = len(w)

    # Identify the "core" waterfall-like subsequence
    # A waterfall cycle would be CL=2n=18, all same direction
    # The stuttered sweep has CL=24 with 3 stutters

    # Find stutter positions (reversals in the word)
    dirs = []
    for i in range(ell):
        diff = (w[(i+1)%ell] - w[i]) % n
        dirs.append('+' if diff == 1 else '-')

    stutter_steps = []
    main_dir = '+' if disp > 0 else '-'
    for i in range(ell):
        if dirs[i] != main_dir:
            stutter_steps.append(i)

    print(f"Main direction: {'CW' if main_dir == '+' else 'CCW'}")
    print(f"Stutter steps: {stutter_steps}")
    print(f"Stutter procs: {[w[s] for s in stutter_steps]}")

    # Core = remove the stutter steps and their reversal partners
    # Each stutter is a pair: go back one step, then go forward again
    # So we need to identify the pairs

    # A CW stutter at binary proc p looks like: ...p-1, p, p-1, p, p+1...
    # The "extra" is the second p-1 and second p (2 extra steps per stutter)
    # 24 = 18 + 3*2

    print(f"\nWord:  {list(w)}")
    print(f"Dirs:  {''.join(dirs)}")

    # Show which steps are "core" (main direction) and which are "stutter"
    for i in range(ell):
        marker = "CORE" if dirs[i] == main_dir else "STUT"
        print(f"  Step {i:2d}: P{w[i]} dir={dirs[i]} [{marker}]")

    sys.stdout.flush()

# ============================================================
# Part 6: Convergence-based argument
# ============================================================
print("\n" + "=" * 72)
print("PART 6: UNIVERSAL TRAP ANALYSIS")
print("=" * 72)
sys.stdout.flush()

# Key question: does a trap ALWAYS exist for stuttered sweeps?
# Try ALL no-EC combos with ALL fill strategies

if noec_sweeps:
    w, cycle, disp, combos = noec_sweeps[0]

    import random
    random.seed(42)

    results_summary = []
    for ci, combo in enumerate(combos):
        for fill in ['identity', 'increment', 'zero']:
            result = build_system_and_check(w, combo, ms, n, free_fill=fill)
            results_summary.append({
                'combo': ci, 'fill': fill,
                'trap_size': result['trap_size'],
                'dead': result['dead_count'],
                'good_ok': result['good_ok'],
                'closure': result['closure_ok'],
            })
        # Also try a few random fills
        for ri in range(3):
            random.seed(42 + ci*10 + ri)
            result = build_system_and_check(w, combo, ms, n, free_fill='random')
            results_summary.append({
                'combo': ci, 'fill': f'random_{ri}',
                'trap_size': result['trap_size'],
                'dead': result['dead_count'],
                'good_ok': result['good_ok'],
                'closure': result['closure_ok'],
            })

    print(f"Tested {len(results_summary)} (combo, fill) pairs:")
    all_have_trap = True
    all_valid_structure = True
    for r in results_summary:
        has_trap = r['trap_size'] > 0
        valid = r['good_ok'] and r['closure']
        if not has_trap:
            all_have_trap = False
        if not valid:
            all_valid_structure = False
        status = "TRAP" if has_trap else "CONVERGES"
        if r['dead'] > 0:
            status = "DEAD (not live)"
        if not r['good_ok']:
            status = "BAD ME"
        print(f"  combo={r['combo']}, fill={r['fill']:12s}: {status}, "
              f"trap={r['trap_size']}, dead={r['dead']}")

    print(f"\n  ALL have trap: {all_have_trap}")
    print(f"  ALL have valid good structure: {all_valid_structure}")
    sys.stdout.flush()

# ============================================================
# Part 7: Does the trap have a STRUCTURAL explanation?
# ============================================================
print("\n" + "=" * 72)
print("PART 7: TRAP STRUCTURE ANALYSIS")
print("=" * 72)
sys.stdout.flush()

if noec_sweeps:
    w, cycle_cfgs, disp, combos = noec_sweeps[0]
    combo = combos[0]
    result = build_system_and_check(w, combo, ms, n, free_fill='identity')

    if result['trap']:
        trap = result['trap']
        good = result['good_set']
        priv_map = result['priv_map']

        print(f"Trap size: {len(trap)}")
        print(f"Good cycle size: {len(good)}")

        # Analyze privilege counts in trap
        priv_counts = Counter(len(priv_map[c]) for c in trap)
        print(f"\nPrivilege distribution in trap: {dict(priv_counts)}")

        # Are there configs in the trap with exactly 1 privileged proc?
        # These would be "shadow good" configs
        single_priv_trap = [c for c in trap if len(priv_map[c]) == 1]
        print(f"Single-privilege configs in trap: {len(single_priv_trap)}")

        # Check: do the single-priv trap configs form their own cycle?
        if single_priv_trap:
            sp_set = set(single_priv_trap)
            sp_succs = {}
            for c in single_priv_trap:
                p = priv_map[c][0]
                s = list(c)
                s[p] = result['fs'][p](c[(p-1)%n], c[p], c[(p+1)%n])
                ns = tuple(s)
                sp_succs[c] = ns

            # How many stay in single-priv trap?
            stays = sum(1 for c in single_priv_trap if sp_succs[c] in sp_set)
            print(f"  Of these, {stays} have successor also in single-priv trap")

            # Find cycles among single-priv trap configs
            visited = set()
            sp_cycles = []
            for start in single_priv_trap:
                if start in visited:
                    continue
                path = [start]
                path_set = {start}
                current = start
                while True:
                    nxt = sp_succs[current]
                    if nxt in path_set:
                        idx = path.index(nxt)
                        sp_cycles.append(path[idx:])
                        break
                    if nxt not in sp_set:
                        break
                    path.append(nxt)
                    path_set.add(nxt)
                    current = nxt
                visited.update(path_set)

            print(f"  Deterministic cycles among single-priv trap: {len(sp_cycles)}")
            for ci, cyc in enumerate(sp_cycles[:3]):
                print(f"\n  Shadow cycle #{ci}: length {len(cyc)}")
                movers = []
                for step, cfg in enumerate(cyc):
                    p = priv_map[cfg][0]
                    movers.append(p)
                print(f"    Mover word: {movers}")
                fc = Counter(movers)
                print(f"    Fire counts: {dict(fc)}")
                d = compute_displacement(movers, n)
                print(f"    Displacement: {d}")
                if len(cyc) <= 30:
                    for step, cfg in enumerate(cyc[:20]):
                        p = priv_map[cfg][0]
                        print(f"      Step {step:2d}: {cfg} fire P{p}")

        sys.stdout.flush()

# ============================================================
# Part 7b: Check ALL no-EC sweeps (not just first)
# ============================================================
print("\n" + "=" * 72)
print("PART 7b: ALL NO-EC SWEEPS, ALL COMBOS")
print("=" * 72)
sys.stdout.flush()

if noec_sweeps:
    for sw_idx, (w, cycle, disp, combos) in enumerate(noec_sweeps):
        print(f"\nSweep #{sw_idx}: word={list(w)}, disp={disp:+d}, #no-EC={len(combos)}")
        for ci, combo in enumerate(combos):
            result = build_system_and_check(w, combo, ms, n, free_fill='identity')
            # Also check if there's ANY fill that converges
            result_inc = build_system_and_check(w, combo, ms, n, free_fill='increment')
            result_zero = build_system_and_check(w, combo, ms, n, free_fill='zero')

            traps = [result['trap_size'], result_inc['trap_size'], result_zero['trap_size']]
            all_trap = all(t > 0 for t in traps)
            print(f"  Combo {ci}: traps=[id:{traps[0]}, inc:{traps[1]}, zero:{traps[2]}] all_trap={all_trap}")
        sys.stdout.flush()

# ============================================================
# Part 8: Small n analysis (easier to see structure)
# ============================================================
print("\n" + "=" * 72)
print("PART 8: SMALL n ANALYSIS")
print("=" * 72)
sys.stdout.flush()

for test_n in [5, 6, 7]:
    # Non-consecutive binary with ≥3 binary
    # For small n, try all-odd-gap patterns
    if test_n == 5:
        test_ms_list = [[2,3,2,3,2]]  # 3 binary non-consecutive
    elif test_n == 6:
        test_ms_list = [[2,3,2,3,2,3]]
    elif test_n == 7:
        test_ms_list = [[2,3,2,3,2,3,3], [2,3,3,2,3,3,2]]

    for test_ms in test_ms_list:
        test_prod = 1
        for m in test_ms:
            test_prod *= m
        threshold = 4 * (3 ** (test_n - 2))
        if test_prod >= threshold:
            continue

        target = {p: test_ms[p] for p in range(test_n)}
        words = enumerate_exact_fc_words(test_ms, test_n, target)

        seen = set()
        unique = []
        for w in words:
            canon = canonicalize_word(w)
            if canon not in seen:
                seen.add(canon)
                unique.append(w)

        valid_words = []
        for w in unique:
            cyc = build_cycle(test_ms, test_n, w)
            if cyc is not None:
                valid_words.append((w, cyc))

        # Find sweeps
        sw = []
        for w, cyc in valid_words:
            d = compute_displacement(w, test_n)
            if abs(d) == 2*test_n:
                sw.append((w, cyc, d))

        # Check EC
        noec = []
        for w, cyc, d in sw:
            all_ec, cnt, tot, cbs = check_ec_all_combos(w, test_ms, test_n)
            if not all_ec:
                noec.append((w, cyc, d, cbs))

        print(f"\nn={test_n}, ms={test_ms}, product={test_prod} (threshold={threshold})")
        print(f"  Valid cycles: {len(valid_words)}, sweeps: {len(sw)}, no-EC sweeps: {len(noec)}")

        if noec:
            for sw_idx, (w, cyc, d, cbs) in enumerate(noec[:2]):
                print(f"\n  No-EC sweep: {list(w)}, disp={d:+d}")
                combo = cbs[0]
                result = build_system_and_check(w, combo, test_ms, test_n, free_fill='identity')
                print(f"    trap={result['trap_size']}, dead={result['dead_count']}, "
                      f"good_ok={result['good_ok']}, closure={result['closure_ok']}")

                if result['trap_cycles']:
                    cyc0 = result['trap_cycles'][0]
                    print(f"    Trap cycle length: {len(cyc0)}")
                    movers = []
                    for step, cfg in enumerate(cyc0):
                        priv = result['priv_map'][cfg]
                        nxt = cyc0[(step+1)%len(cyc0)]
                        for p in priv:
                            s = list(cfg)
                            s[p] = result['fs'][p](cfg[(p-1)%test_n], cfg[p], cfg[(p+1)%test_n])
                            if tuple(s) == nxt:
                                movers.append(p)
                                break
                    print(f"    Trap mover word: {movers}")
        sys.stdout.flush()

print("\n" + "=" * 72)
print("ANALYSIS COMPLETE")
print("=" * 72)
