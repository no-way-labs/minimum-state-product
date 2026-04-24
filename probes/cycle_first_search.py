#!/usr/bin/env python3
"""cycle_first_search.py — n=9 witness via tail-family orientation.

State counts: (2,2,3,4,3,3,2,3,3), product 7776.

Tail extension of n=8 witness (2,2,3,4,3,3,2,3):
  P0-P6: same neighbor configs, same tables as n=8
  P7: config (2,3,3) — was (2,3,2), needs 6 new entries for R=2
  P8: config (3,3,2) — new proc, same config as n=8 P5

Phase 0: Quick table search — 3^6 = 729 P7 extensions × P8 candidates
Phase 1: Cycle-first DFS with n=8 template and forced-move optimization
"""

import sys
import time
from itertools import product as cartesian, permutations
from collections import Counter

SC9 = (2, 2, 3, 4, 3, 3, 2, 3, 3)
N9 = 9


# ── verifier ─────────────────────────────────────────────────────────

def verify(name, state_counts, rules, verbose=True):
    n = len(state_counts)
    P = 1
    for m in state_counts:
        P *= m
    configs = list(cartesian(*(range(m) for m in state_counts)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]; S = cfg[i]; R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]; S = cfg[proc]; R = cfg[(proc + 1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg); lst[proc] = new_S
        return tuple(lst)

    for cfg in configs:
        if not privileged(cfg):
            if verbose:
                print(f"  FAIL liveness: {cfg}")
            return False

    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move(cfg, priv[0]), priv[0])

    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []; movers = []; visited = set(); cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur); visited_global.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover); cur = nxt
        if cur == start and len(path) > 0:
            good_cycle = path; good_movers = movers; break

    if good_cycle is None:
        if verbose:
            print(f"  FAIL: no good cycle (single_priv={len(single_priv)})")
        return False

    good_set = set(good_cycle)
    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False; to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                if move(cfg, p) in bad_set:
                    all_exit = False; break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove; changed = True

    if bad_set:
        if verbose:
            print(f"  FAIL convergence: {len(bad_set)} bad in cycles")
        return False

    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        if verbose:
            print(f"  FAIL fairness: {set(range(n)) - movers_seen} never move")
        return False

    if verbose:
        print(f"  PASS  product={P}  cycle={len(good_cycle)}  "
              f"bad={len(configs) - len(good_cycle)}")
    return True


# ── witnesses ────────────────────────────────────────────────────────

def witness_n6():
    return (2, 2, 2, 4, 3, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):1,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):1,(1,1,3):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):2,(0,1,1):3,(0,1,2):1,(0,2,0):2,(0,2,1):2,(0,2,2):1,
         (0,3,0):2,(0,3,1):0,(0,3,2):3,
         (1,0,0):1,(1,0,1):2,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0,(1,2,0):3,(1,2,1):2,(1,2,2):2,
         (1,3,0):3,(1,3,1):0,(1,3,2):0},
        {(0,0,0):0,(0,0,1):2,(0,0,2):0,(0,1,0):1,(0,1,1):2,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):2,
         (1,0,0):0,(1,0,1):2,(1,0,2):0,(1,1,0):0,(1,1,1):0,(1,1,2):0,(1,2,0):0,(1,2,1):2,(1,2,2):2,
         (2,0,0):0,(2,0,1):1,(2,0,2):1,(2,1,0):2,(2,1,1):1,(2,1,2):2,(2,2,0):2,(2,2,1):2,(2,2,2):2,
         (3,0,0):1,(3,0,1):0,(3,0,2):0,(3,1,0):1,(3,1,1):0,(3,1,2):1,(3,2,0):0,(3,2,1):0,(3,2,2):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):1,(1,2,0):2,(1,2,1):0,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1,(2,2,0):2,(2,2,1):0},
    )

def witness_n7():
    return (3, 2, 2, 2, 3, 4, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):2,(0,1,1):0,(0,2,0):2,(0,2,1):2,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):2,(1,2,1):2,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):1,(2,2,0):2,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):0,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):2,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):0,(1,1,3):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):2},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):3,(0,1,1):1,(0,1,2):1,
         (0,2,0):2,(0,2,1):0,(0,2,2):1,(0,3,0):3,(0,3,1):0,(0,3,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):1,
         (2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):1,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):2,(0,1,2):1,(0,2,0):0,(0,2,1):2,(0,2,2):0,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0,(1,2,0):1,(1,2,1):0,(1,2,2):0,
         (2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):0,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):0,(2,2,2):2,
         (3,0,0):2,(3,0,1):0,(3,0,2):1,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):2,(3,2,1):0,(3,2,2):0},
    )

def witness_n8():
    return (2, 2, 3, 4, 3, 3, 2, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,
         (0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,
         (2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,
         (2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,
         (2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,
         (3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,
         (2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,
         (2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
    )


# ── n=8 cycle extraction ────────────────────────────────────────────

def extract_n8_cycle():
    sc8, r8 = witness_n8()
    n8 = len(sc8)
    configs = list(cartesian(*(range(m) for m in sc8)))
    single_priv = {}
    for cfg in configs:
        priv = []
        for i in range(n8):
            L = cfg[(i-1)%n8]; S = cfg[i]; R = cfg[(i+1)%n8]
            if r8[i][(L,S,R)] != S:
                priv.append(i)
        if len(priv) == 1:
            proc = priv[0]
            L = cfg[(proc-1)%n8]; S = cfg[proc]; R = cfg[(proc+1)%n8]
            new_S = r8[proc][(L,S,R)]
            lst = list(cfg); lst[proc] = new_S
            single_priv[cfg] = (tuple(lst), proc)

    for start in single_priv:
        path = []; visited = set(); cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur); path.append(cur)
            cur = single_priv[cur][0]
        if cur == start and len(path) > 0:
            movers = [single_priv[c][1] for c in path]
            return path, movers
    return None, None


# ── relabeling helpers ───────────────────────────────────────────────

def relabel_332_table(table, sigma, tau):
    """Relabel a (3,3,2) table: sigma permutes {0,1,2} (L,S,out), tau permutes {0,1} (R)."""
    inv_s = [0]*3
    for i, p in enumerate(sigma):
        inv_s[p] = i
    inv_t = [0]*2
    for i, p in enumerate(tau):
        inv_t[p] = i
    new_table = {}
    for (L, S, R), out in table.items():
        new_table[(sigma[L], sigma[S], tau[R])] = sigma[out]
    return new_table


# ── Phase 0: Quick table search ─────────────────────────────────────

def phase0_quick_search():
    """P7 extended + P8 reused from existing witnesses."""
    sc8, r8 = witness_n8()
    sc6, r6 = witness_n6()
    sc7, r7 = witness_n7()

    # P7 base table from n=8 (config (2,3,2), 12 entries for R=0,1)
    p7_base = dict(r8[7])

    # New P7 entries: (L, S, R=2) for L in {0,1}, S in {0,1,2}
    p7_new_keys = [(L, S, 2) for L in range(2) for S in range(3)]

    # P8 base candidates (config (3,3,2))
    p8_bases = [
        ("n8-P5", dict(r8[5])),
        ("n6-P5", dict(r6[5])),
        ("n7-P0", dict(r7[0])),
    ]

    # Generate all relabelings
    sigma_perms = list(permutations(range(3)))
    tau_perms = [(0, 1), (1, 0)]
    p8_candidates = []
    seen_tables = set()

    for name, base in p8_bases:
        for sigma in sigma_perms:
            for tau in tau_perms:
                rt = relabel_332_table(base, sigma, tau)
                key = tuple(sorted(rt.items()))
                if key not in seen_tables:
                    seen_tables.add(key)
                    p8_candidates.append((f"{name}/σ={sigma}/τ={tau}", rt))

    print(f"P8 candidates: {len(p8_candidates)} distinct (from {len(p8_bases)} bases × 12 relabelings)")
    print(f"P7 extensions: 729 (3^6)")
    print(f"Total trials: {len(p8_candidates) * 729}")

    # Precompute: which configs need P7/P8 to be privileged?
    # (configs where P0-P6 are all unprivileged)
    print("Precomputing fixed privilege status for P0-P6...")
    all_configs = list(cartesian(*(range(m) for m in SC9)))

    rules_fixed = list(r8[:7])  # P0-P6 from n=8

    needs_p7p8 = []  # configs where P0-P6 all unprivileged
    p06_priv = {}  # config -> list of privileged among P0-P6

    for cfg in all_configs:
        fp = []
        for i in range(7):  # P0-P6
            L = cfg[(i-1)%N9]; S = cfg[i]; R = cfg[(i+1)%N9]
            if rules_fixed[i][(L,S,R)] != S:
                fp.append(i)
        p06_priv[cfg] = fp
        if len(fp) == 0:
            needs_p7p8.append(cfg)

    print(f"  Configs needing P7/P8 for liveness: {len(needs_p7p8)}")

    # Extract P7/P8 triples for needs configs
    needs_triples = []
    for cfg in needs_p7p8:
        L7 = cfg[6]; S7 = cfg[7]; R7 = cfg[8]
        L8 = cfg[7]; S8 = cfg[8]; R8 = cfg[0]
        needs_triples.append((L7, S7, R7, L8, S8, R8))

    t0 = time.time()
    total = 0
    liveness_pass = 0

    for p8_name, p8_table in p8_candidates:
        for vals in cartesian(range(3), repeat=6):
            total += 1

            # Build P7 table
            p7 = dict(p7_base)
            for key, val in zip(p7_new_keys, vals):
                p7[key] = val

            # Quick liveness check on needs_p7p8 configs
            ok = True
            for (L7, S7, R7, L8, S8, R8) in needs_triples:
                p7_priv = (p7[(L7, S7, R7)] != S7)
                p8_priv = (p8_table[(L8, S8, R8)] != S8)
                if not p7_priv and not p8_priv:
                    ok = False
                    break

            if not ok:
                continue

            liveness_pass += 1

            # Full verify
            rules9 = list(r8[:7]) + [p7, p8_table]
            result = verify(f"q-{total}", SC9, rules9, verbose=False)

            if result:
                elapsed = time.time() - t0
                print(f"\n*** FOUND! Trial {total}, P8={p8_name} ({elapsed:.1f}s) ***")
                print(f"P7 R=2 entries: {dict(zip(p7_new_keys, vals))}")
                verify("n=9 WITNESS", SC9, rules9, verbose=True)
                print(f"\nState counts: {SC9}")
                print(f"Product: 7776")
                print(f"\nP7 table (2,3,3):")
                for L in range(2):
                    for S in range(3):
                        row = [p7[(L,S,R)] for R in range(3)]
                        print(f"  f({L},{S},*) = {row}")
                print(f"\nP8 table (3,3,2):")
                for L in range(3):
                    for S in range(3):
                        row = [p8_table[(L,S,R)] for R in range(2)]
                        print(f"  f({L},{S},*) = {row}")
                return rules9

            if total % 5000 == 0:
                elapsed = time.time() - t0
                print(f"  ...{total} tried, {liveness_pass} liveness pass, {elapsed:.1f}s")

    elapsed = time.time() - t0
    print(f"\nPhase 0 done: {total} tried, {liveness_pass} liveness pass, 0 full pass ({elapsed:.1f}s)")
    return None


# ── Phase 1: Cycle-first DFS ────────────────────────────────────────

def phase1_cycle_dfs():
    """Build a good cycle step-by-step, derive tables from it."""
    sc8, r8 = witness_n8()
    n8_cycle, n8_movers = extract_n8_cycle()

    print(f"\nn=8 template: cycle length {len(n8_cycle)}, mover sequence:")
    print(f"  {n8_movers}")

    # Fixed tables for P0-P6
    rules_fixed = list(r8[:7]) + [None, None]  # P7, P8 unknown

    # The DFS builds a cycle starting from a given config.
    # State: entries dict (proc, L, S, R) -> output
    # At each step: determine candidates, try them with backtracking.

    MAX_LEN = 100
    TIMEOUT = 300  # 5 minutes

    def get_input(cfg, p):
        return (cfg[(p-1)%N9], cfg[p], cfg[(p+1)%N9])

    def run_dfs(start_cfg, template_movers=None):
        """DFS from start_cfg. Returns (path, movers, entries) or None."""
        entries = {}
        path = [start_cfg]
        movers = []
        mover_count = Counter()
        visited = {start_cfg}
        t0 = time.time()
        best_depth = [0]
        calls = [0]

        def solve(depth):
            calls[0] += 1
            if calls[0] % 100000 == 0:
                if time.time() - t0 > TIMEOUT:
                    return False

            if depth > MAX_LEN:
                return False

            if depth > best_depth[0]:
                best_depth[0] = depth
                if depth % 10 == 0:
                    elapsed = time.time() - t0
                    print(f"    depth {depth}, entries={len(entries)}, calls={calls[0]}, {elapsed:.1f}s")

            cfg = path[-1]

            # Check cycle closure
            if depth >= 10 and cfg == start_cfg:
                if all(mover_count[p] > 0 for p in range(N9)):
                    return True
                return False

            # Compute privilege status for each processor
            known_priv = []
            known_unpriv = []
            unknown = []

            for p in range(N9):
                L, S, R = get_input(cfg, p)

                if p <= 6:
                    # Fixed table
                    out = rules_fixed[p][(L, S, R)]
                    if out != S:
                        known_priv.append((p, out))
                    else:
                        known_unpriv.append(p)
                else:
                    # Unknown table (P7 or P8)
                    key = (p, L, S, R)
                    if key in entries:
                        if entries[key] != S:
                            known_priv.append((p, entries[key]))
                        else:
                            known_unpriv.append(p)
                    else:
                        unknown.append(p)

            # 2+ known privileged: can't be single-priv
            if len(known_priv) >= 2:
                return False

            candidates = []

            if len(known_priv) == 1:
                p, new_S = known_priv[0]
                # All unknown must be unprivileged
                new_entries = []
                conflict = False
                for up in unknown:
                    L, S, R = get_input(cfg, up)
                    key = (up, L, S, R)
                    if key in entries:
                        if entries[key] != S:
                            conflict = True; break
                    else:
                        new_entries.append((key, S))
                if not conflict:
                    candidates.append((p, new_S, new_entries))

            elif len(known_priv) == 0:
                if len(unknown) == 0:
                    return False  # dead config

                # Each unknown processor could be the mover
                for p in unknown:
                    L, S, R = get_input(cfg, p)
                    for new_S in range(SC9[p]):
                        if new_S == S:
                            continue
                        new_entries = []
                        conflict = False

                        # Mover entry
                        mkey = (p, L, S, R)
                        if mkey in entries:
                            if entries[mkey] != new_S:
                                continue
                        else:
                            new_entries.append((mkey, new_S))

                        # Non-mover entries for other unknowns
                        for op in unknown:
                            if op == p:
                                continue
                            oL, oS, oR = get_input(cfg, op)
                            okey = (op, oL, oS, oR)
                            if okey in entries:
                                if entries[okey] != oS:
                                    conflict = True; break
                            else:
                                new_entries.append((okey, oS))

                        if not conflict:
                            candidates.append((p, new_S, new_entries))

            # Heuristic ordering: use template if available
            if template_movers and depth < len(template_movers):
                tmover = template_movers[depth]
                # Put template mover first
                candidates.sort(key=lambda c: (0 if c[0] == tmover else 1, c[0], c[1]))

            for p, new_S, new_ents in candidates:
                # Apply entries
                for key, val in new_ents:
                    entries[key] = val

                # Compute successor
                lst = list(cfg); lst[p] = new_S; succ = tuple(lst)

                # Skip if already visited (unless it's the start = cycle closure)
                if succ in visited and succ != start_cfg:
                    for key, val in new_ents:
                        del entries[key]
                    continue

                path.append(succ)
                movers.append(p)
                mover_count[p] += 1
                was_visited = succ in visited
                visited.add(succ)

                if solve(depth + 1):
                    return True

                # Undo
                path.pop()
                movers.pop()
                mover_count[p] -= 1
                if not was_visited:
                    visited.discard(succ)
                for key, val in new_ents:
                    del entries[key]

            return False

        if solve(0):
            return list(path), list(movers), dict(entries)
        else:
            print(f"    DFS exhausted: depth={best_depth[0]}, calls={calls[0]}")
            return None

    # Try starting from (0,...,0) with n=8 template
    start = (0,) * N9
    print(f"\nDFS from {start} with n=8 template...")
    result = run_dfs(start, template_movers=n8_movers)
    if result:
        return result

    # Try without template (pure forced-move)
    print(f"\nDFS from {start} without template...")
    result = run_dfs(start, template_movers=None)
    if result:
        return result

    # Try starting from n=8 cycle configs extended with P8=0
    for i in range(0, len(n8_cycle), 10):
        cfg8 = n8_cycle[i]
        start9 = cfg8 + (0,)
        print(f"\nDFS from n=8 cycle step {i}: {start9}...")
        result = run_dfs(start9, template_movers=n8_movers[i:] + n8_movers[:i])
        if result:
            return result

    return None


def fill_and_verify(path, movers, entries):
    """Fill free entries to satisfy liveness, then verify all 5 properties."""
    sc8, r8 = witness_n8()
    rules_fixed = list(r8[:7])

    # Separate determined entries
    p7_det = {}
    p8_det = {}
    for (proc, L, S, R), out in entries.items():
        if proc == 7:
            p7_det[(L, S, R)] = out
        elif proc == 8:
            p8_det[(L, S, R)] = out

    # Enumerate free entry keys
    p7_free_keys = []
    for L in range(SC9[6]):
        for S in range(SC9[7]):
            for R in range(SC9[8]):
                if (L, S, R) not in p7_det:
                    p7_free_keys.append((7, L, S, R))

    p8_free_keys = []
    for L in range(SC9[7]):
        for S in range(SC9[8]):
            for R in range(SC9[0]):
                if (L, S, R) not in p8_det:
                    p8_free_keys.append((8, L, S, R))

    all_free = p7_free_keys + p8_free_keys
    n_free = len(all_free)
    print(f"\nFilling {n_free} free entries ({len(p7_free_keys)} P7, {len(p8_free_keys)} P8)")
    print(f"  Determined: {len(p7_det)} P7, {len(p8_det)} P8")

    # Precompute: which configs need P7/P8 for liveness?
    all_configs = list(cartesian(*(range(m) for m in SC9)))
    needs = []
    for cfg in all_configs:
        fp = []
        for i in range(7):
            Li = cfg[(i-1)%N9]; Si = cfg[i]; Ri = cfg[(i+1)%N9]
            if rules_fixed[i][(Li, Si, Ri)] != Si:
                fp.append(i)
        if len(fp) == 0:
            L7 = cfg[6]; S7 = cfg[7]; R7 = cfg[8]
            L8 = cfg[7]; S8 = cfg[8]; R8 = cfg[0]
            needs.append((L7, S7, R7, L8, S8, R8))

    print(f"  Configs needing P7/P8 for liveness: {len(needs)}")

    # Check for hard failures (both determined to identity)
    hard_fail = 0
    for (L7, S7, R7, L8, S8, R8) in needs:
        t7 = (L7, S7, R7)
        t8 = (L8, S8, R8)
        p7_determined = t7 in p7_det
        p8_determined = t8 in p8_det
        if p7_determined and p8_determined:
            if p7_det[t7] == S7 and p8_det[t8] == S8:
                hard_fail += 1

    if hard_fail > 0:
        print(f"  HARD FAILURE: {hard_fail} configs have both P7/P8 determined to identity")
        return None

    # Identify liveness-relevant free entries
    # For each need config: at least one of P7/P8 must be non-identity
    # If the entry is determined and already non-identity: covered
    # If both entries are determined identity: hard fail (checked above)
    # Otherwise: at least one free entry must be non-identity

    # Collect constraints: each needs config gives a disjunctive constraint
    # on free entries
    uncovered = []  # needs that require free entries to fix
    for (L7, S7, R7, L8, S8, R8) in needs:
        t7 = (L7, S7, R7)
        t8 = (L8, S8, R8)
        p7_covers = (t7 in p7_det and p7_det[t7] != S7)
        p8_covers = (t8 in p8_det and p8_det[t8] != S8)
        if p7_covers or p8_covers:
            continue  # already covered by determined entries
        # This config needs a free entry to cover it
        options = []
        if t7 not in p7_det:
            options.append((7, L7, S7, R7))
        if t8 not in p8_det:
            options.append((8, L8, S8, R8))
        uncovered.append((options, S7, S8))

    # Find distinct free entries involved in liveness
    liveness_entries = set()
    for (options, _, _) in uncovered:
        for ent in options:
            liveness_entries.add(ent)
    liveness_entries = sorted(liveness_entries)

    # Non-liveness free entries stay identity
    non_liveness_free = [e for e in all_free if e not in set(liveness_entries)]

    print(f"  Uncovered liveness needs: {len(uncovered)}")
    print(f"  Liveness-relevant free entries: {len(liveness_entries)}")
    print(f"  Non-relevant free entries (=identity): {len(non_liveness_free)}")
    print(f"  Search space: 3^{len(liveness_entries)} = {3**len(liveness_entries)}")

    # Enumerate over liveness-relevant entries, keep rest as identity
    t0 = time.time()
    tested = 0
    liveness_pass = 0
    n_rel = len(liveness_entries)
    total_search = 3 ** n_rel

    for vals in cartesian(range(3), repeat=n_rel):
        tested += 1

        # Build tables
        p7 = dict(p7_det)
        p8 = dict(p8_det)

        # Set non-liveness free entries to identity
        for (proc, L, S, R) in non_liveness_free:
            if proc == 7:
                p7[(L, S, R)] = S
            else:
                p8[(L, S, R)] = S

        # Set liveness-relevant entries
        for i, (proc, L, S, R) in enumerate(liveness_entries):
            if proc == 7:
                p7[(L, S, R)] = vals[i]
            else:
                p8[(L, S, R)] = vals[i]

        # Quick liveness check
        ok = True
        for (L7, S7, R7, L8, S8, R8) in needs:
            if p7[(L7, S7, R7)] == S7 and p8[(L8, S8, R8)] == S8:
                ok = False
                break
        if not ok:
            continue
        liveness_pass += 1

        rules9 = rules_fixed + [p7, p8]
        result = verify(f"fill-{tested}", SC9, rules9, verbose=False)
        if result:
            elapsed = time.time() - t0
            print(f"\n*** FOUND! Trial {tested}/{total_search} ({elapsed:.1f}s) ***")
            verify("n=9 WITNESS", SC9, rules9, verbose=True)
            _print_witness(p7, p8)
            return rules9

        if tested % 500 == 0:
            elapsed = time.time() - t0
            print(f"  ...{tested}/{total_search}, liveness={liveness_pass}, {elapsed:.1f}s")

    elapsed = time.time() - t0
    print(f"  Exhausted {total_search}, {liveness_pass} liveness pass ({elapsed:.1f}s)")

    # If liveness-relevant search failed, also try making non-relevant entries
    # non-identity (for convergence). Try 1 extra entry at a time.
    print(f"\n  Trying with 1 extra non-identity entry from non-relevant set...")
    for extra in non_liveness_free:
        ep, eL, eS, eR = extra
        for ev in range(SC9[ep]):
            if ev == eS:
                continue
            for vals in cartesian(range(3), repeat=n_rel):
                p7 = dict(p7_det)
                p8 = dict(p8_det)
                for (proc, L, S, R) in non_liveness_free:
                    if (proc, L, S, R) == extra:
                        if proc == 7: p7[(L,S,R)] = ev
                        else: p8[(L,S,R)] = ev
                    else:
                        if proc == 7: p7[(L,S,R)] = S
                        else: p8[(L,S,R)] = S
                for i, (proc, L, S, R) in enumerate(liveness_entries):
                    if proc == 7: p7[(L,S,R)] = vals[i]
                    else: p8[(L,S,R)] = vals[i]

                ok = True
                for (L7, S7, R7, L8, S8, R8) in needs:
                    if p7[(L7,S7,R7)] == S7 and p8[(L8,S8,R8)] == S8:
                        ok = False; break
                if not ok:
                    continue

                rules9 = rules_fixed + [p7, p8]
                if verify(f"ext-{extra}", SC9, rules9, verbose=False):
                    print(f"\n*** FOUND with extra entry {extra}={ev}! ***")
                    verify("n=9 WITNESS", SC9, rules9, verbose=True)
                    _print_witness(p7, p8)
                    return rules9

    print(f"  No valid witness found with current cycle.")
    return None


def _print_witness(p7, p8):
    print(f"\n*** VALID n=9 WITNESS ***")
    print(f"State counts: {SC9}, product: 7776")
    print(f"\nP7 table (2,3,3):")
    for L in range(2):
        for S in range(3):
            row = [p7[(L,S,R)] for R in range(3)]
            print(f"  f({L},{S},*) = {row}")
    print(f"\nP8 table (3,3,2):")
    for L in range(3):
        for S in range(3):
            row = [p8[(L,S,R)] for R in range(2)]
            print(f"  f({L},{S},*) = {row}")


# ── main ─────────────────────────────────────────────────────────────

def main():
    # Verify n=8 witness first
    print("Verifying n=8 witness...")
    sc8, r8 = witness_n8()
    assert verify("n=8", sc8, r8, verbose=True)

    # Phase 0: Quick table search
    print(f"\n{'='*70}")
    print("Phase 0: Quick table search (P7 extension + P8 reuse)")
    print(f"{'='*70}\n")

    result = phase0_quick_search()
    if result:
        return

    # Phase 1: Cycle-first DFS
    print(f"\n{'='*70}")
    print("Phase 1: Cycle-first DFS with forced-move optimization")
    print(f"{'='*70}")

    result = phase1_cycle_dfs()
    if result:
        path, movers_list, entries = result
        print(f"\nCycle found! Length = {len(path) - 1}")
        print(f"Mover sequence: {movers_list}")
        fill_and_verify(path, movers_list, entries)
        return

    print("\nNo witness found.")


if __name__ == "__main__":
    main()
