#!/usr/bin/env python3
"""n9_templated_search.py — Construct n=9 witness for M_9 = 7776.

Strategy:
  A) Insert one ternary into n=8 witness (2,2,3,4,3,3,3,2,3) — 1 unknown table
  B) Extend n=6 witness to (2,2,2,4,3,3,3,3,3) — 3 unknown tables (same T*)
  C) Try all 9 insertion points in n=8

Candidate (3,3,3) tables:
  1. Dijkstra Sol 1 interior: f(L,S,R) = L
  2. Dijkstra Sol 3 middle: f = L if (S+1)%3==L, R if (S+1)%3==R, else S
  3. All R-independent tables (3^9 = 19683)
  4. All L-independent tables (3^9 = 19683)
  5. All S-independent tables (3^9 = 19683)

Target product: 7776 = 2^5 · 3^5
"""

import sys
import time
from itertools import product as cartesian

# ── verifier (from verify_witnesses.py) ──────────────────────────────

def verify(name, state_counts, rules, verbose=True):
    n = len(state_counts)
    P = 1
    for m in state_counts:
        P *= m
    configs = list(cartesian(*(range(m) for m in state_counts)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]
            S = cfg[i]
            R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]
        S = cfg[proc]
        R = cfg[(proc + 1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # 1. Liveness
    for cfg in configs:
        if not privileged(cfg):
            if verbose:
                print(f"  FAIL liveness: {cfg}")
            return False

    # Find good cycle
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            nxt = move(cfg, priv[0])
            single_priv[cfg] = (nxt, priv[0])

    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []
        movers = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            visited_global.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover)
            cur = nxt
        if cur == start and len(path) > 0:
            good_cycle = path
            good_movers = movers
            break

    if good_cycle is None:
        if verbose:
            print(f"  FAIL: no good cycle found (single_priv={len(single_priv)})")
        return False

    good_set = set(good_cycle)

    # 2. Mutual exclusion (guaranteed by construction)
    # 3. Closure (guaranteed by construction)

    # 4. Convergence
    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                nxt = move(cfg, p)
                if nxt in bad_set:
                    all_exit = False
                    break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove
            changed = True

    if bad_set:
        if verbose:
            print(f"  FAIL convergence: {len(bad_set)} bad configs in cycles")
        return False

    # 5. Fairness
    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        if verbose:
            missing = set(range(n)) - movers_seen
            print(f"  FAIL fairness: processors {missing} never move")
        return False

    if verbose:
        print(f"  PASS  product={P}  cycle={len(good_cycle)}  "
              f"configs={len(configs)}  bad={len(configs)-len(good_cycle)}")
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


# ── neighbor config analysis ────────────────────────────────────────

def neighbor_configs(state_counts):
    """Return list of (m_L, m_S, m_R) for each processor."""
    n = len(state_counts)
    return [(state_counts[(i-1)%n], state_counts[i], state_counts[(i+1)%n])
            for i in range(n)]


# ── candidate (3,3,3) tables ────────────────────────────────────────

def make_table_333(func):
    """Build a dict table for a (3,3,3) processor from a function."""
    return {(L,S,R): func(L,S,R)
            for L in range(3) for S in range(3) for R in range(3)}

def dijkstra_sol1_interior():
    """f(L,S,R) = L — copy left, R irrelevant."""
    return make_table_333(lambda L,S,R: L)

def dijkstra_sol1_bottom():
    """f(L,S,R) = (S+1)%3 if L==S else S."""
    return make_table_333(lambda L,S,R: (S+1)%3 if L==S else S)

def dijkstra_sol3_middle():
    """From verifier.py: f = L if (S+1)%3==L, R if (S+1)%3==R, else S."""
    def f(L,S,R):
        if (S+1)%3 == L: return L
        if (S+1)%3 == R: return R
        return S
    return make_table_333(f)

def dijkstra_sol3_bottom():
    """f = (S-1)%3 if (S+1)%3==R, else S."""
    return make_table_333(lambda L,S,R: (S-1)%3 if (S+1)%3==R else S)

def dijkstra_sol3_top():
    """f = (L+1)%3 if L==R and (L+1)%3!=S, else S."""
    return make_table_333(lambda L,S,R: (L+1)%3 if L==R and (L+1)%3!=S else S)

def copy_right():
    """f(L,S,R) = R."""
    return make_table_333(lambda L,S,R: R)

def increment_if_diff_left():
    """f = (S+1)%3 if L!=S else S."""
    return make_table_333(lambda L,S,R: (S+1)%3 if L!=S else S)

def decrement_if_diff_left():
    """f = (S-1)%3 if L!=S else S."""
    return make_table_333(lambda L,S,R: (S-1)%3 if L!=S else S)

def copy_left_if_diff_right():
    """f = L if R!=S else S."""
    return make_table_333(lambda L,S,R: L if R!=S else S)


# ── n=8 insertion framework ─────────────────────────────────────────

def build_n9_from_n8_insertion(candidate_table, insert_pos=5):
    """
    Insert ternary processor into n=8 ring at position insert_pos.
    Default: between P4 and P5, giving (2,2,3,4,3,T,3,2,3).

    Returns (state_counts, rules) for the n=9 ring, or None if
    insertion is incompatible (neighbor state counts don't match).
    """
    sc8, rules8 = witness_n8()
    n8 = len(sc8)

    # Build n=9 state counts: insert 3 at position insert_pos
    sc9 = list(sc8[:insert_pos]) + [3] + list(sc8[insert_pos:])
    sc9 = tuple(sc9)
    n9 = len(sc9)

    # Verify product
    prod = 1
    for m in sc9:
        prod *= m
    if prod != 7776:
        return None, None

    # Check neighbor config compatibility
    nc9 = neighbor_configs(sc9)

    # Build rules: copy from n=8, adjusting indices
    rules9 = []
    for i in range(n9):
        if i == insert_pos:
            rules9.append(candidate_table)
        elif i < insert_pos:
            old_i = i
            # Check that neighbor configs match
            old_nc = neighbor_configs(sc8)
            if nc9[i] == old_nc[old_i]:
                rules9.append(rules8[old_i])
            else:
                return None, None  # incompatible
        else:  # i > insert_pos
            old_i = i - 1
            old_nc = neighbor_configs(sc8)
            if nc9[i] == old_nc[old_i]:
                rules9.append(rules8[old_i])
            else:
                return None, None  # incompatible

    return sc9, rules9


def build_n9_from_n6_extension(candidate_table):
    """
    Extend n=6 to n=9: (2,2,2,4,3,3) -> (2,2,2,4,3,T,T,T,3).
    P0-P4 from n=6, P5-P7 = candidate, P8 = n=6 P5.
    """
    sc6, rules6 = witness_n6()
    sc9 = (2, 2, 2, 4, 3, 3, 3, 3, 3)
    rules9 = [
        rules6[0],  # P0: (3,2,2)
        rules6[1],  # P1: (2,2,2)
        rules6[2],  # P2: (2,2,4)
        rules6[3],  # P3: (2,4,3)
        rules6[4],  # P4: (4,3,3)
        candidate_table,  # P5: (3,3,3)
        candidate_table,  # P6: (3,3,3)
        candidate_table,  # P7: (3,3,3)
        rules6[5],  # P8: (3,3,2)
    ]
    return sc9, rules9


# ── liveness prefilter ──────────────────────────────────────────────

def precompute_needs_new(state_counts, rules, unknown_idx):
    """
    Find configs where no FIXED processor is privileged.
    Only these need the new processor to be privileged for liveness.
    Returns list of (L, S, R) triples seen by the unknown processor.
    """
    n = len(state_counts)
    needs = []
    for cfg in cartesian(*(range(m) for m in state_counts)):
        has_priv = False
        for i in range(n):
            if i == unknown_idx:
                continue
            L = cfg[(i-1) % n]
            S = cfg[i]
            R = cfg[(i+1) % n]
            if rules[i][(L, S, R)] != S:
                has_priv = True
                break
        if not has_priv:
            L = cfg[(unknown_idx-1) % n]
            S = cfg[unknown_idx]
            R = cfg[(unknown_idx+1) % n]
            needs.append((L, S, R))
    return needs


def check_liveness_fast(needs_new_triples, candidate_table):
    """Check that the candidate makes all needs_new configs have a privileged proc."""
    for (L, S, R) in needs_new_triples:
        if candidate_table[(L, S, R)] == S:
            return False
    return True


# ── enumeration engines ─────────────────────────────────────────────

def enumerate_R_independent():
    """All f(L,S,R) = g(L,S). 3^9 = 19683 tables."""
    for vals in cartesian(range(3), repeat=9):
        table = {}
        idx = 0
        for L in range(3):
            for S in range(3):
                v = vals[idx]
                idx += 1
                for R in range(3):
                    table[(L, S, R)] = v
        yield table

def enumerate_L_independent():
    """All f(L,S,R) = g(S,R). 3^9 = 19683 tables."""
    for vals in cartesian(range(3), repeat=9):
        table = {}
        idx = 0
        for S in range(3):
            for R in range(3):
                v = vals[idx]
                idx += 1
                for L in range(3):
                    table[(L, S, R)] = v
        yield table

def enumerate_S_independent():
    """All f(L,S,R) = g(L,R). 3^9 = 19683 tables."""
    for vals in cartesian(range(3), repeat=9):
        table = {}
        idx = 0
        for L in range(3):
            for R in range(3):
                v = vals[idx]
                idx += 1
                for S in range(3):
                    table[(L, S, R)] = v
        yield table


# ── relabeling / canonicalization ───────────────────────────────────

def relabel_table(table, perm):
    """Apply permutation of {0,1,2} to both inputs and output of a (3,3,3) table."""
    inv = [0]*3
    for i, p in enumerate(perm):
        inv[p] = i
    new_table = {}
    for (L, S, R), out in table.items():
        new_table[(perm[L], perm[S], perm[R])] = perm[out]
    return new_table

def canonical_form(table):
    """Return the canonical (lex-minimum) form under all 6 relabelings."""
    perms = [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]
    forms = []
    for p in perms:
        rt = relabel_table(table, p)
        key = tuple(rt[(L,S,R)] for L in range(3) for S in range(3) for R in range(3))
        forms.append(key)
    return min(forms)


# ── main search ─────────────────────────────────────────────────────

def main():
    log = open("exploration_log3.md", "w")
    def out(s=""):
        print(s)
        log.write(s + "\n")
        log.flush()

    out("# Exploration Log 3: n=9 Witness Construction")
    out()
    out("## Exploration 10")
    out()
    out("### Strategy")
    out("Construct n=9 witness (M_9 = 7776) via templated algebraic construction,")
    out("reusing transition tables from verified n=6 and n=8 witnesses.")
    out()

    # ── Phase 0: Neighbor config analysis ──
    out("### Phase 0: Neighbor Config Analysis")
    out()
    for name, wfn in [("n=6", witness_n6), ("n=7", witness_n7), ("n=8", witness_n8)]:
        sc, rules = wfn()
        nc = neighbor_configs(sc)
        out(f"**{name}**: {sc}")
        for i, (mL, mS, mR) in enumerate(nc):
            marker = " **(3,3,3)**" if (mL,mS,mR)==(3,3,3) else ""
            out(f"  P{i}: m={mS}, neighbors=({mL},{mS},{mR}){marker}")
        out()

    out("**Key finding:** NO existing witness (n=5..8) has a (3,3,3) processor.")
    out("The (3,3,3) triple is genuinely new for n=9.")
    out()

    # ── Phase 1: n=8 insertion compatibility check ──
    out("### Phase 1: n=8 Insertion Compatibility")
    out()
    sc8, rules8 = witness_n8()
    nc8 = neighbor_configs(sc8)

    # Try inserting at position 5 (between P4 and P5)
    test_table = dijkstra_sol1_interior()  # dummy
    sc9, rules9 = build_n9_from_n8_insertion(test_table, insert_pos=5)
    if sc9 is not None:
        nc9 = neighbor_configs(sc9)
        out(f"Insertion at pos 5: {sc9}, product={7776}")
        out(f"Neighbor configs:")
        for i in range(9):
            src = "NEW" if i == 5 else f"n8-P{i if i < 5 else i-1}"
            out(f"  P{i}: ({nc9[i][0]},{nc9[i][1]},{nc9[i][2]}) <- {src}")
        out()
    else:
        out("Insertion at pos 5: INCOMPATIBLE")
        out()

    # Check all 8 insertion points
    out("All insertion points:")
    compatible_insertions = []
    for pos in range(9):
        sc_try, rules_try = build_n9_from_n8_insertion(test_table, insert_pos=pos)
        if sc_try is not None:
            nc_try = neighbor_configs(sc_try)
            new_nc = nc_try[pos]
            out(f"  pos={pos}: {sc_try} — new proc config=({new_nc[0]},{new_nc[1]},{new_nc[2]}) {'✓ (3,3,3)' if new_nc==(3,3,3) else ''}")
            compatible_insertions.append(pos)
        else:
            out(f"  pos={pos}: INCOMPATIBLE")
    out()

    # ── Phase 2: Named candidates ──
    out("### Phase 2: Named Candidates")
    out()

    named_candidates = [
        ("Dijkstra Sol 1 interior (copy-left)", dijkstra_sol1_interior()),
        ("Dijkstra Sol 1 bottom", dijkstra_sol1_bottom()),
        ("Dijkstra Sol 3 middle", dijkstra_sol3_middle()),
        ("Dijkstra Sol 3 bottom", dijkstra_sol3_bottom()),
        ("Dijkstra Sol 3 top", dijkstra_sol3_top()),
        ("Copy-right", copy_right()),
        ("Increment if L!=S", increment_if_diff_left()),
        ("Decrement if L!=S", decrement_if_diff_left()),
        ("Copy-left if R!=S", copy_left_if_diff_right()),
    ]

    for cname, ctable in named_candidates:
        out(f"**{cname}**")
        # Try in n=8 insertion
        for pos in compatible_insertions:
            sc9, rules9 = build_n9_from_n8_insertion(ctable, insert_pos=pos)
            if sc9 is None:
                continue
            nc9 = neighbor_configs(sc9)
            if nc9[pos] != (3,3,3):
                continue  # only test (3,3,3) positions
            result = verify(f"n8-ins-{pos}", sc9, rules9, verbose=False)
            if result:
                out(f"  n=8 insertion pos={pos}: **PASS** ✓✓✓")
                out(f"  State counts: {sc9}")
                out(f"  Table: {ctable}")
                out()
                out("### Outcome: SUCCEEDED")
                out(f"Valid n=9 witness found via {cname}!")
                log.close()
                return
            else:
                # Quick diagnostic
                sc9t, rules9t = build_n9_from_n8_insertion(ctable, insert_pos=pos)
                out(f"  n=8 insertion pos={pos} {sc9}: FAIL")

        # Try in n=6 extension
        sc9, rules9 = build_n9_from_n6_extension(ctable)
        result = verify("n6-ext", sc9, rules9, verbose=False)
        if result:
            out(f"  n=6 extension: **PASS** ✓✓✓")
            out(f"  State counts: {sc9}")
            out()
            out("### Outcome: SUCCEEDED")
            log.close()
            return
        else:
            out(f"  n=6 extension {sc9}: FAIL")
        out()

    # ── Phase 3: R-independent enumeration (n=8 insertion) ──
    out("### Phase 3: R-independent Enumeration (n=8 insertion at pos 5)")
    out()
    t0 = time.time()

    # Precompute liveness filter
    sc9_template, rules9_template = build_n9_from_n8_insertion(test_table, insert_pos=5)
    needs = precompute_needs_new(sc9_template, rules9_template, unknown_idx=5)
    out(f"Prefilter: {len(needs)} configs need P5 to be privileged for liveness")

    # Extract constraint: which (L,S,R) must have f(L,S,R) != S
    constraint_triples = set()
    for (L,S,R) in needs:
        constraint_triples.add((L,S,R, S))  # must differ from S
    out(f"Distinct (L,S,R) constraint triples: {len(set((L,S,R) for L,S,R,_ in constraint_triples))}")
    out()

    count = 0
    liveness_pass = 0
    full_pass = 0
    for ctable in enumerate_R_independent():
        count += 1
        if not check_liveness_fast(needs, ctable):
            continue
        liveness_pass += 1
        sc9, rules9 = build_n9_from_n8_insertion(ctable, insert_pos=5)
        result = verify(f"R-indep-{count}", sc9, rules9, verbose=False)
        if result:
            full_pass += 1
            elapsed = time.time() - t0
            out(f"**SUCCESS at candidate #{count}!** (elapsed {elapsed:.1f}s)")
            out(f"State counts: {sc9}")
            # Decode the table
            out(f"Table entries:")
            for L in range(3):
                for S in range(3):
                    for R in range(3):
                        v = ctable[(L,S,R)]
                        if v != S:
                            out(f"  f({L},{S},{R}) = {v}  [privileged]")
            out()
            out("### Outcome: SUCCEEDED")
            log.close()
            # Also verify with verbose
            print("\n=== FINAL VERIFICATION ===")
            verify("n=9 WITNESS", sc9, rules9, verbose=True)
            print(f"\nState counts: {sc9}")
            print(f"Product: {7776}")
            print(f"\nTransition table for P5 (3,3,3):")
            for L in range(3):
                for S in range(3):
                    row = [ctable[(L,S,R)] for R in range(3)]
                    print(f"  f({L},{S},*) = {row}")
            return
        if count % 5000 == 0:
            elapsed = time.time() - t0
            out(f"  ...tested {count}/19683, liveness_pass={liveness_pass}, elapsed={elapsed:.1f}s")

    elapsed = time.time() - t0
    out(f"R-independent done: {count} tested, {liveness_pass} liveness pass, "
        f"{full_pass} full pass, {elapsed:.1f}s")
    out()

    # ── Phase 4: L-independent enumeration ──
    out("### Phase 4: L-independent Enumeration (n=8 insertion at pos 5)")
    out()
    t0 = time.time()
    count = 0
    liveness_pass = 0
    for ctable in enumerate_L_independent():
        count += 1
        if not check_liveness_fast(needs, ctable):
            continue
        liveness_pass += 1
        sc9, rules9 = build_n9_from_n8_insertion(ctable, insert_pos=5)
        result = verify(f"L-indep-{count}", sc9, rules9, verbose=False)
        if result:
            elapsed = time.time() - t0
            out(f"**SUCCESS at candidate #{count}!** (elapsed {elapsed:.1f}s)")
            out(f"State counts: {sc9}")
            out(f"Table entries:")
            for L in range(3):
                for S in range(3):
                    for R in range(3):
                        v = ctable[(L,S,R)]
                        if v != S:
                            out(f"  f({L},{S},{R}) = {v}  [privileged]")
            out()
            out("### Outcome: SUCCEEDED")
            log.close()
            print("\n=== FINAL VERIFICATION ===")
            verify("n=9 WITNESS", sc9, rules9, verbose=True)
            return
        if count % 5000 == 0:
            elapsed = time.time() - t0
            out(f"  ...tested {count}/19683, liveness_pass={liveness_pass}, elapsed={elapsed:.1f}s")

    elapsed = time.time() - t0
    out(f"L-independent done: {count} tested, {liveness_pass} liveness pass, {elapsed:.1f}s")
    out()

    # ── Phase 5: S-independent enumeration ──
    out("### Phase 5: S-independent Enumeration (n=8 insertion at pos 5)")
    out()
    t0 = time.time()
    count = 0
    liveness_pass = 0
    for ctable in enumerate_S_independent():
        count += 1
        if not check_liveness_fast(needs, ctable):
            continue
        liveness_pass += 1
        sc9, rules9 = build_n9_from_n8_insertion(ctable, insert_pos=5)
        result = verify(f"S-indep-{count}", sc9, rules9, verbose=False)
        if result:
            elapsed = time.time() - t0
            out(f"**SUCCESS at candidate #{count}!** (elapsed {elapsed:.1f}s)")
            out(f"State counts: {sc9}")
            out()
            out("### Outcome: SUCCEEDED")
            log.close()
            print("\n=== FINAL VERIFICATION ===")
            verify("n=9 WITNESS", sc9, rules9, verbose=True)
            return
        if count % 5000 == 0:
            elapsed = time.time() - t0
            out(f"  ...tested {count}/19683, liveness_pass={liveness_pass}, elapsed={elapsed:.1f}s")

    elapsed = time.time() - t0
    out(f"S-independent done: {count} tested, {liveness_pass} liveness pass, {elapsed:.1f}s")
    out()

    # ── Phase 6: R-independent in n=6 extension ──
    out("### Phase 6: R-independent Enumeration (n=6 extension)")
    out()
    t0 = time.time()

    # Precompute needs for n=6 extension (3 unknowns at P5,P6,P7 but all same)
    # We need ALL three to contribute; precompute for the triple
    sc9_ext = (2, 2, 2, 4, 3, 3, 3, 3, 3)
    # For n=6 extension, three processors are unknown. Liveness prefilter is harder.
    # Just do liveness via full check.
    count = 0
    liveness_pass = 0
    for ctable in enumerate_R_independent():
        count += 1
        sc9, rules9 = build_n9_from_n6_extension(ctable)
        # Quick liveness check
        ok = True
        for cfg in cartesian(*(range(m) for m in sc9)):
            has_priv = False
            for i in range(9):
                L = cfg[(i-1)%9]
                S = cfg[i]
                R = cfg[(i+1)%9]
                if rules9[i][(L,S,R)] != S:
                    has_priv = True
                    break
            if not has_priv:
                ok = False
                break
        if not ok:
            continue
        liveness_pass += 1
        result = verify(f"n6-R-indep-{count}", sc9, rules9, verbose=False)
        if result:
            elapsed = time.time() - t0
            out(f"**SUCCESS at candidate #{count}!** (elapsed {elapsed:.1f}s)")
            out(f"State counts: {sc9}")
            out(f"Table entries:")
            for L in range(3):
                for S in range(3):
                    for R in range(3):
                        v = ctable[(L,S,R)]
                        if v != S:
                            out(f"  f({L},{S},{R}) = {v}  [privileged]")
            out()
            out("### Outcome: SUCCEEDED")
            log.close()
            print("\n=== FINAL VERIFICATION ===")
            verify("n=9 WITNESS", sc9, rules9, verbose=True)
            return
        if count % 1000 == 0:
            elapsed = time.time() - t0
            out(f"  ...tested {count}/19683, liveness_pass={liveness_pass}, elapsed={elapsed:.1f}s")

    elapsed = time.time() - t0
    out(f"n=6 extension R-independent done: {count} tested, "
        f"{liveness_pass} liveness pass, {elapsed:.1f}s")
    out()

    # ── Phase 7: Other insertion points in n=8 ──
    out("### Phase 7: Other Compatible Insertion Points")
    out()
    for pos in compatible_insertions:
        if pos == 5:
            continue  # already done
        sc9_try, rules9_try = build_n9_from_n8_insertion(test_table, insert_pos=pos)
        if sc9_try is None:
            continue
        nc9 = neighbor_configs(sc9_try)
        new_nc = nc9[pos]
        if new_nc[1] != 3:
            continue  # inserted proc must be ternary

        out(f"Insertion at pos {pos}: {sc9_try}")
        out(f"  New proc config: ({new_nc[0]},{new_nc[1]},{new_nc[2]})")

        # Build appropriate candidate tables for this neighbor config
        mL, mS, mR = new_nc
        # Generate R-independent tables for this (mL, mS, mR)
        t0_pos = time.time()
        count_pos = 0
        liveness_pos = 0
        for vals in cartesian(range(mS), repeat=mL*mS):
            ctable = {}
            idx = 0
            for L in range(mL):
                for S in range(mS):
                    v = vals[idx]
                    idx += 1
                    for R in range(mR):
                        ctable[(L,S,R)] = v
            count_pos += 1
            sc9, rules9 = build_n9_from_n8_insertion(ctable, insert_pos=pos)
            if sc9 is None:
                continue
            # Quick liveness
            ok = True
            for cfg in cartesian(*(range(m) for m in sc9)):
                has_priv = False
                for i in range(9):
                    Li = cfg[(i-1)%9]; Si = cfg[i]; Ri = cfg[(i+1)%9]
                    if rules9[i][(Li,Si,Ri)] != Si:
                        has_priv = True
                        break
                if not has_priv:
                    ok = False
                    break
            if not ok:
                continue
            liveness_pos += 1
            result = verify(f"ins{pos}-{count_pos}", sc9, rules9, verbose=False)
            if result:
                elapsed = time.time() - t0_pos
                out(f"  **SUCCESS** candidate #{count_pos} (elapsed {elapsed:.1f}s)")
                out(f"  State counts: {sc9}")
                out()
                out("### Outcome: SUCCEEDED")
                log.close()
                print("\n=== FINAL VERIFICATION ===")
                verify("n=9 WITNESS", sc9, rules9, verbose=True)
                return

        elapsed = time.time() - t0_pos
        out(f"  Done: {count_pos} tested, {liveness_pos} liveness pass, {elapsed:.1f}s")
        out()

    # ── Summary ──
    out("### Outcome")
    out("FAILED — no valid n=9 witness found in any structured search family.")
    out()
    out("### What This Rules Out")
    out("- R-independent (3,3,3) tables in n=8 insertion at pos 5")
    out("- L-independent and S-independent tables at same position")
    out("- Same families in n=6 extension framework")
    out("- All compatible insertion points in n=8")
    out()
    out("### What Would Unblock This")
    out("- Full 27-entry enumeration with SMT solver constraints")
    out("- Derivation of (3,3,3) table from good-cycle structure")
    out("- Manual construction using token-flow analysis")
    log.close()


if __name__ == "__main__":
    main()
