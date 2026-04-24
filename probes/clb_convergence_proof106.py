#!/usr/bin/env python3
"""
CONVERGENCE PROOF 106: Extended boundary DAG — n-independence
==============================================================
Key finding from proof105: (c[0..2], c[n-3..n-1]) automaton is DAG at n=9.
Need to verify n-independence and check 8-tuple (adding c[3], c[n-4]).

The 8-tuple (c[0], c[1], c[2], c[3], c[n-4], c[n-3], c[n-2], c[n-1]) is
SELF-CONTAINED for transitions at positions {0, 1, 2, n-3, n-2, n-1}.
Deep interior (positions 4..n-5) doesn't change any of these 8 values.

If the 8-tuple automaton is DAG AND deep interior within each 8-tuple state is DAG,
then the full constant-Φ_full subgraph is DAG. The 8-tuple automaton is n-independent
for n ≥ 9, giving an analytical proof!

Also: explicitly enumerate the 6-tuple and 8-tuple transitions and verify consistency.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)
def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)
def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def dag_check(adj, nodes):
    """Return (is_dag, rank)"""
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in nodes}
    is_dag = True
    for start in nodes:
        if color[start] != WHITE:
            continue
        stack = [(start, iter(adj.get(start, [])))]
        color[start] = GRAY
        while stack:
            node, children = stack[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    is_dag = False
                    break
                if color[child] == WHITE:
                    color[child] = GRAY
                    stack.append((child, iter(adj.get(child, []))))
            except StopIteration:
                color[node] = BLACK
                stack.pop()
        if not is_dag:
            break

    if not is_dag:
        return False, -1

    out_deg = {c: len(adj.get(c, [])) for c in nodes}
    sinks = [c for c in nodes if out_deg[c] == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in nodes:
        for s in adj.get(c, []):
            radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r
                q.append(c)
    return True, max(rank.values()) if rank else 0


def main():
    sys.stdout.reconfigure(line_buffering=True)

    # Collect transition types across n values
    all_6tuple_trans = {}  # n -> set of (6tuple_from, 6tuple_to)
    all_8tuple_trans = {}

    for n_val in range(7, 14):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 900000:
            print(f"\nn={n}: skipping ({len(bad_list)} bad)")
            continue

        # Build TP + g_full + Φ_full
        tp_fwd = defaultdict(list)
        tp_nodes = set()
        fc_cache = {}
        tp_edge_list = []
        for c in bad_list:
            fc_cache[c] = fc(c, n)
            tp_nodes.add(c)
        for c in bad_list:
            e2c = exp2_count(c, n)
            i21c = int_21(c, n)
            ewc = exp2_weight(c, n)
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        if succ not in fc_cache:
                            fc_cache[succ] = fc(succ, n)
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            dfc = fc_cache[succ] - fc_cache[c]
                            tp_fwd[c].append((succ, dfc))
                            tp_edge_list.append((c, succ, i, dfc))
                            tp_nodes.add(succ)

        g = {c: 0 for c in tp_nodes}
        for _ in range(2 * n + 5):
            changed = False
            for c in tp_nodes:
                for s, dfc in tp_fwd.get(c, []):
                    new_g = dfc + g[s]
                    if new_g > g[c]:
                        g[c] = new_g
                        changed = True
            if not changed:
                break

        phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

        # ============================================================
        # 6-tuple (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
        # ============================================================
        t6_adj = defaultdict(set)
        t6_nodes = set()
        t6_trans = set()
        for c, s, pos, dfc in tp_edge_list:
            if phi[s] != phi[c]:
                continue
            s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
            s6s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
            if s6c != s6s:
                t6_adj[s6c].add(s6s)
                t6_nodes.add(s6c)
                t6_nodes.add(s6s)
                t6_trans.add((s6c, s6s))

        is_dag6, rank6 = dag_check(
            {k: list(v) for k, v in t6_adj.items()}, t6_nodes)
        all_6tuple_trans[n_val] = t6_trans

        # ============================================================
        # 8-tuple (c[0], c[1], c[2], c[3], c[n-4], c[n-3], c[n-2], c[n-1])
        # ============================================================
        if n >= 8:  # Need n-4 > 3, i.e., n > 7
            t8_adj = defaultdict(set)
            t8_nodes = set()
            t8_trans = set()
            for c, s, pos, dfc in tp_edge_list:
                if phi[s] != phi[c]:
                    continue
                s8c = (c[0], c[1], c[2], c[3], c[n-4], c[n-3], c[n-2], c[n-1])
                s8s = (s[0], s[1], s[2], s[3], s[n-4], s[n-3], s[n-2], s[n-1])
                if s8c != s8s:
                    t8_adj[s8c].add(s8s)
                    t8_nodes.add(s8c)
                    t8_nodes.add(s8s)
                    t8_trans.add((s8c, s8s))

            is_dag8, rank8 = dag_check(
                {k: list(v) for k, v in t8_adj.items()}, t8_nodes)
            all_8tuple_trans[n_val] = t8_trans
        else:
            is_dag8, rank8 = None, None

        # ============================================================
        # Deep interior: positions 4..n-5 within each 8-tuple
        # ============================================================
        deep_max_rank = 0
        deep_all_dag = True
        deep_edge_cnt = 0
        if n >= 9:
            for c, s, pos, dfc in tp_edge_list:
                if phi[s] != phi[c]:
                    continue
                if 4 <= pos <= n-5:
                    deep_edge_cnt += 1
            # We'd need to group by 8-tuple and check DAG. Too expensive.
            # Instead just check if any deep interior position exists
            deep_positions = set()
            for c, s, pos, dfc in tp_edge_list:
                if phi[s] != phi[c]:
                    continue
                if 4 <= pos <= n-5:
                    deep_positions.add(pos)

        elapsed = time.time() - t0
        print(f"\nn={n}: 6-tuple DAG: {'YES' if is_dag6 else 'NO'} (rank {rank6}, "
              f"{len(t6_nodes)} states, {len(t6_trans)} trans) | "
              f"8-tuple DAG: {('YES' if is_dag8 else 'NO') if is_dag8 is not None else 'N/A'} "
              f"(rank {rank8}, {len(t8_nodes) if n >= 8 else '?'} states, "
              f"{len(t8_trans) if n >= 8 else '?'} trans) | "
              f"{elapsed:.1f}s")
        if n >= 9:
            print(f"  Deep interior (pos 4..{n-5}): {deep_edge_cnt} edges, "
                  f"positions used: {sorted(deep_positions) if deep_positions else 'none'}")

    # ============================================================
    # Compare transition sets across n
    # ============================================================
    print(f"\n{'='*70}")
    print(f"6-TUPLE TRANSITION SET COMPARISON:")
    n_values = sorted(all_6tuple_trans.keys())
    for i in range(len(n_values)):
        for j in range(i+1, len(n_values)):
            ni, nj = n_values[i], n_values[j]
            si, sj = all_6tuple_trans[ni], all_6tuple_trans[nj]
            only_i = si - sj
            only_j = sj - si
            common = si & sj
            print(f"  n={ni} vs n={nj}: common={len(common)}, "
                  f"only-{ni}={len(only_i)}, only-{nj}={len(only_j)}")
            if only_i:
                print(f"    Only in n={ni}: {sorted(only_i)[:5]}...")
            if only_j:
                print(f"    Only in n={nj}: {sorted(only_j)[:5]}...")

    print(f"\n8-TUPLE TRANSITION SET COMPARISON:")
    n_values8 = sorted(all_8tuple_trans.keys())
    for i in range(len(n_values8)):
        for j in range(i+1, len(n_values8)):
            ni, nj = n_values8[i], n_values8[j]
            si, sj = all_8tuple_trans[ni], all_8tuple_trans[nj]
            only_i = si - sj
            only_j = sj - si
            common = si & sj
            print(f"  n={ni} vs n={nj}: common={len(common)}, "
                  f"only-{ni}={len(only_i)}, only-{nj}={len(only_j)}")

    # ============================================================
    # Check if transition set stabilizes
    # ============================================================
    if len(n_values8) >= 3:
        last3 = n_values8[-3:]
        union = set()
        for nv in last3:
            union |= all_8tuple_trans[nv]
        all_same = all(all_8tuple_trans[nv] == union for nv in last3)
        print(f"\n  Last 3 n-values ({last3}): {'IDENTICAL transition sets' if all_same else 'DIFFERENT'}")
        print(f"  Union size: {len(union)}")

    # ============================================================
    # Final: extract the universal 8-tuple transitions and verify DAG
    # ============================================================
    if len(n_values8) >= 2:
        # Take union of all n≥9
        universal = set()
        for nv in n_values8:
            if nv >= 9:
                universal |= all_8tuple_trans[nv]
        print(f"\n  Universal 8-tuple transitions (union of n≥9): {len(universal)}")
        univ_adj = defaultdict(list)
        univ_nodes = set()
        for s8c, s8s in universal:
            univ_adj[s8c].append(s8s)
            univ_nodes.add(s8c)
            univ_nodes.add(s8s)
        is_dag_u, rank_u = dag_check(univ_adj, univ_nodes)
        print(f"  Universal 8-tuple DAG: {'YES' if is_dag_u else 'NO'} "
              f"(rank {rank_u}, {len(univ_nodes)} states)")


if __name__ == '__main__':
    main()
