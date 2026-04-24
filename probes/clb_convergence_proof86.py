#!/usr/bin/env python3
"""
CONVERGENCE PROOF 86: DAG rank analysis of triple-preserved subgraph
=====================================================================
Compute the DAG rank for every config in the TP subgraph, then look for
patterns: what features determine the rank? Can it be expressed as a formula?

Also: decompose by (fc, boundary_state) and see if rank has structure.
"""
import sys
import os
import time
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


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 11):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP subgraph
        tp_adj = defaultdict(list)
        tp_radj = defaultdict(list)  # reverse adj
        tp_nodes = set()
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
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            tp_adj[c].append(succ)
                            tp_radj[succ].append(c)
                            tp_nodes.add(c)
                            tp_nodes.add(succ)

        # Topological sort + DAG rank (distance to sinks)
        out_deg = defaultdict(int)
        for c in tp_nodes:
            out_deg[c] = len(tp_adj[c])

        sinks = [c for c in tp_nodes if out_deg[c] == 0]
        # Also add bad configs with NO TP outgoing edges at all
        for c in bad_list:
            if c not in tp_nodes:
                sinks.append(c)
                tp_nodes.add(c)

        # BFS from sinks in reverse direction to compute rank
        rank = {}
        for c in sinks:
            rank[c] = 0
        q = deque(sinks)
        while q:
            c = q.popleft()
            for p in tp_radj[c]:
                new_r = rank[c] + 1
                if p not in rank or new_r > rank[p]:
                    rank[p] = new_r
                    q.append(p)

        max_rank = max(rank.values()) if rank else 0
        elapsed = time.time() - t0

        print(f"\n{'='*70}")
        print(f"n={n}: max rank = {max_rank}, {len(tp_nodes)} nodes ({elapsed:.1f}s)")

        # Find the highest-ranked configs
        top_configs = sorted([(r, c) for c, r in rank.items()], reverse=True)[:5]
        print(f"\n  Top 5 configs by rank:")
        for r, c in top_configs:
            print(f"    rank={r}: {c}  fc={fc(c,n)} e2={exp2_count(c,n)} "
                  f"i21={int_21(c,n)} ew={exp2_weight(c,n)}")

        # Rank distribution by fc
        fc_rank = defaultdict(list)
        for c, r in rank.items():
            fc_rank[fc(c, n)].append(r)

        print(f"\n  Rank distribution by fc:")
        for fv in sorted(fc_rank.keys()):
            rs = fc_rank[fv]
            print(f"    fc={fv}: {len(rs)} configs, rank ∈ [{min(rs)},{max(rs)}], "
                  f"mean={sum(rs)/len(rs):.1f}")

        # Rank distribution by boundary state
        bnd_rank = defaultdict(list)
        for c, r in rank.items():
            bnd = (c[0], c[1], c[n - 2], c[n - 1])
            bnd_rank[bnd].append(r)

        print(f"\n  Rank by boundary (top 10 by max rank):")
        top_bnd = sorted(bnd_rank.items(), key=lambda x: max(x[1]), reverse=True)[:10]
        for bnd, rs in top_bnd:
            print(f"    bnd={bnd}: {len(rs)} configs, rank ∈ [{min(rs)},{max(rs)}]")

        # Try: rank ≈ α·fc + β·int_fc + γ ?
        # Compute correlation between rank and fc
        if len(rank) > 1:
            from statistics import correlation
            items = [(fc(c, n), r) for c, r in rank.items()]
            fc_vals = [x[0] for x in items]
            r_vals = [x[1] for x in items]
            try:
                corr = correlation(fc_vals, r_vals)
                print(f"\n  Correlation(fc, rank) = {corr:.4f}")
            except Exception:
                pass

        # Check: is rank well-predicted by (fc, boundary, interior_pattern)?
        # Group by (fc, boundary) — what's the rank range?
        fb_rank = defaultdict(list)
        for c, r in rank.items():
            fb = (fc(c, n), c[0], c[1], c[n - 2], c[n - 1])
            fb_rank[fb].append(r)

        spread = [(max(rs) - min(rs), fb, len(rs)) for fb, rs in fb_rank.items() if len(rs) > 1]
        spread.sort(reverse=True)
        if spread:
            print(f"\n  (fc, boundary) rank spread (top 5):")
            for sp, fb, cnt in spread[:5]:
                print(f"    {fb}: {cnt} configs, rank ∈ [{min(fb_rank[fb])},{max(fb_rank[fb])}], "
                      f"spread={sp}")

        # Key question: what INTERIOR feature explains rank within (fc, boundary)?
        # Try adding interior 2-count
        fbi_rank = defaultdict(list)
        for c, r in rank.items():
            cnt2 = sum(1 for j in range(2, n - 2) if c[j] == 2)
            fbi = (fc(c, n), c[0], c[1], c[n - 2], c[n - 1], cnt2)
            fbi_rank[fbi].append(r)

        spread2 = [(max(rs) - min(rs), fbi, len(rs)) for fbi, rs in fbi_rank.items() if len(rs) > 1]
        spread2.sort(reverse=True)
        if spread2:
            max_sp2 = spread2[0][0]
            print(f"\n  (fc, bnd, cnt2_int) rank spread: max={max_sp2}")
            for sp, fbi, cnt in spread2[:3]:
                print(f"    {fbi}: {cnt} configs, spread={sp}")

        # Try the full interior as a string
        int_rank = defaultdict(list)
        for c, r in rank.items():
            interior = c[2:n - 2]
            int_key = (fc(c, n), c[0], c[1], c[n - 2], c[n - 1], interior)
            int_rank[int_key].append(r)

        spread3 = [(max(rs) - min(rs), k) for k, rs in int_rank.items() if len(rs) > 1]
        if spread3:
            print(f"\n  (fc, bnd, full_interior) spread: max={max(s for s, _ in spread3)}")
        else:
            print(f"\n  (fc, bnd, full_interior) UNIQUELY determines rank!")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
