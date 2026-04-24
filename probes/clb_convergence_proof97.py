#!/usr/bin/env python3
"""
CONVERGENCE PROOF 97: Anomalous entry sequence analysis
=========================================================
In any TP cycle, total Δfc = 0. Only 5 entries have Δfc > 0:
  A1: pos 0, T_bot(0,0,0)→1, Δfc=+2  [c[n-1]=0, c[0]=0, c[1]=0]
  A2: pos 0, T_bot(1,1,2)→0, Δfc=+1  [c[n-1]=1, c[0]=1, c[1]=2]
  A3: pos 2, T_mid(2,1,1)→0, Δfc=+1  [c[1]=2, c[2]=1, c[3]=1]
  A4: pos n-2, T_high(1,1,1)→2, Δfc=+2  [c[n-3]=1, c[n-2]=1, c[n-1]=1]
  A5: pos n-1, T_top(2,0,0)→1, Δfc=+1  [c[n-2]=2, c[n-1]=0, c[0]=0]

Key question: which pairs (Ai, Aj) can appear consecutively in a TP path?
More precisely: after Ai fires, can we reach a state where Aj fires,
using only Δfc≤0 TP edges in between?

If the reachability graph on {A1..A5} has no cycle with total Δfc>0
matching the available budget, we rule out TP cycles.
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

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


def classify_anomalous(c, succ, pos, n):
    """Classify a TP edge as anomalous entry A1-A5 or None."""
    L = c[(pos - 1) % n]; S = c[pos]; R = c[(pos + 1) % n]; out = succ[pos]
    dfc = fc(succ, n) - fc(c, n)
    if dfc <= 0:
        return None
    if pos == 0:
        if (L, S, R, out) == (0, 0, 0, 1):
            return 'A1'
        elif (L, S, R, out) == (1, 1, 2, 0):
            return 'A2'
    elif pos == 2:
        if (L, S, R, out) == (2, 1, 1, 0):
            return 'A3'
    elif pos == n - 2:
        if (L, S, R, out) == (1, 1, 1, 2):
            return 'A4'
    elif pos == n - 1:
        if (L, S, R, out) == (2, 0, 0, 1):
            return 'A5'
    return f'UNKNOWN(pos={pos},L={L},S={S},R={R},out={out},dfc={dfc})'


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [7, 8, 9]:
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP edges classified by anomalous type
        tp_adj = defaultdict(list)  # config → [(succ, dfc, anom_type)]
        tp_adj_neg = defaultdict(list)  # Δfc≤0 edges only
        anom_edges = defaultdict(list)  # anom_type → [(c, succ)]
        anom_from = defaultdict(set)  # anom_type → set of (source configs)
        anom_to = defaultdict(set)  # anom_type → set of (dest configs)

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
                            dfc = fc(succ, n) - fc(c, n)
                            atype = classify_anomalous(c, succ, i, n)
                            tp_adj[c].append((succ, dfc, atype))
                            if dfc <= 0:
                                tp_adj_neg[c].append(succ)
                            if atype:
                                anom_edges[atype].append((c, succ))
                                anom_from[atype].add(c)
                                anom_to[atype].add(succ)

        print(f"\n{'='*70}")
        print(f"n={n}")
        for atype in sorted(anom_edges.keys()):
            print(f"  {atype}: {len(anom_edges[atype])} edges")

        # For each anomalous entry Ai: from its DESTINATION configs,
        # can we reach the SOURCE of Aj using only Δfc≤0 edges?
        # BFS from destinations of each Ai
        print(f"\n  Reachability matrix (Ai→Aj via Δfc≤0 paths):")
        anom_types = sorted(anom_edges.keys())

        for ai in anom_types:
            # BFS from all destinations of Ai
            frontier = set()
            for _, succ in anom_edges[ai]:
                frontier.add(succ)
            visited = set(frontier)
            reachable = set(frontier)
            while frontier:
                next_frontier = set()
                for node in frontier:
                    for s in tp_adj_neg.get(node, []):
                        if s not in visited:
                            visited.add(s)
                            next_frontier.add(s)
                            reachable.add(s)
                frontier = next_frontier

            # Check which Aj sources are reachable
            row = []
            for aj in anom_types:
                overlap = reachable & anom_from[aj]
                row.append(len(overlap))
            print(f"    {ai} → " + " ".join(f"{aj}:{cnt}" for aj, cnt in zip(anom_types, row)))

        # More detailed: track min Δfc on paths between anomalous entries
        print(f"\n  Min accumulated Δfc from Ai dest to Aj source:")
        dfc_values = {'+2': {'A1', 'A4'}, '+1': {'A2', 'A3', 'A5'}}
        for ai in anom_types:
            # BFS with Δfc tracking
            dist = {}  # config → min accumulated Δfc
            for _, succ in anom_edges[ai]:
                dist[succ] = 0
            frontier = set(dist.keys())
            while frontier:
                next_frontier = set()
                for node in frontier:
                    for s, dfc, _ in tp_adj.get(node, []):
                        if dfc <= 0:
                            new_dist = dist[node] + dfc
                            if s not in dist or new_dist > dist[s]:
                                # Track MAXIMUM (closest to 0 = hardest to rule out)
                                dist[s] = new_dist
                                next_frontier.add(s)
                frontier = next_frontier

            for aj in anom_types:
                sources = anom_from[aj]
                reachable_sources = {s: dist[s] for s in sources if s in dist}
                if reachable_sources:
                    max_dfc = max(reachable_sources.values())
                    min_dfc = min(reachable_sources.values())
                    ai_dfc = 2 if ai in {'A1', 'A4'} else 1
                    print(f"    {ai}(+{ai_dfc}) → Δfc[{max_dfc:+d}..{min_dfc:+d}] → {aj}: "
                          f"{len(reachable_sources)}/{len(sources)} sources reachable. "
                          f"Net: [{ai_dfc + max_dfc:+d}..{ai_dfc + min_dfc:+d}]")
                else:
                    print(f"    {ai} → {aj}: NOT REACHABLE")

        # Find actual Δfc>0 sequences in the TP graph
        # BFS tracking sequence of anomalous entries
        print(f"\n  All Δfc>0 entry sequences (up to length 4):")
        seq_count = Counter()
        # Start from every config, BFS collecting anomalous sequences
        for start_atype in anom_types:
            for start_c, start_s in anom_edges[start_atype][:100]:  # sample
                # BFS from start_s tracking (node, seq, total_dfc)
                stack = [(start_s, (start_atype,), 2 if start_atype in {'A1','A4'} else 1)]
                visited = {start_s: 0}
                while stack:
                    node, seq, total_dfc_pos = stack.pop()
                    for s, dfc, atype in tp_adj.get(node, []):
                        if atype and len(seq) < 4:
                            new_seq = seq + (atype,)
                            new_total = total_dfc_pos + (2 if atype in {'A1','A4'} else 1)
                            seq_count[new_seq] += 1
                        elif dfc <= 0:
                            if s not in visited or 0 > visited[s]:
                                visited[s] = 0
                                if total_dfc_pos <= 10:
                                    stack.append((s, seq, total_dfc_pos))

        for seq, cnt in sorted(seq_count.items(), key=lambda x: (-len(x[0]), -x[1]))[:30]:
            total_pos = sum(2 if a in {'A1','A4'} else 1 for a in seq)
            print(f"    {' → '.join(seq)}: {cnt} (total +{total_pos})")

        # Critical check: boundary state constraints
        # A1 needs: c[n-1]=0, c[0]=0, c[1]=0
        # A2 needs: c[n-1]=1, c[0]=1, c[1]=2
        # A3 needs: c[1]=2, c[2]=1, c[3]=1
        # A4 needs: c[n-3]=1, c[n-2]=1, c[n-1]=1
        # A5 needs: c[n-2]=2, c[n-1]=0, c[0]=0
        # After A1: c[0] becomes 1 (was 0)
        # After A2: c[0] becomes 0 (was 1)
        # After A3: c[2] becomes 0 (was 1)
        # After A4: c[n-2] becomes 2 (was 1)
        # After A5: c[n-1] becomes 1 (was 0)

        print(f"\n  Boundary state before/after anomalous entries:")
        for atype in anom_types:
            before_bnd = Counter()
            after_bnd = Counter()
            for c, s in anom_edges[atype]:
                bnd_c = (c[0], c[1], c[n-2], c[n-1])
                bnd_s = (s[0], s[1], s[n-2], s[n-1])
                before_bnd[bnd_c] += 1
                after_bnd[bnd_s] += 1
            print(f"  {atype}:")
            for bnd, cnt in sorted(before_bnd.items()):
                print(f"    before: bnd={bnd} [{cnt}]")
            for bnd, cnt in sorted(after_bnd.items()):
                print(f"    after:  bnd={bnd} [{cnt}]")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
