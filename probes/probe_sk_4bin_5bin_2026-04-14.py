#!/usr/bin/env python3
"""4-binary and 5-binary SK binary-projection structural probes.

Hypothesis: the SK binary-cube projection contains the middle-layer
Hamiltonian cycle of the k-cube (k = number of binary positions) plus
structured pole/sub-layer attachments. This would connect our
structural theorem to Mütze's middle-layer Hamiltonicity theorem.

Experiments:
  (1) n=6  ms=(2,2,2,2,3,3)   4 consecutive binary  product 144
  (2) n=7  ms=(2,2,2,2,2,3,3) 5 consecutive binary  product 288

For each:
  * enumerate length-2n sweep cycles
  * compute SK(C)
  * project SK onto the binary positions (k-cube)
  * tabulate: vertices hit by weight class, edge histogram by
    (source weight → target weight) transition
  * check: is the binary-projection edge set equal to the middle
    layer + pole attachments?
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def enumerate_sweep_cycles(ms, n, max_found=40, time_budget=180.0):
    mover_seq = list(range(n)) * 2
    L = len(mover_seq)
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen = set()
    t0 = time.time()

    def dfs(step, config, det, path):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        if step == L:
            if config == path[0]:
                cycle_tup = tuple(path)
                if cycle_tup not in seen:
                    seen.add(cycle_tup)
                    found.append((list(path), list(mover_seq), dict(det)))
            return
        p = mover_seq[step]
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
        key_m = (p, Lp, Sp, Rp)
        forced_out = det.get(key_m)
        for new_val in range(ms[p]):
            if new_val == Sp: continue
            if forced_out is not None and forced_out != new_val: continue
            new_det = dict(det)
            new_det[key_m] = new_val
            consistent = True
            for i in range(n):
                if i == p: continue
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    consistent = False; break
                new_det[ki] = Si
            if not consistent: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(0, start, {}, [start])
    return found


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True; break
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
        rounds += 1
    return remaining, rounds


def binary_pos(ms):
    return [i for i, m in enumerate(ms) if m == 2]


def analyze(kernel, adj, ms, n):
    bpos = binary_pos(ms)
    k = len(bpos)

    # Vertices hit by weight.
    vertices_hit = set()
    by_weight = defaultdict(int)
    for c in kernel:
        bp = tuple(c[i] for i in bpos)
        vertices_hit.add(bp)
        by_weight[sum(bp)] += 1

    # Distinct edges in the projection.
    edges = Counter()
    edge_by_weight_trans = Counter()
    kset = set(kernel)
    edge_count_by_mover = Counter()
    for u in kernel:
        for v, p in adj.get(u, ()):
            if v not in kset: continue
            edge_count_by_mover[p] += 1
            if p in bpos:
                bu = tuple(u[i] for i in bpos)
                bv = tuple(v[i] for i in bpos)
                if bu != bv:
                    edges[(bu, bv)] += 1
                    edge_by_weight_trans[(sum(bu), sum(bv))] += 1

    return {
        "sk_size": len(kernel),
        "k": k,
        "vertices_hit": vertices_hit,
        "by_weight": dict(by_weight),
        "edges": dict(edges),
        "edge_by_weight_trans": dict(edge_by_weight_trans),
        "edge_count_by_mover": dict(edge_count_by_mover),
    }


def hamming_dist(a, b):
    return sum(x != y for x, y in zip(a, b))


def run(ms, label):
    n = len(ms)
    P = 1
    for m in ms: P *= m
    bpos = binary_pos(ms)
    k = len(bpos)
    print(f"\n{'='*66}")
    print(f"{label}")
    print(f"  ms={ms}  n={n}  product={P}  threshold={4*3**(n-2)}")
    print(f"  binary positions: {bpos}  k={k}")
    print(f"{'='*66}")

    t0 = time.time()
    cycles = enumerate_sweep_cycles(ms, n, max_found=30, time_budget=240.0)
    print(f"sweep cycles found: {len(cycles)} in {time.time()-t0:.1f}s")
    if not cycles:
        print("  NO CYCLES — try different max_length or ms")
        return

    infos = []
    for cycle, movers, det in cycles:
        good_set = set(cycle)
        ng, _, adj = build_forced_graph(ms, n, det, good_set)
        sk, rounds = sink_kernel(ng, adj)
        info = analyze(sk, adj, ms, n)
        info["rounds"] = rounds
        infos.append(info)

    # First cycle detail.
    info = infos[0]
    print(f"\nfirst cycle: |SK|={info['sk_size']}  rounds={info['rounds']}")
    print(f"  vertices hit: {len(info['vertices_hit'])} / {2**k}")
    print(f"  by binary weight:")
    for w in sorted(info["by_weight"].keys()):
        cfg_count = info["by_weight"][w]
        verts_at_w = sum(1 for v in info["vertices_hit"] if sum(v) == w)
        total_verts_at_w = 1  # C(k, w)
        from math import comb
        total_verts_at_w = comb(k, w)
        print(f"    weight {w}: {cfg_count} configs "
              f"({verts_at_w}/{total_verts_at_w} vertices hit)")
    print(f"  edges by mover proc: {info['edge_count_by_mover']}")
    print(f"  distinct binary-projection edges: {len(info['edges'])}")
    print(f"  edge weight transitions:")
    for (wu, wv), cnt in sorted(info["edge_by_weight_trans"].items()):
        print(f"    w{wu} -> w{wv}: {cnt}")

    # Dump the binary projection edges.
    print(f"\n  ALL binary projection edges (with multiplicity):")
    for (bu, bv), cnt in sorted(info["edges"].items()):
        dist = hamming_dist(bu, bv)
        print(f"    {bu} -> {bv}  [Hd={dist}]  x{cnt}")

    # Rigidity across cycles.
    print(f"\nRIGIDITY across {len(infos)} cycles:")
    sk_sizes = [info["sk_size"] for info in infos]
    print(f"  |SK|: {Counter(sk_sizes)}")
    weight_hists = [tuple(sorted(info["by_weight"].items())) for info in infos]
    print(f"  distinct weight histograms: {len(set(weight_hists))}")
    edge_sets = [frozenset(info["edges"].keys()) for info in infos]
    print(f"  distinct edge sets: {len(set(edge_sets))}")

    # Common edges across all cycles.
    common_edges = set.intersection(*(set(s) for s in edge_sets))
    print(f"  edges present in ALL cycles: {len(common_edges)}")

    # Middle-layer check.
    print(f"\n  MIDDLE-LAYER ANALYSIS (k={k}):")
    if k % 2 == 1:
        # Odd k — bipartite middle layer at weights m, m+1.
        m_mid = k // 2
        print(f"    odd k: middle = weight-{m_mid} + weight-{m_mid+1}")
        mid_edges_in_proj = [
            (bu, bv) for (bu, bv) in info["edges"]
            if {sum(bu), sum(bv)} == {m_mid, m_mid+1}
            and hamming_dist(bu, bv) == 1
        ]
        print(f"    middle-layer edges in projection: {len(mid_edges_in_proj)}")
        from math import comb
        total_mid_edges = comb(k, m_mid) * (m_mid + 1)
        print(f"    total middle-layer edges possible: {total_mid_edges}")
    else:
        # Even k — thick middle at weight-{m-1, m, m+1}.
        m_mid = k // 2
        print(f"    even k: thick middle = weight-{{{m_mid-1},{m_mid},{m_mid+1}}}")
        thick_edges_in_proj = [
            (bu, bv) for (bu, bv) in info["edges"]
            if sum(bu) in {m_mid-1, m_mid, m_mid+1}
            and sum(bv) in {m_mid-1, m_mid, m_mid+1}
            and hamming_dist(bu, bv) == 1
        ]
        print(f"    thick-middle edges in projection: {len(thick_edges_in_proj)}")


def main():
    run((2,2,2,2,3,3), "EXP 1  4 consecutive binary at n=6")
    run((2,2,2,2,2,3,3), "EXP 2  5 consecutive binary at n=7")


if __name__ == "__main__":
    main()
