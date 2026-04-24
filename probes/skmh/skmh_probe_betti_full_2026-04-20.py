#!/usr/bin/env python3
"""SKMH Exploration 3 — Full Betti vector (all dims) of NG(C).

E2 found β_1 = 0 uniformly on ∏Δ^{m_i-1} induced subcomplex.
E2 found β_2 intermittent (1 at all-binary, 1 on one mixed, 0 elsewhere).

E3 weakens the target: for each cycle, does SOME β_k > 0 for k ≥ 1?

If yes uniformly at sub-threshold → LB reformulates as "∃k. β_k(NG(C)) > 0",
a topological invariant that forbids self-stab via Morse inequality.

If no for some sub-threshold cycle → pure Betti-number LB is dead.

Reuses the boundary machinery from skmh_probe_betti_2026-04-20.py.
"""
from __future__ import annotations
import importlib.util
import itertools
import os
import sys
import time
from collections import defaultdict
import numpy as np

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_CLAUDE = os.path.normpath(os.path.join(_HERE, "..", "..", "..", "claude"))

spec = importlib.util.spec_from_file_location(
    "probe_a",
    os.path.join(_CLAUDE,
                 "probe_sk_hamming1_empty_discriminator_2026-04-17.py"))
probe_a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe_a)
enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart


def M_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def _partitions(total, n, caps):
    if n == 0:
        if total == 0:
            yield ()
        return
    for d0 in range(min(caps[0], total) + 1):
        for tail in _partitions(total - d0, n - 1, caps[1:]):
            yield (d0,) + tail


def enumerate_cells_up_to(ms, max_dim):
    n = len(ms)
    for total_dim in range(max_dim + 1):
        caps = [m - 1 for m in ms]
        for dvec in _partitions(total_dim, n, caps):
            face_sets = [list(itertools.combinations(range(ms[i]),
                                                     dvec[i] + 1))
                         for i in range(n)]
            for combo in itertools.product(*face_sets):
                yield total_dim, combo


def cell_in_ng(cell, cycle_set):
    for v in itertools.product(*cell):
        if v in cycle_set:
            return False
    return True


def boundary(cell):
    out = defaultdict(int)
    offset = 0
    for i, F in enumerate(cell):
        d = len(F) - 1
        if d == 0:
            continue
        for j, _ in enumerate(F):
            F_removed = F[:j] + F[j + 1:]
            if len(F_removed) == 0:
                continue
            new_cell = cell[:i] + (F_removed,) + cell[i + 1:]
            sign = ((-1) ** offset) * ((-1) ** j)
            out[new_cell] += sign
        offset += d
    return dict(out)


def full_betti(ms, cycle, max_dim=None):
    """Compute Betti numbers of induced subcomplex NG(C) through max_dim.

    If max_dim is None, use dim X(ms) = Σ(m_i-1).
    """
    ambient_dim = sum(m - 1 for m in ms)
    if max_dim is None:
        max_dim = ambient_dim
    cycle_set = set(tuple(c) for c in cycle)
    cells_by_dim = {k: [] for k in range(max_dim + 1)}
    cell_index = {}
    t0 = time.time()
    for dim, cell in enumerate_cells_up_to(ms, max_dim):
        if not cell_in_ng(cell, cycle_set):
            continue
        idx = len(cells_by_dim[dim])
        cells_by_dim[dim].append(cell)
        cell_index[cell] = (dim, idx)
    t_enum = time.time() - t0
    counts = {k: len(cells_by_dim[k]) for k in range(max_dim + 1)}

    ranks = {0: 0}
    t_rank = {}
    for k in range(1, max_dim + 1):
        rows = counts[k - 1]
        cols = counts[k]
        if cols == 0 or rows == 0:
            ranks[k] = 0
            t_rank[k] = 0.0
            continue
        M = np.zeros((rows, cols), dtype=np.int64)
        for j, cell in enumerate(cells_by_dim[k]):
            bd = boundary(cell)
            for b_cell, coef in bd.items():
                if b_cell in cell_index:
                    d_b, idx_b = cell_index[b_cell]
                    if d_b == k - 1:
                        M[idx_b, j] += coef
        tr = time.time()
        ranks[k] = int(np.linalg.matrix_rank(M.astype(np.float64)))
        t_rank[k] = round(time.time() - tr, 2)

    betti = {}
    for k in range(max_dim + 1):
        rk_in = ranks.get(k, 0)
        rk_out = ranks.get(k + 1, 0)
        betti[k] = counts[k] - rk_in - rk_out

    return {
        "ms": tuple(ms),
        "ambient_dim": ambient_dim,
        "max_dim_computed": max_dim,
        "cell_counts": counts,
        "boundary_ranks": ranks,
        "betti": betti,
        "enum_seconds": round(t_enum, 3),
        "rank_seconds": t_rank,
    }


def run(ms, n, cycle, cycle_idx, label=""):
    ambient_dim = sum(m - 1 for m in ms)
    # Cap max_dim to keep runtime reasonable. Through full ambient dim
    # at n=5 is fine; at n≥6 we cap at 4 or 5 and note it.
    if ambient_dim <= 6:
        max_dim = ambient_dim
    elif ambient_dim <= 9:
        max_dim = 5
    else:
        max_dim = 4
    t0 = time.time()
    res = full_betti(ms, cycle, max_dim=max_dim)
    dt = time.time() - t0
    betti = res["betti"]
    nonzero_k = [k for k in betti if k >= 1 and betti[k] > 0]
    print(f"[E3{label}] cycle {cycle_idx} L={len(cycle)} "
          f"betti={betti} nonzero_k≥1={nonzero_k} "
          f"({dt:.2f}s total, enum={res['enum_seconds']}s)")
    return res, nonzero_k


def main():
    prod_ms = [
        (5, (2, 2, 2, 2, 2), 32),
        (5, (2, 2, 2, 2, 3), 48),
        (5, (2, 2, 2, 3, 3), 72),
        (5, (2, 2, 3, 3, 3), 108),  # super-threshold at n=5 (>96)
        (5, (2, 2, 2, 3, 4), 96),   # at-threshold
        (6, (2, 2, 2, 2, 3, 3), 144),
        (6, (2, 2, 2, 3, 3, 3), 216),
        (6, (2, 2, 2, 3, 3, 4), 288),  # at-threshold
    ]
    summary = []
    for n, ms, prod in prod_ms:
        threshold = M_n_sharp(n)
        tag = ("sub" if prod < threshold
               else "at" if prod == threshold else "super")
        print(f"\n[E3] === ms={ms} n={n} ∏={prod} (M_n*={threshold}, {tag}) ===")
        L_max = 3 * n + 6
        cycles = enumerate_cycles_multistart(
            ms, n, L_min=6, L_max=L_max,
            time_budget=30.0, max_cycles=4)
        print(f"[E3] enumerated {len(cycles)} cycles")
        for i, (cyc, movers, det) in enumerate(cycles):
            res, nonzero_k = run(ms, n, cyc, i,
                                 label=f" {ms} {tag}")
            summary.append({
                "n": n, "ms": ms, "prod": prod, "tag": tag,
                "cycle_idx": i, "L": len(cyc),
                "betti": res["betti"],
                "nonzero_k_ge_1": nonzero_k,
                "max_dim_computed": res["max_dim_computed"],
                "cell_counts": res["cell_counts"],
            })
    print("\n[E3] ===== SUMMARY =====")
    print(f"{'ms':<18} {'tag':<5} {'L':>3} {'nz_k':<12} {'betti':<40}")
    for s in summary:
        print(f"{str(s['ms']):<18} {s['tag']:<5} {s['L']:>3} "
              f"{str(s['nonzero_k_ge_1']):<12} "
              f"{str({k: v for k, v in s['betti'].items() if v != 0}):<40}")
    # Count rule:
    any_nz = sum(1 for s in summary if s["nonzero_k_ge_1"])
    print(f"\n[E3] cycles with SOME β_k>0 (k≥1): {any_nz}/{len(summary)}")
    subs = [s for s in summary if s["tag"] == "sub"]
    subs_nz = sum(1 for s in subs if s["nonzero_k_ge_1"])
    print(f"[E3] sub-threshold cycles with SOME β_k>0: {subs_nz}/{len(subs)}")
    return summary


if __name__ == "__main__":
    main()
