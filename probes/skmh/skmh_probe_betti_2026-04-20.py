#!/usr/bin/env python3
"""SKMH Exploration 2 — Betti numbers of NG(C) as product-of-simplices subcomplex.

Model:
  X(ms) = ∏_{i=0..n-1} Δ^{m_i - 1}  (product of simplices, 0-cells = Config(ms))
  Cells: tuples (F_0, ..., F_{n-1}) with each F_i a nonempty subset of Fin(m_i).
         dim = Σ(|F_i| - 1).
  NG(C) = full subcomplex on vertices Config \\ Cycle(C).
          Cell (F_0, ..., F_{n-1}) in NG iff every product-vertex ∏ f_i ∉ Cycle.

Boundary (cellular):
  ∂(F_0, ..., F_{n-1}) = Σ_i (-1)^{Σ_{j<i} (|F_j|-1)} · (F_0, ..., ∂F_i, ..., F_{n-1})
  where ∂F_i = Σ_j (-1)^j (F_i \\ {v_j})  for F_i sorted as (v_0 < ... < v_d).

Strategy for Exploration 2:
  1. Pull one fair simple cycle at (n=5, ms=(2,2,2,3,4)) via the repo enumerator.
  2. Build NG subcomplex cells through dim 3.
  3. Compute rank of ∂_1, ∂_2, ∂_3 over Q.
  4. Report β_0, β_1, β_2.

No optimization yet — direct approach. If n=5 runs cleanly scale to n=6,7,8.
"""
from __future__ import annotations
import importlib.util, itertools, json, os, sys, time
from collections import defaultdict
import numpy as np

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))
_CLAUDE = os.path.normpath(os.path.join(_HERE, "..", "..", "..", "claude"))

# --- Load cycle enumerator from existing probe ---
spec = importlib.util.spec_from_file_location(
    "probe_a",
    os.path.join(_CLAUDE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py"))
probe_a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe_a)
enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart


# ---------------- cell enumeration ----------------

def enumerate_cells_up_to(ms, max_dim):
    """Yield (F_0, ..., F_{n-1}) cells of X(ms) with dim ≤ max_dim.

    F_i is a sorted tuple of elements of range(m_i), nonempty.
    dim = sum(len(F_i) - 1).

    Emits cells in order of increasing dim.
    """
    n = len(ms)
    # For each dim-vector (d_0, ..., d_{n-1}) with sum ≤ max_dim, iterate.
    # Number of F_i with |F_i| = d_i+1 equals C(m_i, d_i+1).
    for total_dim in range(max_dim + 1):
        # partitions of total_dim into n nonneg with d_i ≤ m_i - 1
        for dvec in _partitions(total_dim, n, [m - 1 for m in ms]):
            face_sets = [list(itertools.combinations(range(ms[i]), dvec[i] + 1))
                         for i in range(n)]
            for combo in itertools.product(*face_sets):
                yield total_dim, combo


def _partitions(total, n, caps):
    """All tuples (d_0, ..., d_{n-1}) with d_i ≥ 0, d_i ≤ caps[i], Σ = total."""
    if n == 0:
        if total == 0:
            yield ()
        return
    for d0 in range(min(caps[0], total) + 1):
        for tail in _partitions(total - d0, n - 1, caps[1:]):
            yield (d0,) + tail


def cell_in_ng(cell, cycle_set):
    """A cell (F_0, ..., F_{n-1}) is in NG iff all product-vertices ∉ cycle."""
    for v in itertools.product(*cell):
        if v in cycle_set:
            return False
    return True


# ---------------- boundary operator ----------------

def cell_dim(cell):
    return sum(len(F) - 1 for F in cell)


def boundary(cell):
    """Return dict {boundary_cell: signed_int_coeff} for a single cell.

    Signs per tensor-product rule.
    """
    out = defaultdict(int)
    offset = 0
    for i, F in enumerate(cell):
        d = len(F) - 1
        if d == 0:
            offset += 0  # vertex factor has no simplicial boundary
            continue
        # simplicial boundary of F (as a d-simplex): remove each vertex with sign
        for j, _ in enumerate(F):
            F_removed = F[:j] + F[j + 1:]
            if len(F_removed) == 0:
                continue
            new_cell = cell[:i] + (F_removed,) + cell[i + 1:]
            sign = ((-1) ** offset) * ((-1) ** j)
            out[new_cell] += sign
        offset += d
    return dict(out)


# ---------------- Betti computation ----------------

def betti_numbers(ms, cycle, max_dim=3):
    """Return dict with per-dim cell counts in NG subcomplex and Betti numbers.

    Only computes β_k for k ≤ max_dim - 1 (needs ∂_{k+1}).
    """
    cycle_set = set(tuple(c) for c in cycle)
    # Enumerate NG cells by dim.
    cells_by_dim = {k: [] for k in range(max_dim + 1)}
    cell_index = {}  # cell -> (dim, idx)
    t0 = time.time()
    for dim, cell in enumerate_cells_up_to(ms, max_dim):
        if not cell_in_ng(cell, cycle_set):
            continue
        idx = len(cells_by_dim[dim])
        cells_by_dim[dim].append(cell)
        cell_index[cell] = (dim, idx)
    t_enum = time.time() - t0
    counts = {k: len(cells_by_dim[k]) for k in range(max_dim + 1)}

    # Build boundary matrices ∂_k : C_k -> C_{k-1} for k = 1..max_dim.
    # Use numpy dense for simplicity at small scales.
    ranks = {}
    matrices = {}
    for k in range(1, max_dim + 1):
        rows = counts[k - 1]
        cols = counts[k]
        if cols == 0 or rows == 0:
            ranks[k] = 0
            matrices[k] = (rows, cols, 0)
            continue
        M = np.zeros((rows, cols), dtype=np.int64)
        for j, cell in enumerate(cells_by_dim[k]):
            bd = boundary(cell)
            for b_cell, coef in bd.items():
                # b_cell must be in NG too (it's a face of an NG cell; NG is a
                # full subcomplex, so yes — but its dim could be 0 if the k-cell
                # had only one nontrivial factor, in which case we already have it).
                if b_cell in cell_index:
                    d_b, idx_b = cell_index[b_cell]
                    if d_b == k - 1:
                        M[idx_b, j] += coef
        # Rank over Q.
        ranks[k] = int(np.linalg.matrix_rank(M.astype(np.float64)))
        matrices[k] = (rows, cols, ranks[k])

    # β_0 = c_0 - rank ∂_1;  β_k = c_k - rank ∂_k - rank ∂_{k+1}  for k ≥ 1.
    betti = {}
    betti[0] = counts[0] - ranks.get(1, 0)
    for k in range(1, max_dim):
        betti[k] = counts[k] - ranks.get(k, 0) - ranks.get(k + 1, 0)

    return {
        "ms": tuple(ms),
        "cycle_length": len(cycle),
        "cell_counts": counts,
        "boundary_ranks": {k: matrices[k] for k in matrices},
        "betti": betti,
        "enum_seconds": round(t_enum, 3),
    }


# ---------------- driver ----------------

def M_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def run_probe(ms, n, L_min=6, L_max=None, max_cycles=4, label=""):
    if L_max is None:
        L_max = 3 * n + 4
    prod = 1
    for m in ms:
        prod *= m
    print(f"[SKMH E2{label}] ms={ms}, n={n}, ∏m_i={prod}, M_n*={M_n_sharp(n)}, X(ms) dim = {sum(m-1 for m in ms)}")
    t0 = time.time()
    cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                          time_budget=60.0, max_cycles=max_cycles)
    t_enum = time.time() - t0
    print(f"[SKMH E2{label}] enumerated {len(cycles)} cycle(s) in {t_enum:.2f}s")
    results = []
    for i, (cycle, movers, det) in enumerate(cycles):
        t0 = time.time()
        result = betti_numbers(ms, cycle, max_dim=3)
        t_betti = time.time() - t0
        result["movers"] = list(movers)
        result["subsharp"] = (prod < M_n_sharp(n))
        result["sharp"] = (prod == M_n_sharp(n))
        result["probe_seconds"] = round(t_betti, 3)
        results.append(result)
        print(f"[SKMH E2{label} cycle {i}] L={len(cycle)} subsharp={result['subsharp']} "
              f"betti={result['betti']} cells={result['cell_counts']} ({t_betti:.2f}s)")
    return results


def main():
    all_results = {}
    # Sub-threshold n=5 multisets (product < 96).
    for ms in [(2, 2, 2, 2, 3), (2, 2, 2, 3, 3), (2, 2, 2, 2, 2)]:
        lab = f" n=5 {ms}"
        all_results[str(ms)] = run_probe(ms, 5, L_min=6, L_max=18, max_cycles=3, label=lab)
    # At-threshold reference (already ran; rerun for single record).
    all_results[str((2, 2, 2, 3, 4))] = run_probe((2, 2, 2, 3, 4), 5,
                                                   L_min=10, L_max=22, max_cycles=2,
                                                   label=" n=5 (2,2,2,3,4) ref")
    # Optional n=6 sub-threshold sample.
    all_results[str((2, 2, 2, 3, 3, 3))] = run_probe((2, 2, 2, 3, 3, 3), 6,
                                                      L_min=8, L_max=22, max_cycles=2,
                                                      label=" n=6 sub")
    # Dump JSON to TMPDIR.
    tmpdir = os.environ.get("TMPDIR", "/tmp")
    out_path = os.path.join(tmpdir, "skmh_e2_results.json")
    def _convert(x):
        if isinstance(x, dict):
            return {str(k): _convert(v) for k, v in x.items()}
        if isinstance(x, (list, tuple)):
            return [_convert(v) for v in x]
        return x
    with open(out_path, "w") as f:
        json.dump(_convert(all_results), f, indent=2)
    print(f"[SKMH E2] wrote {out_path}")
    return all_results


if __name__ == "__main__":
    main()
