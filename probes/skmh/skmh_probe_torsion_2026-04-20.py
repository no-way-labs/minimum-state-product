#!/usr/bin/env python3
"""SKMH Exploration 7 — integer homology torsion of NG(C).

E2-E6 computed Betti numbers over Q (via numpy float rank). But
H_k(NG; Z) can have TORSION summands Z/m even when Betti = 0. Torsion
is ms-sensitive in a way that ranks are not.

Probe: for each boundary matrix d_k, compute
  - rank over Q
  - rank over Z/p for each prime p in {2, 3, 5, 7}

Torsion detection: H_{k-1} has p-torsion iff
  rank_Q(d_k) > rank_{Z/p}(d_k).

If torsion structure discriminates sub- from at-threshold, or shows
ms-dependent patterns, this is the invariant.

Output: full modular-rank table for each cycle, and any detected
torsion summands in H_k(NG; Z).
"""
from __future__ import annotations
import importlib.util
import itertools
import os
import sys
import time
from collections import defaultdict
import math
import numpy as np

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_CLAUDE = os.path.normpath(
    os.path.join(_HERE, "..", "..", "..", "claude"))
spec = importlib.util.spec_from_file_location(
    "probe_a",
    os.path.join(
        _CLAUDE,
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
            face_sets = [
                list(itertools.combinations(range(ms[i]), dvec[i] + 1))
                for i in range(n)
            ]
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


# ----- modular rank -----

def rank_mod_p(M, p):
    """Gaussian elimination mod p.  M is numpy int array."""
    if M.size == 0:
        return 0
    A = M.copy() % p
    r = A.shape[0]
    c = A.shape[1]
    rank = 0
    col = 0
    row = 0
    while row < r and col < c:
        # find pivot
        pivot = -1
        for i in range(row, r):
            if A[i, col] % p != 0:
                pivot = i
                break
        if pivot < 0:
            col += 1
            continue
        if pivot != row:
            A[[row, pivot], :] = A[[pivot, row], :]
        # normalize
        inv = pow(int(A[row, col]), -1, p)
        A[row, :] = (A[row, :] * inv) % p
        # eliminate other rows
        for i in range(r):
            if i != row and A[i, col] % p != 0:
                A[i, :] = (A[i, :] - A[i, col] * A[row, :]) % p
        rank += 1
        row += 1
        col += 1
    return rank


def build_boundary_matrix(cells_by_dim, cell_index, k):
    """Return int matrix for ∂_k : C_k -> C_{k-1}."""
    rows = len(cells_by_dim[k - 1])
    cols = len(cells_by_dim[k])
    if rows == 0 or cols == 0:
        return np.zeros((rows, cols), dtype=np.int64)
    M = np.zeros((rows, cols), dtype=np.int64)
    for j, cell in enumerate(cells_by_dim[k]):
        bd = boundary(cell)
        for b_cell, coef in bd.items():
            if b_cell in cell_index:
                d_b, idx_b = cell_index[b_cell]
                if d_b == k - 1:
                    M[idx_b, j] += coef
    return M


def integer_homology(ms, cycle, max_dim=None, primes=(2, 3, 5, 7)):
    """Compute modular ranks of boundary matrices to detect torsion."""
    ambient = sum(m - 1 for m in ms)
    if max_dim is None:
        max_dim = ambient
    cycle_set = set(tuple(c) for c in cycle)
    cells_by_dim = {k: [] for k in range(max_dim + 1)}
    cell_index = {}
    for dim, cell in enumerate_cells_up_to(ms, max_dim):
        if not cell_in_ng(cell, cycle_set):
            continue
        idx = len(cells_by_dim[dim])
        cells_by_dim[dim].append(cell)
        cell_index[cell] = (dim, idx)
    counts = {k: len(cells_by_dim[k]) for k in range(max_dim + 1)}

    mat_by_k = {}
    rank_q = {0: 0}
    rank_mod = {0: {p: 0 for p in primes}}
    for k in range(1, max_dim + 1):
        M = build_boundary_matrix(cells_by_dim, cell_index, k)
        mat_by_k[k] = M
        if M.size == 0:
            rank_q[k] = 0
            rank_mod[k] = {p: 0 for p in primes}
            continue
        rank_q[k] = int(np.linalg.matrix_rank(M.astype(np.float64)))
        rank_mod[k] = {p: rank_mod_p(M, p) for p in primes}

    # Torsion: H_{k-1} has p-torsion iff rank_Q(d_k) > rank_{Z/p}(d_k).
    # Amount of p-torsion = rank_Q(d_k) - rank_{Z/p}(d_k).
    # Also p-torsion in H_{k-1} from cokernel of d_k modular vs Q.
    # Standard formula: dim H_k(C; Z/p) - dim H_k(C; Q) =
    #   p-torsion in H_k + p-torsion in H_{k-1}.

    # Betti over Q:
    betti_q = {}
    for k in range(max_dim + 1):
        rk_in = rank_q.get(k, 0)
        rk_out = rank_q.get(k + 1, 0)
        betti_q[k] = counts[k] - rk_in - rk_out

    # Betti over Z/p:
    betti_p = {}
    for p in primes:
        betti_p[p] = {}
        for k in range(max_dim + 1):
            rk_in = rank_mod.get(k, {p: 0}).get(p, 0)
            rk_out = rank_mod.get(k + 1, {p: 0}).get(p, 0)
            betti_p[p][k] = counts[k] - rk_in - rk_out

    # Extra p-torsion detector:
    p_torsion_signature = {}
    for p in primes:
        sig = {}
        for k in range(max_dim + 1):
            diff = betti_p[p][k] - betti_q[k]
            if diff != 0:
                sig[k] = diff
        p_torsion_signature[p] = sig

    return {
        "ms": tuple(ms),
        "cycle_len": len(cycle),
        "ambient_dim": ambient,
        "max_dim": max_dim,
        "cell_counts": counts,
        "rank_q": rank_q,
        "rank_mod": rank_mod,
        "betti_q": betti_q,
        "betti_mod_p": betti_p,
        "p_torsion_signature": p_torsion_signature,
    }


def run_multiset(n, ms, prod, max_cycles=2):
    threshold = M_n_sharp(n)
    tag = ("sub" if prod < threshold
           else "at" if prod == threshold else "super")
    L_max = 3 * n + 6
    cycles = enumerate_cycles_multistart(
        ms, n, L_min=6, L_max=L_max,
        time_budget=30.0, max_cycles=max_cycles)
    results = []
    for i, (cyc, movers, det) in enumerate(cycles):
        ambient = sum(m - 1 for m in ms)
        if ambient <= 6:
            max_dim = ambient
        elif ambient <= 9:
            max_dim = 5
        else:
            max_dim = 4
        t0 = time.time()
        res = integer_homology(ms, cyc, max_dim=max_dim)
        dt = time.time() - t0
        tor = res["p_torsion_signature"]
        # trim noise: only report primes with any torsion detection
        tor_nonzero = {p: sig for p, sig in tor.items() if sig}
        print(f"[E7] ms={ms} L={len(cyc)} tag={tag} cycle{i} "
              f"({dt:.1f}s)")
        print(f"     betti_Q = {res['betti_q']}")
        if tor_nonzero:
            print(f"     TORSION DETECTED: {tor_nonzero}")
        else:
            print(f"     no p-torsion (p in 2,3,5,7) at any dim")
        results.append({
            "n": n, "ms": ms, "prod": prod, "tag": tag,
            "L": len(cyc), "betti_q": res["betti_q"],
            "tor": tor_nonzero, "cell_counts": res["cell_counts"]
        })
    return results


def main():
    prod_ms = [
        (5, (2, 2, 2, 2, 2), 32),
        (5, (2, 2, 2, 2, 3), 48),
        (5, (2, 2, 2, 3, 3), 72),
        (5, (2, 2, 3, 3, 3), 108),
        (5, (2, 2, 2, 3, 4), 96),
        (5, (3, 3, 3, 3, 3), 243),
        (6, (2, 2, 2, 2, 3, 3), 144),
        (6, (2, 2, 2, 3, 3, 3), 216),
        (6, (2, 2, 2, 3, 3, 4), 288),
    ]
    all_results = []
    for n, ms, prod in prod_ms:
        print(f"\n[E7] === ms={ms} n={n} ∏={prod} "
              f"(M_n*={M_n_sharp(n)}) ===")
        res = run_multiset(n, ms, prod, max_cycles=2)
        all_results.extend(res)
    print("\n[E7] ===== SUMMARY =====")
    any_tor = [r for r in all_results if r["tor"]]
    print(f"Cycles with ANY p-torsion (p in 2,3,5,7): "
          f"{len(any_tor)}/{len(all_results)}")
    for r in any_tor:
        print(f"  {r['ms']} L={r['L']} tag={r['tag']} tor={r['tor']}")
    print("\nCycles WITHOUT p-torsion:")
    no_tor = [r for r in all_results if not r["tor"]]
    for r in no_tor:
        print(f"  {r['ms']} L={r['L']} tag={r['tag']}")


if __name__ == "__main__":
    main()
