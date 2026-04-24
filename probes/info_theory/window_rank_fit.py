#!/usr/bin/env python3
"""Fit bad-side rank by additive overlapping state windows.

Model:
    rank(c) ~= bias + sum_i g_i(c[i], c[i+1], ..., c[i+w-1])

with cyclic indexing. This is a richer factorization than one-site local
contexts and tests whether the global descent code has low-order window
structure.
"""

from __future__ import annotations

import argparse
import os
import sys

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import lsqr


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, verify_system  # type: ignore

from cycle_info_metrics import sol3_v1_rules
from rank_info_metrics import rank_bad_configs


def build_family(name: str, n: int):
    if name == "cup2":
        ms, fs = build_cup2_system(n)
        return f"CUP-2(n={n})", ms, fs
    if name == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
        return f"Sol3(n={n})", ms, fs
    raise ValueError(f"unknown family {name}")


def fit_family(label: str, ms, fs, width: int) -> str:
    result = verify_system(ms, fs)
    if not result.get("valid"):
        raise ValueError(f"{label} is not valid")
    good = set(result["good_configs"])
    rank, _ = rank_bad_configs(ms, fs, good)
    bad = [cfg for cfg in all_configs(ms) if cfg not in good]
    n = len(ms)

    vocab = [dict() for _ in range(n)]
    for start in range(n):
        seen = sorted(
            {
                tuple(cfg[(start + j) % n] for j in range(width))
                for cfg in bad
            }
        )
        vocab[start] = {window: idx for idx, window in enumerate(seen)}

    offsets = []
    cur = 1
    for start in range(n):
        offsets.append(cur)
        cur += len(vocab[start])

    y = np.zeros(len(bad), dtype=np.float64)
    rows: list[int] = []
    cols: list[int] = []
    data: list[float] = []

    for row, cfg in enumerate(bad):
        y[row] = rank[cfg]
        rows.append(row)
        cols.append(0)
        data.append(1.0)
        for start in range(n):
            window = tuple(cfg[(start + j) % n] for j in range(width))
            rows.append(row)
            cols.append(offsets[start] + vocab[start][window])
            data.append(1.0)

    X = csr_matrix((data, (rows, cols)), shape=(len(bad), cur), dtype=np.float64)
    coeffs = lsqr(X, y, atol=1e-10, btol=1e-10)[0]
    pred = X @ coeffs
    resid = y - pred
    rmse = float(np.sqrt(np.mean(resid ** 2)))
    mae = float(np.mean(np.abs(resid)))
    max_abs = float(np.max(np.abs(resid)))
    ss_res = float(np.sum(resid ** 2))
    ss_tot = float(np.sum((y - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot
    exact_rounded = int(np.sum(np.rint(pred) == y))

    return "\n".join(
        [
            f"{label}, window_width={width}",
            f"  bad_configs={len(bad)}, features={cur}",
            f"  additive window fit R^2 = {r2:.6f}",
            f"  RMSE = {rmse:.6f}",
            f"  MAE = {mae:.6f}",
            f"  max_abs_error = {max_abs:.6f}",
            f"  exact after rounding = {exact_rounded}/{len(bad)}",
        ]
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3", "all"], default="all")
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--width", type=int, default=4)
    args = parser.parse_args()

    families = ["cup2", "sol3"] if args.family == "all" else [args.family]
    outputs = []
    for family in families:
        label, ms, fs = build_family(family, args.n)
        outputs.append(fit_family(label, ms, fs, args.width))
    print("\n\n".join(outputs))


if __name__ == "__main__":
    main()
