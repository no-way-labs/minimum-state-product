#!/usr/bin/env python3
"""Null-model capacity check for additive window codes.

Fits the same additive window model used for bad-side rank to randomized targets
on the same bad-config set. This distinguishes genuine structure from a merely
too-expressive linear model.
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


def build_design(ms, good, width):
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

    rows = []
    cols = []
    data = []
    for row, cfg in enumerate(bad):
        rows.append(row)
        cols.append(0)
        data.append(1.0)
        for start in range(n):
            window = tuple(cfg[(start + j) % n] for j in range(width))
            rows.append(row)
            cols.append(offsets[start] + vocab[start][window])
            data.append(1.0)

    X = csr_matrix((data, (rows, cols)), shape=(len(bad), cur), dtype=np.float64)
    return bad, X


def fit_score(X, y):
    coeffs = lsqr(X, y, atol=1e-10, btol=1e-10)[0]
    pred = X @ coeffs
    resid = y - pred
    rmse = float(np.sqrt(np.mean(resid ** 2)))
    ss_res = float(np.sum(resid ** 2))
    ss_tot = float(np.sum((y - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot
    return r2, rmse, float(np.max(np.abs(resid)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--width", type=int, required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    rank, _ = rank_bad_configs(ms, fs, good)
    bad, X = build_design(ms, good, args.width)
    y_rank = np.array([rank[cfg] for cfg in bad], dtype=np.float64)
    y_perm = rng.permutation(y_rank)
    y_rand = rng.normal(size=len(y_rank))

    print(label, f"width={args.width}")
    print("  actual :", fit_score(X, y_rank))
    print("  perm   :", fit_score(X, y_perm))
    print("  random :", fit_score(X, y_rand))


if __name__ == "__main__":
    main()
