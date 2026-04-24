#!/usr/bin/env python3
"""Fit the bad-side rank by an additive local-context model.

Model:
    rank(c) ~= bias + sum_i w_i(C_i(c))

where C_i(c) is the radius-1 local context at processor i.

This tests whether the global descent certificate is representable as a
distributed additive code over local observations.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict

import numpy as np


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


def fit_family(label: str, ms, fs) -> str:
    result = verify_system(ms, fs)
    if not result.get("valid"):
        raise ValueError(f"{label} is not valid")
    good = set(result["good_configs"])
    rank, _ = rank_bad_configs(ms, fs, good)
    bad = [cfg for cfg in all_configs(ms) if cfg not in good]
    n = len(ms)

    vocab = [dict() for _ in range(n)]
    for proc in range(n):
        seen = sorted({(cfg[(proc - 1) % n], cfg[proc], cfg[(proc + 1) % n]) for cfg in bad})
        vocab[proc] = {ctx: idx for idx, ctx in enumerate(seen)}

    offsets = []
    cur = 1
    for proc in range(n):
        offsets.append(cur)
        cur += len(vocab[proc])

    X = np.zeros((len(bad), cur), dtype=np.float64)
    y = np.zeros(len(bad), dtype=np.float64)
    X[:, 0] = 1.0

    for row, cfg in enumerate(bad):
        y[row] = rank[cfg]
        for proc in range(n):
            ctx = (cfg[(proc - 1) % n], cfg[proc], cfg[(proc + 1) % n])
            X[row, offsets[proc] + vocab[proc][ctx]] = 1.0

    coeffs, *_ = np.linalg.lstsq(X, y, rcond=None)
    pred = X @ coeffs
    resid = y - pred
    rmse = float(np.sqrt(np.mean(resid ** 2)))
    mae = float(np.mean(np.abs(resid)))
    max_abs = float(np.max(np.abs(resid)))
    ss_res = float(np.sum(resid ** 2))
    ss_tot = float(np.sum((y - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot

    rounded = np.rint(pred)
    exact_rounded = int(np.sum(rounded == y))

    top_contexts = []
    for proc in range(n):
        inv = {idx: ctx for ctx, idx in vocab[proc].items()}
        proc_coeffs = []
        for idx in range(len(vocab[proc])):
            proc_coeffs.append((coeffs[offsets[proc] + idx], inv[idx]))
        proc_coeffs.sort(key=lambda item: abs(item[0]), reverse=True)
        top_contexts.append((proc, proc_coeffs[:5]))

    lines = []
    lines.append(label)
    lines.append(f"  bad_configs={len(bad)}, features={cur}")
    lines.append(f"  additive rank fit R^2 = {r2:.6f}")
    lines.append(f"  RMSE = {rmse:.6f}")
    lines.append(f"  MAE = {mae:.6f}")
    lines.append(f"  max_abs_error = {max_abs:.6f}")
    lines.append(f"  exact after rounding = {exact_rounded}/{len(bad)}")
    lines.append("")
    lines.append("  top local coefficients by processor:")
    for proc, entries in top_contexts:
        formatted = ", ".join(f"{ctx}:{value:.3f}" for value, ctx in entries)
        lines.append(f"  - proc {proc}: {formatted}")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3", "all"], default="all")
    parser.add_argument("--n", type=int, default=9)
    args = parser.parse_args()

    families = ["cup2", "sol3"] if args.family == "all" else [args.family]
    outputs = []
    for family in families:
        label, ms, fs = build_family(family, args.n)
        outputs.append(fit_family(label, ms, fs))
    print("\n\n".join(outputs))


if __name__ == "__main__":
    main()
