#!/usr/bin/env python3
"""Table-level information metrics for self-stabilizing witnesses.

The transition table at processor i marks a subset P_i of local contexts
as privileged. Each privileged context lifts to a cylinder in global
configuration space of size product(ms) / L_i, where L_i is the local
alphabet size. These cylinders must cover the full state space (liveness),
and their bad-config part must admit an acyclic orientation (convergence).

This script measures the coarse cover side of that story:
- privileged entry counts per processor
- the cylinder-cover lower bound sum_i |P_i| / L_i >= 1
- distribution of privileged multiplicity over all global configurations
- the size of the single-privileged set versus the actual good set
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from functools import reduce
from operator import mul


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, privileged_set, verify_system  # type: ignore

from cycle_info_metrics import sol3_v1_rules


def product(values: list[int]) -> int:
    return reduce(mul, values, 1)


def build_family(name: str, n: int) -> tuple[str, list[int], list]:
    if name == "cup2":
        ms, fs = build_cup2_system(n)
        return f"CUP-2(n={n})", ms, fs
    if name == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
        return f"Sol3(n={n})", ms, fs
    raise ValueError(f"unknown family {name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3", "all"], default="all")
    parser.add_argument("--n", type=int, default=9)
    args = parser.parse_args()

    families = ["cup2", "sol3"] if args.family == "all" else [args.family]
    outputs: list[str] = []

    for family in families:
        label, ms, fs = build_family(family, args.n)
        result = verify_system(ms, fs)
        if not result.get("valid"):
            raise ValueError(f"{label} is not valid")

        cfgs = list(all_configs(ms))
        good = set(result["good_configs"])
        n = len(ms)

        per_proc: list[tuple[int, int, float]] = []
        cover_lb = 0.0
        for proc in range(n):
            local_size = ms[(proc - 1) % n] * ms[proc] * ms[(proc + 1) % n]
            priv_count = 0
            for left in range(ms[(proc - 1) % n]):
                for self_ in range(ms[proc]):
                    for right in range(ms[(proc + 1) % n]):
                        if not fs[proc](left, self_, right) == self_:
                            priv_count += 1
            frac = priv_count / local_size
            per_proc.append((priv_count, local_size, frac))
            cover_lb += frac

        priv_mult = Counter()
        single_priv_total = 0
        single_priv_good = 0
        single_priv_bad = 0
        for cfg in cfgs:
            privs = privileged_set(cfg, fs, ms)
            k = len(privs)
            priv_mult[k] += 1
            if k == 1:
                single_priv_total += 1
                if cfg in good:
                    single_priv_good += 1
                else:
                    single_priv_bad += 1

        lines: list[str] = []
        lines.append(label)
        lines.append(f"  n={n}, product={product(ms)}, total_configs={len(cfgs)}")
        lines.append(f"  good_set={len(good)}, cycle_len={result['cycle_length']}")
        lines.append("")
        lines.append("  proc  m_i  L_i  |P_i|  |P_i|/L_i")
        lines.append("  ----  ---  ---  -----  ---------")
        for proc, (priv_count, local_size, frac) in enumerate(per_proc):
            lines.append(
                f"  {proc:>4}  {ms[proc]:>3}  {local_size:>3}  {priv_count:>5}  {frac:>9.4f}"
            )
        lines.append("")
        lines.append(f"  cylinder-cover lower bound sum_i |P_i|/L_i = {cover_lb:.6f}")
        lines.append(
            f"  single-privileged configs: total={single_priv_total}, good={single_priv_good}, bad={single_priv_bad}"
        )
        lines.append("  privileged multiplicity distribution:")
        for k in sorted(priv_mult):
            lines.append(f"  - {k} privileged: {priv_mult[k]}")
        outputs.append("\n".join(lines))

    print("\n\n".join(outputs))


if __name__ == "__main__":
    main()
