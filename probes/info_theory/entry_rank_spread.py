#!/usr/bin/env python3
"""Measure bad-edge rank spread inside each privileged local entry.

For each bad transition edge c --(i, local context)--> c', the label
e = (i, C_i(c)) is the only local information available to processor i.
This script asks how much global rank variation one such label must handle.

Key quantities per label e:
- number of bad edges using e
- number of distinct source ranks
- number of distinct successor ranks
- entropy of source rank and successor rank conditioned on e
- rank-drop range and whether the drop is constant on that label
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict
from statistics import mean


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, apply_move, privileged_set, verify_system  # type: ignore

from cycle_info_metrics import entropy, sol3_v1_rules
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


def summarize_family(label: str, ms, fs) -> str:
    result = verify_system(ms, fs)
    if not result.get("valid"):
        raise ValueError(f"{label} is not valid")
    good = set(result["good_configs"])
    rank, _ = rank_bad_configs(ms, fs, good)
    bad = [cfg for cfg in all_configs(ms) if cfg not in good]

    by_label = defaultdict(list)
    for cfg in bad:
        for proc in privileged_set(cfg, fs, ms):
            nxt = apply_move(cfg, proc, fs, ms)
            if nxt in good:
                succ_rank = -1
            else:
                succ_rank = rank[nxt]
            context = (cfg[(proc - 1) % len(ms)], cfg[proc], cfg[(proc + 1) % len(ms)])
            by_label[(proc, context)].append((rank[cfg], succ_rank))

    source_entropies = []
    succ_entropies = []
    source_supports = []
    succ_supports = []
    edge_counts = []
    constant_drop = 0
    max_source_support = 0
    widest_drop = None

    for label_key, pairs in by_label.items():
        src = [a for a, _ in pairs]
        dst = [b for _, b in pairs]
        drops = [a - b for a, b in pairs]
        src_counter = Counter(src)
        dst_counter = Counter(dst)
        h_src = entropy(src_counter)
        h_dst = entropy(dst_counter)
        s_src = len(src_counter)
        s_dst = len(dst_counter)
        source_entropies.append(h_src)
        succ_entropies.append(h_dst)
        source_supports.append(s_src)
        succ_supports.append(s_dst)
        edge_counts.append(len(pairs))
        if len(set(drops)) == 1:
            constant_drop += 1
        if s_src > max_source_support:
            max_source_support = s_src
        drop_range = (min(drops), max(drops))
        width = drop_range[1] - drop_range[0]
        if widest_drop is None or width > widest_drop[0]:
            widest_drop = (width, label_key, len(pairs), s_src, h_src, drop_range)

    top_labels = sorted(
        by_label.items(),
        key=lambda item: (len({a for a, _ in item[1]}), entropy(Counter(a for a, _ in item[1])), len(item[1])),
        reverse=True,
    )[:10]

    lines = []
    lines.append(label)
    lines.append(f"  bad labels = {len(by_label)}")
    lines.append(f"  avg bad edges per label = {mean(edge_counts):.4f}")
    lines.append(f"  avg distinct source ranks per label = {mean(source_supports):.4f}")
    lines.append(f"  avg distinct successor ranks per label = {mean(succ_supports):.4f}")
    lines.append(f"  avg H(source rank | label) = {mean(source_entropies):.4f} bits")
    lines.append(f"  avg H(successor rank | label) = {mean(succ_entropies):.4f} bits")
    lines.append(f"  max distinct source ranks on one label = {max_source_support}")
    lines.append(f"  labels with constant rank drop = {constant_drop}/{len(by_label)}")
    if widest_drop is not None:
        width, label_key, count, src_supp, h_src, drop_range = widest_drop
        lines.append(
            f"  widest drop range = {drop_range} (width {width}) at label {label_key}, "
            f"edges={count}, src_support={src_supp}, Hsrc={h_src:.4f}"
        )
    lines.append("")
    lines.append("  top labels by source-rank spread:")
    for (proc, context), pairs in top_labels:
        src = [a for a, _ in pairs]
        dst = [b for _, b in pairs]
        drops = [a - b for a, b in pairs]
        lines.append(
            f"  - proc={proc}, ctx={context}, edges={len(pairs)}, "
            f"src_supp={len(set(src))}, dst_supp={len(set(dst))}, "
            f"Hsrc={entropy(Counter(src)):.4f}, Hdst={entropy(Counter(dst)):.4f}, "
            f"drop_range=({min(drops)},{max(drops)})"
        )
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
        outputs.append(summarize_family(label, ms, fs))
    print("\n\n".join(outputs))


if __name__ == "__main__":
    main()
