#!/usr/bin/env python3
"""
Path A L4 short-arc alternate-site probe.

On the Q2c failure set from `path_a_L4_restricted_repair_probe.py`, report
where the full Path A witness search lands.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


UNIV = load_module(
    "path_a_universal",
    ROOT / "probes/branch_b_bypass/path_a_witness_search_universal.py",
)
WITNESS = load_module(
    "path_a_witness",
    ROOT / "probes/branch_b_bypass/path_a_witness_search.py",
)
REPAIR = load_module(
    "path_a_repair",
    ROOT / "probes/branch_b_bypass/path_a_L4_restricted_repair_probe.py",
)

ORIGINAL_LABELS = {"n9 pivot alt", "n11 pivot 3bin"}
EXTENDED_FAMILIES = [
    UNIV.Family(7, "n7 3-bin cluster", (2, 3, 2, 3, 2, 3, 3)),
    UNIV.Family(9, "n9 4-bin alt", (2, 3, 2, 3, 2, 3, 2, 3, 3)),
    UNIV.Family(11, "n11 4-bin alt", (2, 3, 2, 3, 2, 3, 2, 3, 3, 3, 3)),
    UNIV.Family(13, "n13 5-bin alt", (2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 3, 3)),
]


def family_list(kind: str):
    if kind == "original":
        return [fam for fam in UNIV.FAMILIES if fam.label in ORIGINAL_LABELS]
    if kind == "extended":
        base = [fam for fam in UNIV.FAMILIES if fam.label in ORIGINAL_LABELS]
        return base + EXTENDED_FAMILIES
    raise ValueError(kind)


def site_role(ms: tuple[int, ...], i: int) -> str:
    if ms[i] == 2:
        return "binary"
    left_bin = ms[(i - 1) % len(ms)] == 2
    right_bin = ms[(i + 1) % len(ms)] == 2
    if left_bin and right_bin:
        return "sandwiched-ternary"
    if left_bin or right_bin:
        return "binary-adjacent-ternary"
    return "deep-ternary"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--family-set",
        choices=["original", "extended"],
        default="original",
        help="Which pivot-family test set to run.",
    )
    args = parser.parse_args()

    print("=" * 70)
    print(f"Path A L4 short-arc alternate-site probe ({args.family_set})")
    print("=" * 70)
    print()

    for fam in family_list(args.family_set):

        population_count = 0
        candidate_count = 0
        q2c_count = 0
        site_counter = Counter()
        option_counter = Counter()
        role_counter = Counter()
        examples = []

        for word in UNIV.path_a_population(fam):
            population_count += 1
            if not REPAIR.L4.candidate_sites(fam.ms):
                continue
            candidate_count += 1
            has_linear, has_wrap, _ = REPAIR.cycle_status(word, fam)
            if has_linear or has_wrap:
                continue
            q2c_count += 1
            hits = WITNESS.search_cycle(word, fam.ms, fam.n)
            seen_sites = set()
            for i, a1, a2, k2, option in hits:
                site_counter[i] += 1
                option_counter[option] += 1
                if i not in seen_sites:
                    role_counter[site_role(fam.ms, i)] += 1
                    seen_sites.add(i)
            if len(examples) < 5:
                examples.append((list(word), hits[:10]))

        print(f"### {fam.label}")
        print(f"  path-a population: {population_count}")
        print(f"  candidate cycles (has sandwiched ternary): {candidate_count}")
        print(f"  Q2c cycles: {q2c_count}")
        print(f"  witness site histogram: {dict(site_counter)}")
        print(f"  witness option histogram: {dict(option_counter)}")
        print(f"  per-cycle site-role coverage: {dict(role_counter)}")
        for word, hits in examples:
            print(f"  example word={word}")
            print(f"  example hits={hits}")
        print()

    print("=" * 70)


if __name__ == "__main__":
    main()
