"""
Controller-complexity probe for explicit good cycles.

Given a mixed-radix state profile `ms` and a list of cycle codes, this script:

- decodes the cycle
- extracts the mover word
- computes repeated-shadow router capacity at each forgotten processor
- identifies critical repeated shadows
- optionally searches for deterministic controller quotients

Usage example:
  python3 controller_complexity_probe.py \
    --ms 2,2,2,3 \
    --codes 0,1,3,7,15,11,19,18,2,6,4,5,13,12,20,16
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from itertools import product
from typing import Dict, Iterable, List, Sequence, Tuple


Config = Tuple[int, ...]


def parse_nat_list(text: str) -> List[int]:
    return [int(x.strip()) for x in text.split(",") if x.strip()]


def decode_code(code: int, ms: Sequence[int]) -> Config:
    vals = []
    base = 1
    for m in ms:
        vals.append((code // base) % m)
        base *= m
    return tuple(vals)


def mover_word(cycle: Sequence[Config]) -> List[int]:
    n = len(cycle[0])
    movers: List[int] = []
    for a, b in zip(cycle, cycle[1:] + cycle[:1]):
        diffs = [j for j in range(n) if a[j] != b[j]]
        if len(diffs) != 1:
            raise ValueError(f"non-single mover between {a} and {b}: {diffs}")
        movers.append(diffs[0])
    return movers


def shadow(config: Config, forget: int) -> Config:
    return tuple(v for j, v in enumerate(config) if j != forget)


def controller_groups(cycle: Sequence[Config], forget: int) -> Dict[Config, List[Tuple[int, int, int]]]:
    moves = mover_word(cycle)
    groups: Dict[Config, List[Tuple[int, int, int]]] = defaultdict(list)
    for t, (cfg, mv) in enumerate(zip(cycle, moves)):
        groups[shadow(cfg, forget)].append((t, cfg[forget], mv))
    return groups


def router_capacity(groups: Dict[Config, List[Tuple[int, int, int]]]) -> int:
    return max(len({mv for _, _, mv in vals}) for vals in groups.values())


def critical_groups(
    groups: Dict[Config, List[Tuple[int, int, int]]], target_movers: Iterable[int] | None = None
) -> List[Tuple[Config, List[Tuple[int, int, int]]]]:
    out = []
    for sh, vals in groups.items():
        movers = {mv for _, _, mv in vals}
        if target_movers is None:
            if len(movers) >= 3:
                out.append((sh, vals))
        elif movers == set(target_movers):
            out.append((sh, vals))
    return out


def all_surjections(domain_size: int, codomain_size: int) -> List[Tuple[int, ...]]:
    vals = range(codomain_size)
    return [f for f in product(vals, repeat=domain_size) if set(f) == set(vals)]


def deterministic_under_merge(vals: Sequence[Tuple[int, int, int]], merge: Sequence[int]) -> bool:
    class_to_movers: Dict[int, set[int]] = defaultdict(set)
    for _, st, mv in vals:
        class_to_movers[merge[st]].add(mv)
    return all(len(ms) == 1 for ms in class_to_movers.values())


def minimal_controller_size(groups: Dict[Config, List[Tuple[int, int, int]]], critical_only: bool = True) -> int:
    vals_sets = [vals for _, vals in groups.items()]
    if critical_only:
        vals_sets = [vals for vals in vals_sets if len({mv for _, _, mv in vals}) >= 2]
    max_state = max(st for vals in vals_sets for _, st, _ in vals)
    domain = max_state + 1
    for k in range(1, domain + 1):
        for merge in all_surjections(domain, k):
            if all(deterministic_under_merge(vals, merge) for vals in vals_sets):
                return k
    return domain


def print_shadow_report(ms: Sequence[int], cycle: Sequence[Config]) -> None:
    moves = mover_word(cycle)
    print("cycle length:", len(cycle))
    print("mover word:", moves)
    print("move counts:", {j: moves.count(j) for j in range(len(ms))})
    print()
    for forget in range(len(ms)):
        groups = controller_groups(cycle, forget)
        cap = router_capacity(groups)
        print(f"forget {forget}: cap={cap}")
        if cap >= 3:
            for sh, vals in critical_groups(groups):
                print(f"  shadow {sh}: {vals}")
                state_map: Dict[int, set[int]] = defaultdict(set)
                for _, st, mv in vals:
                    state_map[st].add(mv)
                pretty = {st: sorted(mvs) for st, mvs in sorted(state_map.items())}
                print(f"    state->movers {pretty}")
        print()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ms", required=True, help="comma-separated state profile")
    parser.add_argument("--codes", required=True, help="comma-separated cycle codes")
    parser.add_argument(
        "--show-min-quotients",
        action="store_true",
        help="also compute the minimal deterministic controller size for each forgotten processor",
    )
    args = parser.parse_args()

    ms = parse_nat_list(args.ms)
    codes = parse_nat_list(args.codes)
    cycle = [decode_code(c, ms) for c in codes]

    print("ms:", tuple(ms))
    print("codes:", codes)
    print("decoded cycle:")
    for i, cfg in enumerate(cycle):
        print(f"  {i:2d}: {cfg}")
    print()

    print_shadow_report(ms, cycle)

    if args.show_min_quotients:
        for forget in range(len(ms)):
            groups = controller_groups(cycle, forget)
            m = minimal_controller_size(groups)
            print(f"minimal deterministic controller size at forget {forget}: {m}")


if __name__ == "__main__":
    main()
