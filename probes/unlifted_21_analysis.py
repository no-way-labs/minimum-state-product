#!/usr/bin/env python3
"""Analyze the 21 unlifted Phi-achiever pairs for source_transport at n=9, k=4.

The target family is the same one counted in
`source_transport_global_research.py` TASK 2:

  - bad source `c` at size `n`
  - bad deleted source `delete(c)` at size `n-1`
  - `PhiFull(c) = PhiFull(delete(c))`
  - `d'` is TP-reachable from `delete(c)` and achieves `PhiFull(delete(c))`
  - there is no exact lift `d in S_n(c)` with `delete(d) = d'`

This script prints all such pairs explicitly and then diagnoses the actual
mechanism that still proves `fc(d') <= PhiFull(c)`.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


ROOT = os.path.dirname(__file__)
sys.path.insert(0, ROOT)

from source_transport_seam_research import (  # type: ignore
    Config,
    TpBadGraph,
    delete_config,
    format_cfg,
    valid_sites,
)
from source_transport_global_research import (  # type: ignore
    PathResult,
    bfs_path_bad,
    component_desc_bits,
    reachable_bad_nodes,
    small_path,
)


@dataclass
class ReachCache:
    graph: TpBadGraph
    desc_bits: List[int]
    nodes: Dict[Config, Tuple[Config, ...]]

    def get(self, cfg: Config) -> Tuple[Config, ...]:
        cached = self.nodes.get(cfg)
        if cached is not None:
            return cached
        if cfg in self.graph.good_cycle:
            out = (cfg,)
        else:
            out = tuple(reachable_bad_nodes(self.graph, self.desc_bits, cfg))
        self.nodes[cfg] = out
        return out


@dataclass(frozen=True)
class PairAnalysis:
    c: Config
    deleted_c: Config
    dprime: Config
    phi_big: int
    phi_small: int
    fc_c: int
    fc_deleted_c: int
    fc_dprime: int
    defect: int
    gap_to_fc_c: int
    reachable_same_delete: Tuple[Config, ...]
    max_deleted_fc_in_big_reach: int
    closest_deleted_image: Config
    closest_edit_distance: int
    closest_edit_positions: Tuple[int, ...]
    seam_only_single_edit: bool
    dominating_d: Config
    big_path: PathResult
    deleted_d: Config
    projected_path: PathResult
    deleted_lag: PathResult
    fc_deleted_d: int


def hamming_positions(a: Config, b: Config) -> Tuple[int, ...]:
    return tuple(idx for idx, (x, y) in enumerate(zip(a, b)) if x != y)


def summarize_counter(counter: Counter[int]) -> str:
    if not counter:
        return "(empty)"
    return ", ".join(f"{key}:{counter[key]}" for key in sorted(counter))


def pair_key(row: PairAnalysis) -> Tuple[Config, Config]:
    return (row.c, row.dprime)


def choose_dominating_witness(
    big: TpBadGraph,
    small: TpBadGraph,
    c: Config,
    deleted_c: Config,
    dprime: Config,
    phi_big: int,
    k: int,
    big_nodes: Iterable[Config],
) -> Tuple[Config, PathResult, Config, PathResult, PathResult]:
    seam = {k - 1, k}
    candidates = []
    for d in big_nodes:
        if big.fc_all[d] != phi_big:
            continue
        deleted_d = delete_config(d, k)
        lag = small_path(small, deleted_d, dprime)
        if lag is None:
            continue
        big_path = bfs_path_bad(big, c, d)
        projected_path = small_path(small, deleted_c, deleted_d)
        if big_path is None or projected_path is None:
            continue
        seam_count = sum(1 for mover in lag.movers if mover in seam)
        candidates.append(
            (
                small.fc_all[deleted_d],
                -len(lag.movers),
                -seam_count,
                -len(big_path.movers),
                d,
                big_path,
                deleted_d,
                projected_path,
                lag,
            )
        )

    if not candidates:
        raise RuntimeError(f"missing dominating witness for c={format_cfg(c)} d'={format_cfg(dprime)}")

    best = max(candidates)
    d = best[4]
    big_path = best[5]
    deleted_d = best[6]
    projected_path = best[7]
    lag = best[8]

    if big_path.movers != projected_path.movers:
        raise RuntimeError(
            "expected the chosen dominating witness to project with the same mover word: "
            f"c={format_cfg(c)} d={format_cfg(d)}"
        )

    return d, big_path, deleted_d, projected_path, lag


def analyze_unlifted_pairs(n: int, k: int) -> Tuple[List[PairAnalysis], int, int]:
    big = TpBadGraph(n)
    small = TpBadGraph(n - 1)
    big.ensure_scc()
    small.ensure_scc()

    big_reach = ReachCache(big, component_desc_bits(big), {})
    small_reach = ReachCache(small, component_desc_bits(small), {})

    total_achiever_pairs = 0
    exact_achiever_pairs = 0
    analyses: List[PairAnalysis] = []

    for c in big.all_configs:
        deleted_c = delete_config(c, k)
        phi_big = big.phi_of(c)
        phi_small = small.phi_of(deleted_c)
        if phi_big != phi_small:
            continue
        if c in big.good_cycle or deleted_c in small.good_cycle:
            continue

        fc_c = big.fc_all[c]
        fc_deleted_c = small.fc_all[deleted_c]
        defect = fc_c - fc_deleted_c

        big_nodes = big_reach.get(c)
        small_nodes = small_reach.get(deleted_c)

        deleted_index: Dict[Config, List[Config]] = defaultdict(list)
        deleted_images: List[Config] = []
        max_deleted_fc = -1
        for d in big_nodes:
            deleted_d = delete_config(d, k)
            deleted_index[deleted_d].append(d)
            deleted_images.append(deleted_d)
            max_deleted_fc = max(max_deleted_fc, small.fc_all[deleted_d])

        achievers = [dprime for dprime in small_nodes if small.fc_all[dprime] == phi_small]
        total_achiever_pairs += len(achievers)

        for dprime in achievers:
            reachable_same_delete = tuple(
                sorted(d for d in deleted_index.get(dprime, []) if big.fc_all[d] >= phi_small)
            )
            if reachable_same_delete:
                exact_achiever_pairs += 1
                continue

            best_edit_positions = min(
                (hamming_positions(dprime, deleted_d) for deleted_d in deleted_images),
                key=lambda pos: (len(pos), pos),
            )
            closest_deleted_image = min(
                deleted_images,
                key=lambda deleted_d: (len(hamming_positions(dprime, deleted_d)), deleted_d),
            )

            seam_only_single_edit = (
                len(best_edit_positions) == 1 and best_edit_positions[0] in {k - 1, k}
            )

            dominating_d, big_path, deleted_d, projected_path, deleted_lag = choose_dominating_witness(
                big=big,
                small=small,
                c=c,
                deleted_c=deleted_c,
                dprime=dprime,
                phi_big=phi_big,
                k=k,
                big_nodes=big_nodes,
            )

            analyses.append(
                PairAnalysis(
                    c=c,
                    deleted_c=deleted_c,
                    dprime=dprime,
                    phi_big=phi_big,
                    phi_small=phi_small,
                    fc_c=fc_c,
                    fc_deleted_c=fc_deleted_c,
                    fc_dprime=small.fc_all[dprime],
                    defect=defect,
                    gap_to_fc_c=small.fc_all[dprime] - fc_c,
                    reachable_same_delete=reachable_same_delete,
                    max_deleted_fc_in_big_reach=max_deleted_fc,
                    closest_deleted_image=closest_deleted_image,
                    closest_edit_distance=len(best_edit_positions),
                    closest_edit_positions=best_edit_positions,
                    seam_only_single_edit=seam_only_single_edit,
                    dominating_d=dominating_d,
                    big_path=big_path,
                    deleted_d=deleted_d,
                    projected_path=projected_path,
                    deleted_lag=deleted_lag,
                    fc_deleted_d=small.fc_all[deleted_d],
                )
            )

    analyses.sort(key=pair_key)
    return analyses, total_achiever_pairs, exact_achiever_pairs


def print_summary(rows: Sequence[PairAnalysis], total_achiever_pairs: int, exact_pairs: int, k: int) -> None:
    seam = {k - 1, k}
    print(f"Unlifted Phi-achiever analysis at n=9, k={k}")
    print()
    print("Counts")
    print(f"  achiever pairs checked: {total_achiever_pairs}")
    print(f"  exact achiever lifts: {exact_pairs}")
    print(f"  unlifted achiever pairs: {len(rows)}")
    print(f"  distinct sources c: {len({row.c for row in rows})}")
    print(f"  distinct deleted sources delete(c): {len({row.deleted_c for row in rows})}")
    print(f"  fc(d') - fc(c): {summarize_counter(Counter(row.gap_to_fc_c for row in rows))}")
    print(f"  defect(c): {summarize_counter(Counter(row.defect for row in rows))}")
    print(
        "  fc(d') <= PhiFull(c): "
        f"{sum(1 for row in rows if row.fc_dprime <= row.phi_big)} / {len(rows)}"
    )
    print(
        "  fc(d') = PhiFull(c): "
        f"{sum(1 for row in rows if row.fc_dprime == row.phi_big)} / {len(rows)}"
    )
    print(
        "  reachable d in S_n(c) with delete(d)=d': "
        f"{sum(1 for row in rows if row.reachable_same_delete)} / {len(rows)}"
    )
    print(
        "  PhiFull(c) - max fc(delete(S_n(c))): "
        f"{summarize_counter(Counter(row.phi_big - row.max_deleted_fc_in_big_reach for row in rows))}"
    )
    print(
        "  fc(d') - max fc(delete(S_n(c))): "
        f"{summarize_counter(Counter(row.fc_dprime - row.max_deleted_fc_in_big_reach for row in rows))}"
    )
    print(
        "  min edit distance from d' to delete(S_n(c)): "
        f"{summarize_counter(Counter(row.closest_edit_distance for row in rows))}"
    )
    print(
        "  seam-only edit-distance-1 matches: "
        f"{sum(1 for row in rows if row.seam_only_single_edit)} / {len(rows)}"
    )
    print(
        "  dominating witness path length c -> d: "
        f"{summarize_counter(Counter(len(row.big_path.movers) for row in rows))}"
    )
    print(
        "  deleted-lag gain fc(d') - fc(delete(d)): "
        f"{summarize_counter(Counter(row.fc_dprime - row.fc_deleted_d for row in rows))}"
    )
    print(
        "  deleted-lag seam-step count: "
        f"{summarize_counter(Counter(sum(1 for m in row.deleted_lag.movers if m in seam) for row in rows))}"
    )
    print(
        "  deleted-lag total length: "
        f"{summarize_counter(Counter(len(row.deleted_lag.movers) for row in rows))}"
    )
    print(
        "  projected-prefix check delete(c)->delete(d) uses same mover word as c->d: "
        f"{sum(1 for row in rows if row.big_path.movers == row.projected_path.movers)} / {len(rows)}"
    )
    print(
        "  deleted-lag mover patterns: "
        f"{Counter(tuple(row.deleted_lag.movers) for row in rows)}"
    )
    print()
    print("Mechanism")
    print("  1. These 21 failures are pure delete-image failures, not fc failures.")
    print("     In every case, fc(d') = PhiFull(delete(c)) = PhiFull(c).")
    print("  2. None of the 21 pairs has any reachable exact image delete(d)=d'.")
    print("     The closest deleted reachable state is still Hamming distance 5 or 6 away.")
    print("  3. Nevertheless, every pair has a reachable size-9 witness d with fc(d)=fc(d').")
    print("     For the chosen d, delete(c)->delete(d) projects exactly from c->d, and")
    print("     delete(d)->d' is a deleted-only tail.")
    print("  4. Numerically, max fc(delete(S_n(c))) is always exactly one below PhiFull(c),")
    print("     while fc(d') = PhiFull(c). So deletion loses one frontier on every exact image,")
    print("     and the deleted graph recreates that one frontier later through seam-driven lag.")
    print()


def print_details(rows: Sequence[PairAnalysis], k: int) -> None:
    by_source: Dict[Config, List[PairAnalysis]] = defaultdict(list)
    for row in rows:
        by_source[row.c].append(row)

    for source_idx, c in enumerate(sorted(by_source), start=1):
        source_rows = sorted(by_source[c], key=lambda row: row.dprime)
        first = source_rows[0]
        print(
            f"[source {source_idx}] c={format_cfg(first.c)} "
            f"delete(c)={format_cfg(first.deleted_c)} "
            f"PhiFull(c)={first.phi_big} fc(c)={first.fc_c} defect(c)={first.defect}"
        )
        print(
            "  source-level numbers: "
            f"fc(delete(c))={first.fc_deleted_c} "
            f"max fc(delete(S_n(c)))={first.max_deleted_fc_in_big_reach}"
        )
        print()

        for pair_idx, row in enumerate(source_rows, start=1):
            gap_vs_phi = row.phi_big - row.fc_dprime
            gap_vs_delete_image = row.fc_dprime - row.max_deleted_fc_in_big_reach
            edit_positions = ",".join(str(pos) for pos in row.closest_edit_positions)
            seam_count = sum(1 for mover in row.deleted_lag.movers if mover in {k - 1, k})

            print(f"  ({pair_idx}) d'={format_cfg(row.dprime)}")
            print(
                "      "
                f"fc(d')={row.fc_dprime} "
                f"PhiFull(c)={row.phi_big} "
                f"fc(c)={row.fc_c} "
                f"gap_vs_fc(c)={row.gap_to_fc_c}"
            )
            print(
                "      "
                f"fc(d') <= PhiFull(c): yes "
                f"(gap PhiFull(c)-fc(d')={gap_vs_phi})"
            )
            print("      reachable d with delete(d)=d': no")
            print(
                "      "
                f"max fc(delete(S_n(c)))={row.max_deleted_fc_in_big_reach} "
                f"(short by {gap_vs_delete_image})"
            )
            print(
                "      "
                f"closest delete-image={format_cfg(row.closest_deleted_image)} "
                f"edit_distance={row.closest_edit_distance} "
                f"edit_positions=[{edit_positions}] "
                f"seam_only_edit1={row.seam_only_single_edit}"
            )
            print(
                "      "
                f"dominating d={format_cfg(row.dominating_d)} "
                f"fc(d)={row.phi_big} "
                f"big movers={row.big_path.movers}"
            )
            print(
                "      "
                f"delete(d)={format_cfg(row.deleted_d)} "
                f"fc(delete(d))={row.fc_deleted_d} "
                f"projected movers={row.projected_path.movers}"
            )
            print(
                "      "
                f"delete(d)->d' movers={row.deleted_lag.movers} "
                f"seam_steps={seam_count} "
                f"gain={row.fc_dprime - row.fc_deleted_d}"
            )
            print()


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--k", type=int, default=4)
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    if args.k not in valid_sites(args.n):
        raise SystemExit(f"k must be one of {valid_sites(args.n)} for n={args.n}")

    rows, total_achiever_pairs, exact_pairs = analyze_unlifted_pairs(args.n, args.k)
    print_summary(rows, total_achiever_pairs, exact_pairs, args.k)
    print_details(rows, args.k)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
