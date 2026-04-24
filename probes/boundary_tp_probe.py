#!/usr/bin/env python3
"""Probe boundary TP-preserving bad steps for H_nocopy membership.

Problem target:
  CPhiDelete.lean around period2_noCopy_nIndep_core (~line 2933 in this tree).

This script does two kinds of checks.

1. Exact scan on n = 9..13:
   Enumerate every boundary move (positions 0,1,2,n-3,n-2,n-1), keep the ones
   that are exact Lean bad steps and TP-preserving, and test whether the induced
   boundary 6-tuple transition lies in H_nocopy (= isNoCopyEdge).

2. Boundary-local abstract scan:
   Enumerate only the finite boundary data relevant to each boundary mover,
   independent of global good/bad status, and compare:
     - all privileged boundary transitions
     - privileged + TP-preserving boundary transitions
     - membership in G617 and H_nocopy

The goal is to distinguish:
  - "always in G617 anyway"
  - "H_nocopy follows from TP-preservation"
  - "simple finite case split on the 6 boundary positions"
"""

from __future__ import annotations

import ast
import itertools
import re
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple


Config = Tuple[int, ...]


LEAN_CHECKOUT = Path(__file__).resolve().parents[2]
LEAN_ROOT = LEAN_CHECKOUT / "LeanMn" / "Convergence"
CPHI_DELETE = LEAN_ROOT / "CPhiDelete.lean"
SIX_TUPLE = LEAN_ROOT / "SixTuple.lean"


# Exact CUP-2 tables from LeanMn/Tables.lean.
T_BOT = {
    (0, 0, 0): 1, (0, 0, 1): 1, (0, 0, 2): 0,
    (0, 1, 0): 1, (0, 1, 1): 1, (0, 1, 2): 1,
    (1, 0, 0): 0, (1, 0, 1): 1, (1, 0, 2): 0,
    (1, 1, 0): 0, (1, 1, 1): 1, (1, 1, 2): 0,
}

T_LOW = {
    (0, 0, 0): 0, (0, 0, 1): 0, (0, 0, 2): 0,
    (0, 1, 0): 0, (0, 1, 1): 1, (0, 1, 2): 0,
    (0, 2, 0): 0, (0, 2, 1): 2, (0, 2, 2): 0,
    (1, 0, 0): 1, (1, 0, 1): 1, (1, 0, 2): 1,
    (1, 1, 0): 1, (1, 1, 1): 1, (1, 1, 2): 2,
    (1, 2, 0): 0, (1, 2, 1): 1, (1, 2, 2): 2,
}

T_MID = {
    (0, 0, 0): 0, (0, 0, 1): 0, (0, 0, 2): 0,
    (0, 1, 0): 0, (0, 1, 1): 1, (0, 1, 2): 0,
    (0, 2, 0): 0, (0, 2, 1): 2, (0, 2, 2): 0,
    (1, 0, 0): 1, (1, 0, 1): 1, (1, 0, 2): 1,
    (1, 1, 0): 1, (1, 1, 1): 1, (1, 1, 2): 2,
    (1, 2, 0): 0, (1, 2, 1): 1, (1, 2, 2): 2,
    (2, 0, 0): 0, (2, 0, 1): 0, (2, 0, 2): 2,
    (2, 1, 0): 1, (2, 1, 1): 0, (2, 1, 2): 2,
    (2, 2, 0): 0, (2, 2, 1): 2, (2, 2, 2): 2,
}

T_HIGH = {
    (0, 0, 0): 0, (0, 0, 1): 0,
    (0, 1, 0): 0, (0, 1, 1): 0,
    (0, 2, 0): 0, (0, 2, 1): 0,
    (1, 0, 0): 1, (1, 0, 1): 1,
    (1, 1, 0): 1, (1, 1, 1): 2,
    (1, 2, 0): 0, (1, 2, 1): 2,
    (2, 0, 0): 0, (2, 0, 1): 2,
    (2, 1, 0): 0, (2, 1, 1): 2,
    (2, 2, 0): 2, (2, 2, 1): 2,
}

T_TOP = {
    (0, 0, 0): 0, (0, 0, 1): 0,
    (0, 1, 0): 0, (0, 1, 1): 0,
    (1, 0, 0): 0, (1, 0, 1): 1,
    (1, 1, 0): 1, (1, 1, 1): 1,
    (2, 0, 0): 1, (2, 0, 1): 1,
    (2, 1, 0): 1, (2, 1, 1): 1,
}


BOUNDARY_LABELS = ("0", "1", "2", "n-3", "n-2", "n-1")


@dataclass
class ExactSummary:
    n: int
    total_bad_tp_boundary: int
    by_label: Counter
    all_tp_boundary: int
    all_tp_boundary_by_label: Counter
    all_priv_boundary: int
    all_priv_boundary_by_label: Counter
    bad_failures_h: List[Tuple[str, Config, Config, int, int]]
    bad_failures_g617: List[Tuple[str, Config, Config, int, int]]
    all_tp_failures_h: List[Tuple[str, Config, Config, int, int]]


@dataclass
class AbstractPositionSummary:
    total_cases: int
    privileged_cases: int
    privileged_in_g617: int
    privileged_in_h: int
    tp_cases: int
    tp_in_h: int
    tp_not_h_examples: List[Tuple]
    priv_not_h_examples: List[Tuple]
    signatures_tp: Set[Tuple]


def load_nat_array_from_lean(path: Path, def_name: str) -> List[int]:
    text = path.read_text()
    pattern = rf"def {re.escape(def_name)}\s*:\s*Array Nat\s*:=\s*#\[(.*?)\]"
    match = re.search(pattern, text, re.S)
    if not match:
        raise RuntimeError(f"Could not locate Array Nat definition {def_name} in {path}")
    body = "[" + match.group(1) + "]"
    return list(ast.literal_eval(body))


def load_pair_list_from_lean(path: Path, def_name: str) -> List[Tuple[int, int]]:
    text = path.read_text()
    pattern = rf"def {re.escape(def_name)}\s*:\s*List \(Nat × Nat\)\s*:=\s*\[(.*?)\]"
    match = re.search(pattern, text, re.S)
    if not match:
        raise RuntimeError(f"Could not locate pair list definition {def_name} in {path}")
    body = "[" + match.group(1) + "]"
    return [tuple(pair) for pair in ast.literal_eval(body)]


def cup2_m(n: int, i: int) -> int:
    return 2 if i == 0 or i == n - 1 else 3


def state_ranges(n: int) -> List[range]:
    return [range(cup2_m(n, i)) for i in range(n)]


def all_configs(n: int) -> Iterator[Config]:
    return itertools.product(*state_ranges(n))


def cup2_cycle_val(n: int, t: int, j: int) -> int:
    if t < n:
        return 1 if j < t else 0
    if t < 2 * n - 2:
        if j < 2 * n - 1 - t:
            return 1
        if j < n - 1:
            return 2
        return 1
    if t == 2 * n - 2:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    k = t - (2 * n - 2)
    if k == 0:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    if j < k:
        return 0
    if j < n - 1:
        return 2
    return 1


def cycle_config(n: int, t: int) -> Config:
    return tuple(cup2_cycle_val(n, t, j) for j in range(n))


def good_cycle_configs(n: int) -> Set[Config]:
    return {cycle_config(n, t) for t in range(3 * n - 2)}


def move_table(n: int, mover: int) -> Dict[Tuple[int, int, int], int]:
    if mover == 0:
        return T_BOT
    if mover == 1:
        return T_LOW
    if mover == n - 2:
        return T_HIGH
    if mover == n - 1:
        return T_TOP
    return T_MID


def out_value(config: Config, mover: int) -> int:
    n = len(config)
    left = config[(mover - 1) % n]
    self_val = config[mover]
    right = config[(mover + 1) % n]
    return move_table(n, mover)[(left, self_val, right)]


def move(config: Config, mover: int) -> Optional[Config]:
    out = out_value(config, mover)
    if out == config[mover]:
        return None
    updated = list(config)
    updated[mover] = out
    return tuple(updated)


def boundary_positions(n: int) -> List[Tuple[str, int]]:
    return [
        ("0", 0),
        ("1", 1),
        ("2", 2),
        ("n-3", n - 3),
        ("n-2", n - 2),
        ("n-1", n - 1),
    ]


def encode_boundary6(c0: int, c1: int, c2: int, cn3: int, cn2: int, cn1: int) -> int:
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cn3) * 3 + cn2) * 2 + cn1


def boundary_state(config: Config) -> int:
    n = len(config)
    return encode_boundary6(config[0], config[1], config[2], config[n - 3], config[n - 2], config[n - 1])


def exp2_bit(n: int, j: int, a: int, b: int) -> int:
    return 1 if 2 <= j and j + 2 < n and a == 2 and b != 2 else 0


def int21_bit(n: int, j: int, a: int, b: int) -> int:
    return 1 if 2 <= j and j + 2 < n and a == 2 and b == 1 else 0


def tp_preserving_move(config: Config, mover: int, dst: Config) -> bool:
    n = len(config)
    before_exp2 = before_i21 = before_w = 0
    after_exp2 = after_i21 = after_w = 0
    for j in (mover - 1, mover):
        if 2 <= j and j + 2 < n:
            a0 = config[j]
            b0 = config[j + 1]
            a1 = dst[j]
            b1 = dst[j + 1]
            be = exp2_bit(n, j, a0, b0)
            bi = int21_bit(n, j, a0, b0)
            ae = exp2_bit(n, j, a1, b1)
            ai = int21_bit(n, j, a1, b1)
            before_exp2 += be
            before_i21 += bi
            before_w += j * be
            after_exp2 += ae
            after_i21 += ai
            after_w += j * ae
    return (
        before_exp2 == after_exp2
        and before_i21 == after_i21
        and before_w == after_w
    )


def synthetic_boundary_config(
    n: int,
    src_boundary: Tuple[int, int, int, int, int, int],
    label: str,
    extra: Optional[int],
) -> Config:
    c0, c1, c2, cn3, cn2, cn1 = src_boundary
    values = [0] * n
    values[0] = c0
    values[1] = c1
    values[2] = c2
    values[n - 3] = cn3
    values[n - 2] = cn2
    values[n - 1] = cn1
    if label == "2":
        assert extra is not None
        values[3] = extra
    elif label == "n-3":
        assert extra is not None
        values[n - 4] = extra
    return tuple(values)


def abstract_signature(src_boundary: Tuple[int, int, int, int, int, int], extra: Optional[int]) -> Tuple:
    if extra is None:
        return (encode_boundary6(*src_boundary),)
    return (encode_boundary6(*src_boundary), extra)


def analyze_exact_n(n: int, h_set: Set[int], g617: Set[Tuple[int, int]]) -> ExactSummary:
    good = good_cycle_configs(n)
    bad_failures_h: List[Tuple[str, Config, Config, int, int]] = []
    bad_failures_g617: List[Tuple[str, Config, Config, int, int]] = []
    all_tp_failures_h: List[Tuple[str, Config, Config, int, int]] = []

    total_bad_tp_boundary = 0
    total_all_tp_boundary = 0
    total_all_priv_boundary = 0
    by_label: Counter = Counter()
    all_tp_by_label: Counter = Counter()
    all_priv_by_label: Counter = Counter()

    for src in all_configs(n):
        src_good = src in good
        src_b = boundary_state(src)
        for label, mover in boundary_positions(n):
            dst = move(src, mover)
            if dst is None:
                continue

            total_all_priv_boundary += 1
            all_priv_by_label[label] += 1

            dst_b = boundary_state(dst)
            packed = src_b * 324 + dst_b
            pair = (src_b, dst_b)

            tp_ok = tp_preserving_move(src, mover, dst)
            if tp_ok:
                total_all_tp_boundary += 1
                all_tp_by_label[label] += 1
                if packed not in h_set and len(all_tp_failures_h) < 10:
                    all_tp_failures_h.append((label, src, dst, src_b, dst_b))

            if src_good or dst in good:
                continue

            if not tp_ok:
                continue

            total_bad_tp_boundary += 1
            by_label[label] += 1

            if packed not in h_set and len(bad_failures_h) < 10:
                bad_failures_h.append((label, src, dst, src_b, dst_b))
            if pair not in g617 and len(bad_failures_g617) < 10:
                bad_failures_g617.append((label, src, dst, src_b, dst_b))

    return ExactSummary(
        n=n,
        total_bad_tp_boundary=total_bad_tp_boundary,
        by_label=by_label,
        all_tp_boundary=total_all_tp_boundary,
        all_tp_boundary_by_label=all_tp_by_label,
        all_priv_boundary=total_all_priv_boundary,
        all_priv_boundary_by_label=all_priv_by_label,
        bad_failures_h=bad_failures_h,
        bad_failures_g617=bad_failures_g617,
        all_tp_failures_h=all_tp_failures_h,
    )


def analyze_abstract_position(
    n: int,
    label: str,
    mover: int,
    h_set: Set[int],
    g617: Set[Tuple[int, int]],
) -> AbstractPositionSummary:
    total_cases = 0
    privileged_cases = 0
    privileged_in_g617 = 0
    privileged_in_h = 0
    tp_cases = 0
    tp_in_h = 0
    tp_not_h_examples: List[Tuple] = []
    priv_not_h_examples: List[Tuple] = []
    signatures_tp: Set[Tuple] = set()

    extras: Iterable[Optional[int]]
    if label in ("2", "n-3"):
        extras = range(3)
    else:
        extras = (None,)

    for c0 in range(2):
        for c1 in range(3):
            for c2 in range(3):
                for cn3 in range(3):
                    for cn2 in range(3):
                        for cn1 in range(2):
                            src_boundary = (c0, c1, c2, cn3, cn2, cn1)
                            for extra in extras:
                                total_cases += 1
                                src = synthetic_boundary_config(n, src_boundary, label, extra)
                                dst = move(src, mover)
                                if dst is None:
                                    continue

                                privileged_cases += 1
                                src_b = boundary_state(src)
                                dst_b = boundary_state(dst)
                                packed = src_b * 324 + dst_b
                                pair = (src_b, dst_b)

                                if pair in g617:
                                    privileged_in_g617 += 1
                                if packed in h_set:
                                    privileged_in_h += 1
                                elif len(priv_not_h_examples) < 5:
                                    priv_not_h_examples.append((label, src_boundary, extra, src_b, dst_b))

                                if not tp_preserving_move(src, mover, dst):
                                    continue

                                tp_cases += 1
                                signatures_tp.add(abstract_signature(src_boundary, extra))
                                if packed in h_set:
                                    tp_in_h += 1
                                elif len(tp_not_h_examples) < 5:
                                    tp_not_h_examples.append((label, src_boundary, extra, src_b, dst_b))

    return AbstractPositionSummary(
        total_cases=total_cases,
        privileged_cases=privileged_cases,
        privileged_in_g617=privileged_in_g617,
        privileged_in_h=privileged_in_h,
        tp_cases=tp_cases,
        tp_in_h=tp_in_h,
        tp_not_h_examples=tp_not_h_examples,
        priv_not_h_examples=priv_not_h_examples,
        signatures_tp=signatures_tp,
    )


def analyze_abstract_ns(
    ns: Sequence[int],
    h_set: Set[int],
    g617: Set[Tuple[int, int]],
) -> Dict[int, Dict[str, AbstractPositionSummary]]:
    results: Dict[int, Dict[str, AbstractPositionSummary]] = {}
    for n in ns:
        per_n: Dict[str, AbstractPositionSummary] = {}
        for label, mover in boundary_positions(n):
            per_n[label] = analyze_abstract_position(n, label, mover, h_set, g617)
        results[n] = per_n
    return results


def format_pct(count: int, total: int) -> str:
    if total == 0:
        return "0.00%"
    return f"{100.0 * count / total:.2f}%"


def print_exact_summary(summary: ExactSummary) -> None:
    print(f"\n=== Exact scan: n={summary.n} ===")
    print(f"all privileged boundary steps: {summary.all_priv_boundary}")
    print(f"all TP-preserving boundary steps: {summary.all_tp_boundary}")
    print(f"bad TP-preserving boundary steps: {summary.total_bad_tp_boundary}")
    print("bad TP-preserving mover fractions:")
    for label in BOUNDARY_LABELS:
        count = summary.by_label[label]
        print(f"  {label:>3}: {count:>8}  ({format_pct(count, summary.total_bad_tp_boundary)})")

    if summary.bad_failures_g617:
        print("bad TP boundary failures of G617:")
        for label, src, dst, src_b, dst_b in summary.bad_failures_g617:
            print(f"  {label}: src_b={src_b}, dst_b={dst_b}, src={src}, dst={dst}")
    else:
        print("bad TP boundary steps in G617: yes, all of them")

    if summary.bad_failures_h:
        print("bad TP boundary failures of H_nocopy:")
        for label, src, dst, src_b, dst_b in summary.bad_failures_h:
            print(f"  {label}: src_b={src_b}, dst_b={dst_b}, src={src}, dst={dst}")
    else:
        print("bad TP boundary steps in H_nocopy: yes, all of them")

    if summary.all_tp_failures_h:
        print("all TP-preserving boundary failures of H_nocopy:")
        for label, src, dst, src_b, dst_b in summary.all_tp_failures_h:
            print(f"  {label}: src_b={src_b}, dst_b={dst_b}, src={src}, dst={dst}")
    else:
        print("stronger check: every TP-preserving boundary step is in H_nocopy")


def print_aggregate_exact(summaries: Sequence[ExactSummary]) -> None:
    total_bad = sum(s.total_bad_tp_boundary for s in summaries)
    by_label = Counter()
    for s in summaries:
        by_label.update(s.by_label)

    print("\n=== Aggregate bad TP boundary counts (n=9..13) ===")
    print(f"total: {total_bad}")
    for label in BOUNDARY_LABELS:
        count = by_label[label]
        print(f"  {label:>3}: {count:>8}  ({format_pct(count, total_bad)})")

    if total_bad:
        top = max(BOUNDARY_LABELS, key=lambda label: by_label[label])
        print(f"largest share by count: {top}")


def print_abstract_summary(abstract_results: Dict[int, Dict[str, AbstractPositionSummary]]) -> None:
    print("\n=== Boundary-local abstract scan ===")
    stable = True
    first_n = min(abstract_results)
    reference = abstract_results[first_n]

    for n in sorted(abstract_results):
        print(f"\nabstract local cases at n={n}:")
        for label in BOUNDARY_LABELS:
            item = abstract_results[n][label]
            print(
                f"  {label:>3}: total={item.total_cases:>4}, priv={item.privileged_cases:>4}, "
                f"priv_in_G617={item.privileged_in_g617:>4}, priv_in_H={item.privileged_in_h:>4}, "
                f"tp={item.tp_cases:>4}, tp_in_H={item.tp_in_h:>4}"
            )
            ref = reference[label]
            if item.signatures_tp != ref.signatures_tp:
                stable = False

    if stable:
        print("\nTP-preserving abstract boundary signatures are identical across n=9..13.")
    else:
        print("\nTP-preserving abstract boundary signatures vary across n=9..13.")

    print("\nproof-meaningful position summary:")
    for label in BOUNDARY_LABELS:
        ref = reference[label]
        tp_bad = ref.tp_cases - ref.tp_in_h
        priv_not_h = ref.privileged_cases - ref.privileged_in_h
        print(
            f"  {label:>3}: privileged_not_H={priv_not_h:>4}, "
            f"tp_not_H={tp_bad:>4}, distinct_tp_signatures={len(ref.signatures_tp):>4}"
        )
        if ref.priv_not_h_examples:
            print(f"       example privileged-not-H: {ref.priv_not_h_examples[0]}")


def main() -> None:
    t0 = time.time()
    no_copy_codes = load_nat_array_from_lean(CPHI_DELETE, "noCopyEdgeCodes")
    six_tuple_edges = load_pair_list_from_lean(SIX_TUPLE, "sixTupleEdgeVals")
    h_set = set(no_copy_codes)
    g617 = set(six_tuple_edges)

    print("Loaded Lean tables:")
    print(f"  H_nocopy codes: {len(no_copy_codes)}")
    print(f"  G617 edges:     {len(six_tuple_edges)}")

    ns = list(range(9, 14))

    exact_summaries = []
    for n in ns:
        tn = time.time()
        summary = analyze_exact_n(n, h_set, g617)
        exact_summaries.append(summary)
        print_exact_summary(summary)
        print(f"scan time for n={n}: {time.time() - tn:.2f}s")

    print_aggregate_exact(exact_summaries)

    ta = time.time()
    abstract_results = analyze_abstract_ns(ns, h_set, g617)
    print_abstract_summary(abstract_results)
    print(f"\nabstract scan time: {time.time() - ta:.2f}s")

    print(f"\ntotal runtime: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
