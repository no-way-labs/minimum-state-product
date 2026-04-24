#!/usr/bin/env python3
"""
Validate a finite-state summary candidate for the one-segment macro potential.

Candidate summary for a configuration c:

  summary(c) =
    (c[0], c[1], c[2], c[3], c[4], c[5],
     c[n-6], c[n-5], c[n-4], c[n-3], c[n-2], c[n-1],
     monoTag(c[6:n-6]))

where monoTag(core) is:
  - 0, 1, or 2 if the omitted middle core is constant at that value
  - None otherwise

This script checks that the one-segment correction
  segmentMaxFc(c) - fc(c)
is determined by this summary, using boundary-6 slice DP to avoid full-state
materialization at larger n.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from itertools import product
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.phifull_verify_lean_contract import Cup2Model


def mono_tag(core: tuple[int, ...]) -> int | None:
    if not core:
        return None
    first = core[0]
    return first if all(x == first for x in core) else None


def boundary6(cfg: tuple[int, ...]) -> tuple[int, ...]:
    n = len(cfg)
    return (cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1])


def summary_sig(cfg: tuple[int, ...]) -> tuple[int | None, ...]:
    n = len(cfg)
    core = cfg[6 : n - 6]
    return (
        *cfg[:6],
        *cfg[n - 6 :],
        mono_tag(core),
    )


def all_boundary6_classes() -> list[tuple[int, ...]]:
    out = []
    for c0 in [0, 1]:
        for c1 in [0, 1, 2]:
            for c2 in [0, 1, 2]:
                for cn3 in [0, 1, 2]:
                    for cn2 in [0, 1, 2]:
                        for cn1 in [0, 1]:
                            out.append((c0, c1, c2, cn3, cn2, cn1))
    return out


def slice_segment_corrections(n: int, b6: tuple[int, ...]) -> tuple[list[tuple[int, ...]], list[int]]:
    model = Cup2Model(n)
    good = model.good_cycle_set()
    free_positions = [i for i in range(n) if i not in {0, 1, 2, n - 3, n - 2, n - 1}]

    states: list[tuple[int, ...]] = []
    for vals in product(range(3), repeat=len(free_positions)):
        cfg = [None] * n
        cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1] = b6
        for i, v in zip(free_positions, vals):
            cfg[i] = v
        states.append(tuple(cfg))

    idx_of = {cfg: i for i, cfg in enumerate(states)}
    fc_vals = [model.fc(cfg) for cfg in states]
    tp_vals = [model.tp(cfg) for cfg in states]
    bad_flags = [model.encode(cfg) not in good for cfg in states]

    fixed_succ = [[] for _ in states]
    indeg = [0] * len(states)
    segment_max_fc = fc_vals[:]

    for i, cfg in enumerate(states):
        if not bad_flags[i]:
            continue
        for p in range(n):
            if not model.privileged(cfg, p):
                continue
            dst = model.fire(cfg, p)
            if model.encode(dst) in good:
                continue
            if model.tp(dst) != tp_vals[i]:
                continue
            if boundary6(dst) == b6:
                j = idx_of[dst]
                fixed_succ[i].append(j)
                indeg[j] += 1
            else:
                dst_fc = model.fc(dst)
                if dst_fc > segment_max_fc[i]:
                    segment_max_fc[i] = dst_fc

    q = deque(i for i, d in enumerate(indeg) if d == 0)
    topo: list[int] = []
    while q:
        i = q.popleft()
        topo.append(i)
        for j in fixed_succ[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                q.append(j)
    assert len(topo) == len(states)

    for i in reversed(topo):
        for j in fixed_succ[i]:
            if segment_max_fc[j] > segment_max_fc[i]:
                segment_max_fc[i] = segment_max_fc[j]

    corrections = [segment_max_fc[i] - fc_vals[i] for i in range(len(states))]
    return states, corrections


def validate_summary(n: int) -> None:
    nonfunctional = 0
    examples: list[tuple[tuple[int, ...], tuple[int | None, ...], list[int]]] = []
    corr_counter: Counter[int] = Counter()

    for idx, b6 in enumerate(all_boundary6_classes(), start=1):
        states, corr = slice_segment_corrections(n, b6)
        corr_counter.update(corr)
        by_sig: dict[tuple[int | None, ...], set[int]] = defaultdict(set)
        for cfg, d in zip(states, corr):
            by_sig[summary_sig(cfg)].add(d)
        local_nonfunc = sum(1 for vals in by_sig.values() if len(vals) > 1)
        if local_nonfunc:
            nonfunctional += local_nonfunc
            if len(examples) < 10:
                for sig, vals in by_sig.items():
                    if len(vals) > 1:
                        examples.append((b6, sig, sorted(vals)))
                        break
        if idx % 50 == 0:
            print(f"processed {idx} / 324 boundary slices; nonfunctional = {nonfunctional}")

    print(f"n = {n}")
    print(f"segment correction distribution: {dict(sorted(corr_counter.items()))}")
    print(f"nonfunctional summary signatures: {nonfunctional}")
    if examples:
        print("examples:")
        for ex in examples:
            print(ex)


def main() -> None:
    validate_summary(14)


if __name__ == "__main__":
    main()
