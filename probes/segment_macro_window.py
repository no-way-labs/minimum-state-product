#!/usr/bin/env python3
"""
Analyze the one-segment macro object suggested by the uniform-strip intuition:

  segmentMaxFc(c) = max fc(d)
    over paths c ~>* x -> d
    where ~>* is a chain of boundary-fixed TP-preserving bad steps
    and x -> d is one boundary-changing TP-preserving bad step.

This quotients out interior transport before the next boundary event.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.phifull_verify_lean_contract import Cup2Model, compute_phi_full


def boundary6(cfg: tuple[int, ...]) -> tuple[int, ...]:
    n = len(cfg)
    return (cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1])


def compute_segment_max_fc(n: int) -> dict[str, object]:
    model = Cup2Model(n)
    data = compute_phi_full(model)
    cfgs = data["cfgs"]
    fc_vals = data["fc"]
    bad_global = data["bad_global"]
    adj = data["adj"]

    bdry = [boundary6(cfgs[g]) for g in bad_global]
    fixed_rev = [[] for _ in bad_global]
    fixed_indeg = [0] * len(bad_global)
    change_succ = [[] for _ in bad_global]

    for src in range(len(bad_global)):
        for dst in adj[src]:
            if bdry[src] == bdry[dst]:
                fixed_rev[dst].append(src)
                fixed_indeg[dst] += 1
            else:
                change_succ[src].append(dst)

    q = deque(i for i, d in enumerate(fixed_indeg) if d == 0)
    topo: list[int] = []
    while q:
        i = q.popleft()
        topo.append(i)
        for dst in adj[i]:
            if bdry[i] == bdry[dst]:
                fixed_indeg[dst] -= 1
                if fixed_indeg[dst] == 0:
                    q.append(dst)
    assert len(topo) == len(bad_global)

    segment_max_fc = [fc_vals[g] for g in bad_global]
    for src in range(len(bad_global)):
        if change_succ[src]:
            segment_max_fc[src] = max(
                segment_max_fc[src],
                max(fc_vals[bad_global[dst]] for dst in change_succ[src]),
            )
    for dst in reversed(topo):
        for src in fixed_rev[dst]:
            if segment_max_fc[dst] > segment_max_fc[src]:
                segment_max_fc[src] = segment_max_fc[dst]

    return {
        "model": model,
        "data": data,
        "segment_max_fc": segment_max_fc,
    }


def nonfunctional_window_count(
    cfgs: list[tuple[int, ...]],
    bad_global: list[int],
    values: list[int],
    left_width: int,
    right_width: int,
) -> int:
    n = len(cfgs[0])
    by_sig: dict[tuple[int, ...], set[int]] = defaultdict(set)
    for i, g in enumerate(bad_global):
        cfg = cfgs[g]
        sig = tuple(cfg[:left_width]) + tuple(cfg[n - right_width :])
        by_sig[sig].add(values[i])
    return sum(1 for vals in by_sig.values() if len(vals) > 1)


def first_ambiguous_signature(
    cfgs: list[tuple[int, ...]],
    bad_global: list[int],
    values: list[int],
    left_width: int,
    right_width: int,
) -> tuple[tuple[int, ...], dict[int, tuple[int, ...]]] | None:
    n = len(cfgs[0])
    by_sig: dict[tuple[int, ...], dict[int, tuple[int, ...]]] = defaultdict(dict)
    for i, g in enumerate(bad_global):
        cfg = cfgs[g]
        sig = tuple(cfg[:left_width]) + tuple(cfg[n - right_width :])
        by_sig[sig].setdefault(values[i], cfg)
    for sig, bucket in by_sig.items():
        if len(bucket) > 1:
            return sig, bucket
    return None


def summarize(n: int) -> None:
    result = compute_segment_max_fc(n)
    data = result["data"]
    cfgs = data["cfgs"]
    bad_global = data["bad_global"]
    fc_vals = data["fc"]
    seg_fc = result["segment_max_fc"]
    corr = [seg_fc[i] - fc_vals[g] for i, g in enumerate(bad_global)]

    print("=" * 72)
    print(f"n = {n}")
    print(f"  segment correction distribution: {dict(sorted(Counter(corr).items()))}")

    best = []
    for left_width in range(3, min(7, n + 1)):
        for right_width in range(3, min(7, n + 1)):
            nonfunc = nonfunctional_window_count(
                cfgs, bad_global, corr, left_width, right_width
            )
            if nonfunc == 0:
                best.append((left_width + right_width, left_width, right_width))
    print(f"  exact windows with widths <= 6: {sorted(best)[:10]}")
    for widths in [(6, 6), (6, 5), (5, 6), (5, 5), (6, 4), (4, 6)]:
        left_width, right_width = widths
        if left_width > n or right_width > n:
            continue
        nonfunc = nonfunctional_window_count(
            cfgs, bad_global, corr, left_width, right_width
        )
        print(f"    window {widths}: nonfunctional signatures = {nonfunc}")

    if n == 13:
        witness = first_ambiguous_signature(cfgs, bad_global, corr, 6, 6)
        if witness is not None:
            sig, bucket = witness
            print("  first n=13 ambiguity for 6+6 boundary window:")
            print(f"    signature = {sig}")
            for value in sorted(bucket):
                print(f"    correction {value}: {bucket[value]}")


def main() -> None:
    for n in [9, 10, 11, 12, 13]:
        summarize(n)


if __name__ == "__main__":
    main()
