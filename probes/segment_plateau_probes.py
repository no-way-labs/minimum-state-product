#!/usr/bin/env python3
"""
Targeted probes for the correction-2 plateau of the one-segment macro potential.

This script does not attempt the full quotient graph. It records the concrete
structure discovered so far:

- on the all-0 and all-1 boundary families, the correction-2 plateau moves by a
  simple transport distance from the relevant side;
- the correction-2 family graph appears sparse and chain-like on tested
  examples.
"""

from __future__ import annotations

from collections import Counter, deque
from functools import lru_cache
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
    return core[0] if all(x == core[0] for x in core) else None


def summary_sig(cfg: tuple[int, ...]) -> tuple[int | None, ...]:
    n = len(cfg)
    return (*cfg[:6], *cfg[n - 6 :], mono_tag(cfg[6 : n - 6]))


def boundary6(cfg: tuple[int, ...]) -> tuple[int, ...]:
    n = len(cfg)
    return (cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1])


def nearest_not_val_from_right(cfg: tuple[int, ...], val: int) -> int | None:
    n = len(cfg)
    for d, i in enumerate(range(n - 1, -1, -1)):
        if cfg[i] != val:
            return d
    return None


def nearest_not_val_from_left(cfg: tuple[int, ...], val: int) -> int | None:
    for d, x in enumerate(cfg):
        if x != val:
            return d
    return None


class SliceAnalyzer:
    def __init__(self, n: int):
        self.n = n
        self.model = Cup2Model(n)
        self.good = self.model.good_cycle_set()
        self.free = [i for i in range(n) if i not in {0, 1, 2, n - 3, n - 2, n - 1}]

    @lru_cache(None)
    def slice_summary_corr(self, b6: tuple[int, ...]) -> dict[tuple[int | None, ...], int]:
        states, seg_fc, _ = self.slice_segment_data(b6)
        out: dict[tuple[int | None, ...], int] = {}
        for cfg, seg in zip(states, seg_fc):
            d = seg - self.model.fc(cfg)
            sig = summary_sig(cfg)
            prev = out.get(sig)
            if prev is None:
                out[sig] = d
            elif prev != d:
                raise RuntimeError(("correction summary mismatch", b6, sig, prev, d))
        return out

    @lru_cache(None)
    def slice_segment_data(
        self, b6: tuple[int, ...]
    ) -> tuple[list[tuple[int, ...]], list[int], list[set[tuple[int, ...]]]]:
        states: list[tuple[int, ...]] = []
        for vals in product(range(3), repeat=len(self.free)):
            cfg = [None] * self.n
            cfg[0], cfg[1], cfg[2], cfg[self.n - 3], cfg[self.n - 2], cfg[self.n - 1] = b6
            for i, v in zip(self.free, vals):
                cfg[i] = v
            states.append(tuple(cfg))

        idx_of = {cfg: i for i, cfg in enumerate(states)}
        fc_vals = [self.model.fc(cfg) for cfg in states]
        tp_vals = [self.model.tp(cfg) for cfg in states]
        bad_flags = [self.model.encode(cfg) not in self.good for cfg in states]

        fixed_succ = [[] for _ in states]
        indeg = [0] * len(states)
        out_targets = [set() for _ in states]
        seg_fc = fc_vals[:]

        for i, cfg in enumerate(states):
            if not bad_flags[i]:
                continue
            for p in range(self.n):
                if not self.model.privileged(cfg, p):
                    continue
                dst = self.model.fire(cfg, p)
                if self.model.encode(dst) in self.good:
                    continue
                if self.model.tp(dst) != tp_vals[i]:
                    continue
                if boundary6(dst) == b6:
                    j = idx_of[dst]
                    fixed_succ[i].append(j)
                    indeg[j] += 1
                else:
                    dst_fc = self.model.fc(dst)
                    if dst_fc > seg_fc[i]:
                        seg_fc[i] = dst_fc
                    out_targets[i].add(dst)

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
                if seg_fc[j] > seg_fc[i]:
                    seg_fc[i] = seg_fc[j]
                out_targets[i].update(out_targets[j])

        return states, seg_fc, out_targets

    def family_targets(self, source_b6: tuple[int, ...]) -> Counter[tuple[int, ...]]:
        states, seg_fc, out_targets = self.slice_segment_data(source_b6)
        fam = Counter()
        for cfg, seg, targets in zip(states, seg_fc, out_targets):
            if seg - self.model.fc(cfg) != 2:
                continue
            for dst in targets:
                dst_b6 = boundary6(dst)
                dst_corr = self.slice_summary_corr(dst_b6)[summary_sig(dst)]
                if dst_corr == 2:
                    fam[dst_b6] += 1
        return fam

    def monochromatic_plateau_pairs(
        self, b6: tuple[int, ...], defect_val: int, side: str
    ) -> Counter[tuple[int | None, int | None]]:
        states, seg_fc, out_targets = self.slice_segment_data(b6)
        pairs = Counter()
        for cfg, seg, targets in zip(states, seg_fc, out_targets):
            if seg - self.model.fc(cfg) != 2:
                continue
            src_d = (
                nearest_not_val_from_right(cfg, defect_val)
                if side == "right"
                else nearest_not_val_from_left(cfg, defect_val)
            )
            for dst in targets:
                dst_b6 = boundary6(dst)
                dst_corr = self.slice_summary_corr(dst_b6)[summary_sig(dst)]
                if dst_corr != 2:
                    continue
                dst_d = (
                    nearest_not_val_from_right(dst, defect_val)
                    if side == "right"
                    else nearest_not_val_from_left(dst, defect_val)
                )
                pairs[(src_d, dst_d)] += 1
        return pairs


def main() -> None:
    for n in [14, 15]:
        print("=" * 72)
        print(f"n = {n}")
        analyzer = SliceAnalyzer(n)

        print("All-0 family correction-2 plateau distance pairs:")
        print(
            analyzer.monochromatic_plateau_pairs((0, 0, 0, 0, 0, 0), 0, "right")
        )
        print("All-1 family correction-2 plateau distance pairs:")
        print(
            analyzer.monochromatic_plateau_pairs((1, 1, 1, 1, 1, 1), 1, "left")
        )

        print("Selected correction-2 boundary-family transitions:")
        for b6 in [
            (0, 0, 0, 0, 0, 0),
            (0, 0, 0, 0, 1, 0),
            (0, 0, 0, 1, 0, 0),
            (0, 0, 0, 1, 1, 0),
            (1, 1, 1, 1, 1, 1),
            (1, 1, 2, 1, 1, 1),
        ]:
            print(f"  {b6} -> {analyzer.family_targets(b6)}")


if __name__ == "__main__":
    main()
