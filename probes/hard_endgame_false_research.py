#!/usr/bin/env python3
"""Research probe for `hard_endgame_false` in `AllNormalFormFalse.lean`.

This script stays on the concrete CUP-2 witness side:
  - build the standard CUP-2 systems for n=5,6,7
  - enumerate every cycle in the maximal closed single-privileged subgraph
  - report which cycles are fair
  - check whether the theorem hypotheses for `allNormalForm_false` can even
    start: namely, whether there exists a ternary `t` with both neighbors
    binary (`hbL`, `hbR`)

If no such `t` exists, then the `HardResidue` / `hk_last` branches are vacuous
for the standard CUP-2 witness at that n.
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable


ROOT = os.path.dirname(__file__)
sys.path.insert(0, ROOT)

from cup2_theorem import build_system  # type: ignore
from verifier import verify_system  # type: ignore


Config = tuple[int, ...]
StepFn = Callable[[int, int, int], int]


@dataclass(frozen=True)
class CycleInfo:
    configs: tuple[Config, ...]
    movers: tuple[int, ...]

    @property
    def length(self) -> int:
        return len(self.configs)

    @property
    def fair(self) -> bool:
        return set(self.movers) == set(range(len(self.configs[0])))


def privileged_processors(config: Config, fs: list[StepFn]) -> tuple[int, ...]:
    n = len(config)
    out = []
    for i in range(n):
        left = config[(i - 1) % n]
        self_val = config[i]
        right = config[(i + 1) % n]
        if fs[i](left, self_val, right) != self_val:
            out.append(i)
    return tuple(out)


def apply_move(config: Config, proc: int, fs: list[StepFn]) -> Config:
    updated = list(config)
    left = config[(proc - 1) % len(config)]
    self_val = config[proc]
    right = config[(proc + 1) % len(config)]
    updated[proc] = fs[proc](left, self_val, right)
    return tuple(updated)


def maximal_closed_single_privileged_subset(
    ms: list[int], fs: list[StepFn]
) -> tuple[set[Config], dict[Config, tuple[Config, int]]]:
    configs = list(product(*(range(m) for m in ms)))
    single_priv: set[Config] = set()
    succ: dict[Config, tuple[Config, int]] = {}

    for config in configs:
        privs = privileged_processors(config, fs)
        if len(privs) != 1:
            continue
        proc = privs[0]
        single_priv.add(config)
        succ[config] = (apply_move(config, proc, fs), proc)

    closed = set(single_priv)
    changed = True
    while changed:
        changed = False
        bad = {config for config in closed if succ[config][0] not in closed}
        if bad:
            closed -= bad
            changed = True

    return closed, succ


def enumerate_cycles(
    closed: set[Config], succ: dict[Config, tuple[Config, int]]
) -> list[CycleInfo]:
    seen: set[Config] = set()
    cycles: list[CycleInfo] = []

    for start in sorted(closed):
        if start in seen:
            continue
        local_index: dict[Config, int] = {}
        path: list[Config] = []
        node = start
        while node not in seen and node not in local_index:
            local_index[node] = len(path)
            path.append(node)
            node = succ[node][0]

        if node in local_index:
            cycle_configs = tuple(path[local_index[node] :])
            cycle_movers = tuple(succ[c][1] for c in cycle_configs)
            cycles.append(CycleInfo(cycle_configs, cycle_movers))

        seen.update(path)

    return cycles


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def sandwiched_ternaries(ms: list[int]) -> list[int]:
    n = len(ms)
    return [
        t
        for t in range(n)
        if ms[t] == 3 and ms[(t - 1) % n] == 2 and ms[(t + 1) % n] == 2
    ]


def hk_last_hits(movers: tuple[int, ...], t: int, n: int) -> list[int]:
    local = local_five(t, n)
    outside = [k for k, mover in enumerate(movers) if mover not in local]
    return [k for k in outside if k + 1 == len(movers)]


def summarize_cycle(cycle: CycleInfo, pivots: list[int]) -> list[str]:
    n = len(cycle.configs[0])
    lines = [
        f"    length={cycle.length} fair={cycle.fair}",
        f"    movers={cycle.movers}",
        f"    start={cycle.configs[0]}",
    ]
    if not pivots:
        lines.append("    no sandwiched ternary `t`; `hbL`/`hbR` cannot be instantiated")
        lines.append("    `allNormalForm`, `hk_last`, and every HardResidue branch are vacuous")
        return lines

    for t in pivots:
        hits = hk_last_hits(cycle.movers, t, n)
        lines.append(f"    t={t}: hk_last_hits={hits}")
    return lines


def analyze_n(n: int) -> None:
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    closed, succ = maximal_closed_single_privileged_subset(ms, fs)
    cycles = enumerate_cycles(closed, succ)
    fair_cycles = [cycle for cycle in cycles if cycle.fair]
    pivots = sandwiched_ternaries(ms)

    print(f"n={n}")
    print(f"  ms={tuple(ms)}")
    print(f"  verify.valid={result['valid']}")
    print(f"  verify.cycle_length={result.get('cycle_length')}")
    print(f"  closed_single_privileged={len(closed)}")
    print(f"  cycles_in_closed_subgraph={len(cycles)}")
    print(f"  fair_cycles={len(fair_cycles)}")
    print(f"  sandwiched_ternaries={pivots}")
    if not pivots:
        print("  theorem pivot hypothesis fails: no ternary has binary neighbors on both sides")
    for idx, cycle in enumerate(cycles, start=1):
        print(f"  cycle[{idx}]")
        for line in summarize_cycle(cycle, pivots):
            print(line)
    print()


def main() -> None:
    for n in (5, 6, 7):
        analyze_n(n)


if __name__ == "__main__":
    main()
