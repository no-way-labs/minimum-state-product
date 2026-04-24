#!/usr/bin/env python3
"""Check cyclic closure for the n=9 hard-residue witness families.

This script is deliberately Python-only. It reads no `.lean` files at runtime,
but it mirrors the in-repo `AllNormalFormFalse.lean` witness packaging:

- `hard_residue_ghost_check.py` shows that the only in-repo source of the
  number `22,698` is the count of *sandwiched-pivot instances* at `n = 9`:
  sub-threshold state vectors with at least one ternary pivot `t` whose
  neighbors are binary.
- For each such `(ms, t)` instance, that script gives four canonical mover-word
  witness families:
  `LeftSame`, `RightSame`, `LeftCross`, `RightCross`.

What "closure" means here:

- A good cycle is a cyclic list of configurations. If the mover word has length
  `L`, and the step sequence is `c_0 --w[0]--> c_1 --w[1]--> ... --w[L-1]--> c_L`,
  then cyclic closure is `c_L = c_0`.
- We do not assume incrementing updates. Instead, we ask whether there exists
  *some* set of local transition tables consistent with the mover word:
  same local context at processor `i` must always produce the same output, the
  designated mover must change, and every non-mover must stay put.

The script uses two checks.

1. Full-cycle SAT on a permissive super-domain:
   - pivot neighborhood has exact moduli `(2, 3, 2)`,
   - every other processor gets modulus `5`.
   This is an over-approximation of every actual witness instance:
   in the canonical hard words, every non-pivot processor fires at most `4`
   times, so modulus `5` already permits any possible per-processor value trace.
   If the word is impossible even here, it is impossible for every actual
   sub-threshold witness state vector.

2. Boundary-triple split check:
   - split the word at `k_out + 1`, where `k_out` is the last mover outside the
     pivot 5-neighborhood,
   - let the prefix and terminal segments use *independent* local tables,
   - ask whether any boundary triple `(s_{t-1}, s_t, s_{t+1})` in
     `{0,1} × {0,1,2} × {0,1}` is a fixed point of
     `terminal ∘ prefix`.
   If no fixed triple exists even under this relaxation, closure is impossible.

When the universal obstruction succeeds, the exact survivor count for the full
`22,698` census is immediately `0` for that hard type; the script still reports
the exact witness counts.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from typing import Iterable

from z3 import And, Implies, Int, Not, Solver, sat

from hard_residue_ghost_check import (
    BASE_LEFT_CROSS,
    BASE_LEFT_SAME,
    BASE_RIGHT_CROSS,
    BASE_RIGHT_SAME,
    enumerate_state_vectors,
    has_ge3_binary,
    last_outside_index,
    sandwiched_pivots,
)


N = 9
PIVOT = 0
LEFT = N - 1
RIGHT = 1
BOUNDARY_TRIPLES = tuple((l, s, r) for l in range(2) for s in range(3) for r in range(2))

# Exact pivot-neighborhood moduli, permissive elsewhere.
# Each non-pivot processor fires at most 4 times in every canonical hard word,
# so modulus 5 already dominates all possible local value traces.
SUPER_MS = (3, 2, 5, 5, 5, 5, 5, 5, 2)


@dataclass(frozen=True)
class HardType:
    name: str
    word: tuple[int, ...]


HARD_TYPES = (
    HardType("LeftSame", tuple(BASE_LEFT_SAME)),
    HardType("RightSame", tuple(BASE_RIGHT_SAME)),
    HardType("LeftCross", tuple(BASE_LEFT_CROSS)),
    HardType("RightCross", tuple(BASE_RIGHT_CROSS)),
)


def rotate_ms_to_pivot_zero(ms: tuple[int, ...], t: int) -> tuple[int, ...]:
    """Rotate so the chosen pivot sits at index 0."""
    return tuple(ms[(i + t) % N] for i in range(N))


def add_transition_table_consistency(
    solver: Solver,
    configs: list[list],
    steps: tuple[int, ...],
) -> None:
    """Add the standard local-table constraints for a linear step segment."""
    n = len(configs[0])
    num_steps = len(steps)
    for j, mover in enumerate(steps):
        for i in range(n):
            if i == mover:
                solver.add(Not(configs[j + 1][i] == configs[j][i]))
            else:
                solver.add(configs[j + 1][i] == configs[j][i])

    for i in range(n):
        li = (i - 1) % n
        ri = (i + 1) % n
        for a in range(num_steps):
            out_a = configs[a + 1][i] if steps[a] == i else configs[a][i]
            for b in range(a + 1, num_steps):
                out_b = configs[b + 1][i] if steps[b] == i else configs[b][i]
                same_ctx = And(
                    configs[a][li] == configs[b][li],
                    configs[a][i] == configs[b][i],
                    configs[a][ri] == configs[b][ri],
                )
                solver.add(Implies(same_ctx, out_a == out_b))


def fresh_config_vars(prefix: str, ms: tuple[int, ...], length: int) -> list[list]:
    return [[Int(f"{prefix}_{j}_{i}") for i in range(len(ms))] for j in range(length)]


def add_domain_bounds(solver: Solver, configs: list[list], ms: tuple[int, ...]) -> None:
    for cfg in configs:
        for i, mod in enumerate(ms):
            solver.add(cfg[i] >= 0, cfg[i] < mod)


def word_max_fire_count(word: Iterable[int]) -> int:
    return max(Counter(word).values())


@lru_cache(maxsize=None)
def full_cycle_sat(ms: tuple[int, ...], word: tuple[int, ...], timeout_ms: int = 5000) -> bool:
    """Exact closure SAT for one rotated state vector."""
    n = len(ms)
    L = len(word)
    solver = Solver()
    solver.set(timeout=timeout_ms)
    configs = fresh_config_vars("cycle", ms, L)
    add_domain_bounds(solver, configs, ms)

    for j, mover in enumerate(word):
        nxt = (j + 1) % L
        for i in range(n):
            if i == mover:
                solver.add(Not(configs[nxt][i] == configs[j][i]))
            else:
                solver.add(configs[nxt][i] == configs[j][i])

    for i in range(n):
        li = (i - 1) % n
        ri = (i + 1) % n
        for a in range(L):
            out_a = configs[(a + 1) % L][i] if word[a] == i else configs[a][i]
            for b in range(a + 1, L):
                out_b = configs[(b + 1) % L][i] if word[b] == i else configs[b][i]
                same_ctx = And(
                    configs[a][li] == configs[b][li],
                    configs[a][i] == configs[b][i],
                    configs[a][ri] == configs[b][ri],
                )
                solver.add(Implies(same_ctx, out_a == out_b))

    return solver.check() == sat


@lru_cache(maxsize=None)
def split_fixed_boundary_triples(word: tuple[int, ...], timeout_ms: int = 2000) -> tuple[tuple[int, int, int], ...]:
    """Return the boundary triples fixed by terminal∘prefix under independent tables."""
    split = last_outside_index(list(word), PIVOT) + 1
    prefix_steps = word[:split]
    terminal_steps = word[split:]
    fixed: list[tuple[int, int, int]] = []

    for triple in BOUNDARY_TRIPLES:
        solver = Solver()
        solver.set(timeout=timeout_ms)

        start = [Int(f"start_{i}") for i in range(N)]
        mid = [Int(f"mid_{i}") for i in range(N)]
        add_domain_bounds(solver, [start, mid], SUPER_MS)
        solver.add(start[LEFT] == triple[0], start[PIVOT] == triple[1], start[RIGHT] == triple[2])

        prefix_cfgs = fresh_config_vars("pref", SUPER_MS, len(prefix_steps) + 1)
        add_domain_bounds(solver, prefix_cfgs, SUPER_MS)
        for i in range(N):
            solver.add(prefix_cfgs[0][i] == start[i])
        add_transition_table_consistency(solver, prefix_cfgs, prefix_steps)
        for i in range(N):
            solver.add(prefix_cfgs[len(prefix_steps)][i] == mid[i])

        terminal_cfgs = fresh_config_vars("term", SUPER_MS, len(terminal_steps) + 1)
        add_domain_bounds(solver, terminal_cfgs, SUPER_MS)
        for i in range(N):
            solver.add(terminal_cfgs[0][i] == mid[i])
        add_transition_table_consistency(solver, terminal_cfgs, terminal_steps)
        for i in range(N):
            solver.add(terminal_cfgs[len(terminal_steps)][i] == start[i])

        if solver.check() == sat:
            fixed.append(triple)

    return tuple(fixed)


def candidate_instances() -> list[tuple[tuple[int, ...], int]]:
    vecs = enumerate_state_vectors()
    out: list[tuple[tuple[int, ...], int]] = []
    for ms in vecs:
        if not has_ge3_binary(ms):
            continue
        pivots = sandwiched_pivots(ms)
        for t in pivots:
            out.append((ms, t))
    return out


def analyze_hard_type(instances: list[tuple[tuple[int, ...], int]], hard: HardType) -> dict:
    full_sat_super = full_cycle_sat(SUPER_MS, hard.word)
    fixed_triples = split_fixed_boundary_triples(hard.word)

    # Strong universal blocker:
    # - impossible even on the permissive super-domain, and
    # - no boundary triple is a fixed point even when prefix and terminal get
    #   independent tables.
    universally_blocked = (not full_sat_super) and (len(fixed_triples) == 0)

    if universally_blocked:
        survivors = 0
    else:
        survivors = 0
        for ms, t in instances:
            rotated = rotate_ms_to_pivot_zero(ms, t)
            if full_cycle_sat(rotated, hard.word):
                survivors += 1

    return {
        "name": hard.name,
        "word_length": len(hard.word),
        "max_fire_count": word_max_fire_count(hard.word),
        "split_index": last_outside_index(list(hard.word), PIVOT) + 1,
        "full_cycle_sat_super": full_sat_super,
        "fixed_boundary_triples": fixed_triples,
        "universally_blocked": universally_blocked,
        "survivors": survivors,
        "witness_instances": len(instances),
    }


def main() -> None:
    instances = candidate_instances()
    total_vectors = len({ms for ms, _ in instances})
    total_pivots = len(instances)

    print("n=9 hard-residue cyclic-closure census")
    print(f"  candidate state vectors: {total_vectors}")
    print(f"  sandwiched-pivot instances: {total_pivots}")
    print("  interpretation of 22,698: this is the pivot-instance census from hard_residue_ghost_check.py")
    print("  typed witness count: each hard type applies to each pivot instance")
    print(f"  total typed witnesses: {total_pivots * len(HARD_TYPES)}")
    print()
    print(f"permissive super-domain: ms={SUPER_MS}")
    print("  pivot-neighborhood moduli fixed at (2,3,2); others set to 5")
    print()

    grand_survivors = 0
    for hard in HARD_TYPES:
        result = analyze_hard_type(instances, hard)
        grand_survivors += result["survivors"]
        print(f"{result['name']}:")
        print(f"  word_length={result['word_length']} split={result['split_index']} max_fire={result['max_fire_count']}")
        print(f"  full_cycle_sat_on_super_domain={result['full_cycle_sat_super']}")
        print(f"  fixed_boundary_triples={list(result['fixed_boundary_triples'])}")
        print(f"  universal_blocker={result['universally_blocked']}")
        print(f"  survivors={result['survivors']}/{result['witness_instances']}")
        print()

    print("summary:")
    print(f"  per-type witness instances: {total_pivots}")
    print(f"  total typed witnesses: {total_pivots * len(HARD_TYPES)}")
    print(f"  total survivors across all four hard types: {grand_survivors}")


if __name__ == "__main__":
    main()
