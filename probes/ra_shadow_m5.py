#!/usr/bin/env python3
"""Test the binary-flip shadow condition on the known M_5=96 witness."""

from __future__ import annotations

from typing import Iterable

from verifier import all_configs, privileged_set, verify_system


MS = [2, 2, 2, 3, 4]
START_CONFIG = (0, 0, 0, 0, 0)
FLIP_PROCS = (0, 2)


def build_m5_96_witness():
    """Return the known valid M_5=96 witness system."""
    tables = [
        {
            (0, 0, 0): 1,
            (0, 0, 1): 0,
            (0, 1, 0): 1,
            (0, 1, 1): 1,
            (1, 0, 0): 0,
            (1, 0, 1): 0,
            (1, 1, 0): 0,
            (1, 1, 1): 0,
            (2, 0, 0): 0,
            (2, 0, 1): 0,
            (2, 1, 0): 0,
            (2, 1, 1): 0,
            (3, 0, 0): 0,
            (3, 0, 1): 0,
            (3, 1, 0): 0,
            (3, 1, 1): 0,
        },
        {
            (0, 0, 0): 0,
            (0, 0, 1): 0,
            (0, 1, 0): 0,
            (0, 1, 1): 0,
            (1, 0, 0): 1,
            (1, 0, 1): 1,
            (1, 1, 0): 1,
            (1, 1, 1): 1,
        },
        {
            (0, 0, 0): 0,
            (0, 0, 1): 0,
            (0, 0, 2): 1,
            (0, 1, 0): 1,
            (0, 1, 1): 0,
            (0, 1, 2): 1,
            (1, 0, 0): 1,
            (1, 0, 1): 0,
            (1, 0, 2): 0,
            (1, 1, 0): 1,
            (1, 1, 1): 1,
            (1, 1, 2): 0,
        },
        {
            (0, 0, 0): 0,
            (0, 0, 1): 0,
            (0, 0, 2): 1,
            (0, 0, 3): 0,
            (0, 1, 0): 1,
            (0, 1, 1): 2,
            (0, 1, 2): 1,
            (0, 1, 3): 0,
            (0, 2, 0): 0,
            (0, 2, 1): 2,
            (0, 2, 2): 2,
            (0, 2, 3): 2,
            (1, 0, 0): 1,
            (1, 0, 1): 0,
            (1, 0, 2): 2,
            (1, 0, 3): 0,
            (1, 1, 0): 1,
            (1, 1, 1): 1,
            (1, 1, 2): 1,
            (1, 1, 3): 1,
            (1, 2, 0): 2,
            (1, 2, 1): 0,
            (1, 2, 2): 2,
            (1, 2, 3): 1,
        },
        {
            (0, 0, 0): 0,
            (0, 0, 1): 0,
            (0, 1, 0): 2,
            (0, 1, 1): 1,
            (0, 2, 0): 2,
            (0, 2, 1): 2,
            (0, 3, 0): 0,
            (0, 3, 1): 1,
            (1, 0, 0): 0,
            (1, 0, 1): 1,
            (1, 1, 0): 1,
            (1, 1, 1): 1,
            (1, 2, 0): 1,
            (1, 2, 1): 0,
            (1, 3, 0): 3,
            (1, 3, 1): 0,
            (2, 0, 0): 0,
            (2, 0, 1): 0,
            (2, 1, 0): 1,
            (2, 1, 1): 1,
            (2, 2, 0): 3,
            (2, 2, 1): 0,
            (2, 3, 0): 3,
            (2, 3, 1): 0,
        },
    ]

    fs = []
    for table in tables:
        def make_f(t):
            def f(left, self_state, right):
                return t[(left, self_state, right)]

            return f

        fs.append(make_f(table))
    return tables, fs


def rotate_cycle(cycle: list[tuple[int, ...]], start: tuple[int, ...]) -> list[tuple[int, ...]]:
    if start not in cycle:
        return cycle
    idx = cycle.index(start)
    return cycle[idx:] + cycle[:idx]


def flip_shadow(config: tuple[int, ...], procs: Iterable[int]) -> tuple[int, ...]:
    shadow = list(config)
    for proc in procs:
        shadow[proc] = 1 - shadow[proc]
    return tuple(shadow)


def main():
    tables, fs = build_m5_96_witness()
    result = verify_system(MS, fs, verbose=False)
    if not result["valid"]:
        raise SystemExit("M_5 witness failed verify_system(); aborting.")

    cycle = rotate_cycle(list(result["cycle"]), START_CONFIG)
    good_count = len(result["good_configs"])

    print("M_5=96 witness shadow test")
    print("=" * 60)
    print(f"ms = {MS}")
    print(f"verify_system.valid = {result['valid']}")
    print(f"verify_system.good_configs = {good_count}")
    print(f"verify_system.cycle_length = {result['cycle_length']}")
    print(f"flip processors = {FLIP_PROCS}")
    print()
    print("Transition table sizes:")
    for proc, table in enumerate(tables):
        print(f"  P{proc}: {len(table)} entries")

    print()
    print("Cycle-step shadow privilege check:")
    live_shadow_steps = 0
    failing_steps = []
    for step, config in enumerate(cycle):
        shadow = flip_shadow(config, FLIP_PROCS)
        privs = privileged_set(shadow, fs, MS)
        if privs:
            live_shadow_steps += 1
        else:
            failing_steps.append((step, config, shadow))
        print(
            f"  step {step:2d}: config={config} shadow={shadow} privileged={privs}"
        )

    print()
    print(
        f"Cycle result: {live_shadow_steps}/{len(cycle)} cycle steps have some privileged processor in the shadow."
    )
    if failing_steps:
        print("Failing steps:")
        for step, config, shadow in failing_steps:
            print(f"  step {step}: config={config} shadow={shadow} privileged=[]")
    else:
        print("Failing steps: none")

    # This addresses the task wording that refers to 96 steps. The actual good cycle
    # has length 18, but the flip map is a bijection on the full 96-config space.
    full_space_live = 0
    for config in all_configs(MS):
        shadow = flip_shadow(config, FLIP_PROCS)
        if privileged_set(shadow, fs, MS):
            full_space_live += 1

    print()
    print(
        f"Full-space result: {full_space_live}/96 flipped configs have some privileged processor."
    )
    print("Because the system is valid, liveness already forces this full-space count to be 96/96.")


if __name__ == "__main__":
    main()
