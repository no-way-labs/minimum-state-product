#!/usr/bin/env python3
"""Shadow-trap checks at n=7 and n=8 using stored verified witnesses.

This follows the same pattern as ra_shadow_m5.py:
1. Build a known witness
2. Verify it with verifier.verify_system()
3. Extract the verified good cycle
4. Flip processors 0 and 2 in each cycle config
5. Check whether the flipped shadow always has some privileged processor

Notes:
- For n=7, we rotate the stored verified witness so the binary block is
  exactly P0,P1,P2, matching the user's requested P0/P2 flip.
- For n=8, the stored verified M_8 witness in this repo is
  ms=(2,2,3,4,3,3,2,3), not a consecutive-binary witness. We still report
  the P0/P2 flip result after a rotation that makes both P0 and P2 binary,
  but this is only a supplemental distance-2 binary test, not the exact
  consecutive-binary geometry requested in the task text.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from n9_templated_search import witness_n7, witness_n8
from verifier import privileged_set, verify_system


FLIP_PROCS = (0, 2)


@dataclass(frozen=True)
class WitnessSpec:
    label: str
    ms: tuple[int, ...]
    rules: tuple[dict[tuple[int, int, int], int], ...]
    note: str = ""


def rotate_ring(
    ms: tuple[int, ...],
    rules: tuple[dict[tuple[int, int, int], int], ...],
    shift: int,
) -> tuple[tuple[int, ...], tuple[dict[tuple[int, int, int], int], ...]]:
    """Rotate a ring left by shift positions."""
    n = len(ms)
    shift %= n
    return (
        tuple(ms[(i + shift) % n] for i in range(n)),
        tuple(rules[(i + shift) % n] for i in range(n)),
    )


def make_fs(
    rules: tuple[dict[tuple[int, int, int], int], ...],
):
    fs = []
    for table in rules:
        def make_f(t):
            def f(left, self_state, right):
                return t[(left, self_state, right)]
            return f
        fs.append(make_f(table))
    return fs


def rotate_cycle(
    cycle: list[tuple[int, ...]],
    start: tuple[int, ...],
) -> list[tuple[int, ...]]:
    if start not in cycle:
        return cycle
    idx = cycle.index(start)
    return cycle[idx:] + cycle[:idx]


def flip_shadow(config: tuple[int, ...], procs: Iterable[int]) -> tuple[int, ...]:
    shadow = list(config)
    for proc in procs:
        shadow[proc] = 1 - shadow[proc]
    return tuple(shadow)


def analyze_witness(spec: WitnessSpec) -> dict:
    fs = make_fs(spec.rules)
    result = verify_system(list(spec.ms), fs, verbose=False)
    if not result["valid"]:
        raise RuntimeError(f"{spec.label} failed verify_system()")

    cycle = rotate_cycle(list(result["cycle"]), (0,) * len(spec.ms))

    live_shadow_steps = 0
    failing_steps = []
    step_rows = []
    for step, config in enumerate(cycle):
        shadow = flip_shadow(config, FLIP_PROCS)
        privs = privileged_set(shadow, fs, list(spec.ms))
        if privs:
            live_shadow_steps += 1
        else:
            failing_steps.append((step, config, shadow))
        step_rows.append((step, config, shadow, privs))

    return {
        "label": spec.label,
        "note": spec.note,
        "ms": spec.ms,
        "binary_positions": [i for i, m in enumerate(spec.ms) if m == 2],
        "verify": result,
        "cycle": cycle,
        "step_rows": step_rows,
        "live_shadow_steps": live_shadow_steps,
        "failing_steps": failing_steps,
    }


def print_report(report: dict) -> None:
    verify = report["verify"]
    print(report["label"])
    print("=" * len(report["label"]))
    print(f"ms = {report['ms']}")
    print(f"binary positions = {report['binary_positions']}")
    print(f"flip processors = {FLIP_PROCS}")
    print(f"verify_system.valid = {verify['valid']}")
    print(f"verify_system.good_configs = {len(verify['good_configs'])}")
    print(f"verify_system.cycle_length = {verify['cycle_length']}")
    if report["note"]:
        print(f"note = {report['note']}")
    print()
    print("Cycle-step shadow privilege check:")
    for step, config, shadow, privs in report["step_rows"]:
        print(f"  step {step:2d}: config={config} shadow={shadow} privileged={privs}")
    print()
    print(
        f"Cycle result: {report['live_shadow_steps']}/{len(report['cycle'])} cycle steps "
        "have some privileged processor in the shadow."
    )
    if report["failing_steps"]:
        print("Failing steps:")
        for step, config, shadow in report["failing_steps"]:
            print(f"  step {step}: config={config} shadow={shadow} privileged=[]")
    else:
        print("Failing steps: none")
    print()


def main() -> None:
    # n=7: rotate the stored witness so the binary block is P0,P1,P2.
    ms7, rules7 = witness_n7()
    ms7_rot, rules7_rot = rotate_ring(ms7, rules7, shift=1)
    report7 = analyze_witness(
        WitnessSpec(
            label="n=7 consecutive-binary test (rotated verified witness)",
            ms=ms7_rot,
            rules=rules7_rot,
            note="Stored witness rotated by 1 so binaries are exactly P0,P1,P2.",
        )
    )
    print_report(report7)

    # n=8: the stored verified witness is not consecutive-binary. Rotate it so
    # P0 and P2 are binary and report the same flip as a supplemental test.
    ms8, rules8 = witness_n8()
    ms8_rot, rules8_rot = rotate_ring(ms8, rules8, shift=6)
    report8 = analyze_witness(
        WitnessSpec(
            label="n=8 stored-witness distance-2 binary test (supplemental)",
            ms=ms8_rot,
            rules=rules8_rot,
            note=(
                "This repo's verified M_8 witness is not a consecutive-binary witness. "
                "After rotation, P0 and P2 are binary, but P1 is ternary."
            ),
        )
    )
    print_report(report8)

    print("Summary")
    print("=======")
    print(
        f"n=7 consecutive-binary shadow result: "
        f"{report7['live_shadow_steps']}/{len(report7['cycle'])}"
    )
    print(
        f"n=8 stored-witness supplemental result: "
        f"{report8['live_shadow_steps']}/{len(report8['cycle'])}"
    )
    print(
        "Repo note: no verified consecutive-binary n=8 witness is stored here; "
        "the verified M_8 witness in the repo is ms=(2,2,3,4,3,3,2,3)."
    )


if __name__ == "__main__":
    main()
