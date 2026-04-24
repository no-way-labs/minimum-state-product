#!/usr/bin/env python3
"""
Path A stay-step probe.

For each Path A family, count how many cycles contain a "stay step"
(consecutive movers equal: word[k] == word[(k+1) % L]). If the answer
is zero everywhere, then `stayStepCount = 0` is universally true on
the Path A min-CL population, which closes L4d analytically:

  L4d (double-(1,1,0)) requires the wrap arc to be empty (f_0 = 0,
  f_2 = L - 1), which forces moverAt 0 = moverAt(L - 1) = i. The
  cyclic wrap step from L - 1 to 0 then has both endpoints at i,
  i.e., a stay step. If stay steps don't occur, this is a
  contradiction, and L4d holds.
"""

from __future__ import annotations

import importlib.util
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


UNIV = load_module(
    "path_a_universal",
    ROOT / "probes/branch_b_bypass/path_a_witness_search_universal.py",
)


def stay_steps(word):
    """Count k in [0, L) with word[k] == word[(k + 1) % L]."""
    L = len(word)
    return sum(1 for k in range(L) if word[k] == word[(k + 1) % L])


def main():
    print("=" * 70)
    print("Path A stay-step probe")
    print("=" * 70)
    print()

    grand_total = 0
    grand_with_stay = 0
    grand_total_stays = 0

    for fam in UNIV.FAMILIES:
        words = UNIV.path_a_population(fam)
        with_stay = 0
        max_stay = 0
        total_stay_steps = 0
        for word in words:
            s = stay_steps(word)
            if s > 0:
                with_stay += 1
                if s > max_stay:
                    max_stay = s
            total_stay_steps += s
        grand_total += len(words)
        grand_with_stay += with_stay
        grand_total_stays += total_stay_steps
        print(f"### {fam.label}")
        print(f"  population: {len(words)}")
        print(f"  cycles with at least one stay step: {with_stay}")
        print(f"  total stay steps across all cycles: {total_stay_steps}")
        print(f"  max stay steps in a single cycle: {max_stay}")
        print()

    print("=" * 70)
    print(f"Grand total population: {grand_total}")
    print(f"Grand total cycles with stay steps: {grand_with_stay}")
    print(f"Grand total stay steps: {grand_total_stays}")
    print("=" * 70)

    if grand_with_stay == 0:
        print("VERDICT: Path A min-CL good cycles have ZERO stay steps universally.")
        print("Implication: stayStepCount = 0 on the Path A population,")
        print("which closes L4d (double-(1,1,0) impossibility) analytically.")
    else:
        print(f"VERDICT: {grand_with_stay} cycles have stay steps.")
        print("L4d cannot be closed via the no-stay route.")
    print("=" * 70)


if __name__ == "__main__":
    main()
