#!/usr/bin/env python3
"""
Path A L4d per-sandwich probe.

For each Path A pivot cycle, for each sandwiched ternary `i`, check
whether `i` has at least one stay step (consecutive i-fires). The L4d
analytical argument (case 1) closes when every sandwich ternary has
a stay; the case 2 (no-stay) sub-case requires an independent
contradiction argument.

Outputs per family:
  - cycles where every sandwich-T has a stay
  - cycles where some sandwich-T has no stay
  - example "no-stay" sandwich-T sites
"""

from __future__ import annotations

import importlib.util
import sys
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


def sandwiched_indices(ms):
    n = len(ms)
    out = []
    for i in range(n):
        if ms[i] == 3 and ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2:
            out.append(i)
    return out


def has_stay_at(word, i):
    L = len(word)
    for k in range(L):
        if word[k] == i and word[(k + 1) % L] == i:
            return True
    return False


def main():
    print("=" * 70)
    print("Path A L4d per-sandwich probe")
    print("=" * 70)
    print()

    grand_total = 0
    grand_all_have_stay = 0
    grand_some_no_stay = 0

    for fam in UNIV.FAMILIES:
        sandwiches = sandwiched_indices(fam.ms)
        if not sandwiches:
            print(f"### {fam.label} — no sandwiched ternaries, skipping")
            print()
            continue
        words = UNIV.path_a_population(fam)
        all_stay = 0
        some_no_stay = 0
        no_stay_examples = []
        for word in words:
            statuses = {i: has_stay_at(word, i) for i in sandwiches}
            if all(statuses.values()):
                all_stay += 1
            else:
                some_no_stay += 1
                if len(no_stay_examples) < 3:
                    no_stay_examples.append((list(word), statuses))
        grand_total += len(words)
        grand_all_have_stay += all_stay
        grand_some_no_stay += some_no_stay
        print(f"### {fam.label}")
        print(f"  ms: {fam.ms}")
        print(f"  sandwiched ternaries: {sandwiches}")
        print(f"  population: {len(words)}")
        print(f"  cycles where every sandwich-T has a stay: {all_stay}")
        print(f"  cycles where some sandwich-T has NO stay: {some_no_stay}")
        if no_stay_examples:
            for word, statuses in no_stay_examples:
                print(f"    example word={word} statuses={statuses}")
        print()

    print("=" * 70)
    print(f"Grand total (sandwich-having families only): {grand_total}")
    print(f"All sandwich-T have stay:    {grand_all_have_stay}")
    print(f"Some sandwich-T has no stay: {grand_some_no_stay}")
    if grand_some_no_stay == 0:
        print()
        print("VERDICT: every sandwich-T in every Path A pivot cycle has a stay.")
        print("L4d closes via case 1 (stay forces empty/zero arc → not (1,1,0)).")
    else:
        print()
        print(f"VERDICT: {grand_some_no_stay} cycles have a sandwich-T with no stay.")
        print("The no-stay sub-case of L4d is still open.")
    print("=" * 70)


if __name__ == "__main__":
    main()
