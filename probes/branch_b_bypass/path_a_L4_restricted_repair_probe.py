#!/usr/bin/env python3
"""
Path A L4 restricted repair probe.

Check the repaired claim:
  at a sandwiched ternary i, there is either a linear witness or a wrap witness.

Runs on the pivot-family slice of the Path A population.
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
WITNESS = load_module(
    "path_a_witness",
    ROOT / "probes/branch_b_bypass/path_a_witness_search.py",
)
L4 = load_module(
    "path_a_l4_probe",
    ROOT / "probes/branch_b_bypass/path_a_L4_distribution_probe.py",
)


TARGET_LABELS = {"n9 pivot alt", "n11 pivot 3bin"}


def cycle_status(word, fam):
    """Return (has_linear, has_wrap, witness_records)."""
    has_linear = False
    has_wrap = False
    records = []
    for i in L4.candidate_sites(fam.ms):
        triples = L4.triples_for_site(word, i)
        site_linear = False
        for triple in triples:
            if L4.linear_witness_for_triple(word, fam.ms, fam.n, i, triple):
                has_linear = True
                site_linear = True
                records.append(("linear", i, triple))
                break
        fires = L4.fire_steps(word, i)
        if len(fires) >= 2:
            wrap = WITNESS.check_wrap_witness(word, fam.ms, fam.n, i, fires[0], fires[-1])
            if wrap is not None:
                has_wrap = True
                records.append((wrap, i, (fires[0], fires[-1])))
    return has_linear, has_wrap, records


def main():
    print("=" * 70)
    print("Path A L4 restricted repair probe")
    print("=" * 70)
    print()

    grand_candidate = 0
    grand_linear = 0
    grand_wrap = 0
    grand_ok = 0
    failures = []

    for fam in UNIV.FAMILIES:
        if fam.label not in TARGET_LABELS:
            continue
        words = UNIV.path_a_population(fam)
        cand = 0
        lin = 0
        wrp = 0
        ok = 0
        fam_failures = []
        for word in words:
            if not L4.candidate_sites(fam.ms):
                continue
            cand += 1
            has_linear, has_wrap, records = cycle_status(word, fam)
            if has_linear:
                lin += 1
            if has_wrap:
                wrp += 1
            if has_linear or has_wrap:
                ok += 1
            else:
                if len(fam_failures) < 5:
                    fam_failures.append((list(word), records))
        grand_candidate += cand
        grand_linear += lin
        grand_wrap += wrp
        grand_ok += ok
        failures.extend((fam.label, word, recs) for word, recs in fam_failures)

        print(f"### {fam.label}")
        print(f"  candidate cycles: {cand}")
        print(f"  Q2a linear-hit cycles: {lin}")
        print(f"  Q2b wrap-hit cycles: {wrp}")
        print(f"  Q2c cycles with neither linear nor wrap: {cand - ok}")
        print()

    print("=" * 70)
    print(f"Grand candidate cycles: {grand_candidate}")
    print(f"Q2a total linear-hit cycles: {grand_linear}")
    print(f"Q2b total wrap-hit cycles: {grand_wrap}")
    print(f"Q2c total cycles with neither linear nor wrap: {grand_candidate - grand_ok}")
    if grand_candidate - grand_ok:
        print("Failure examples:")
        for fam_label, word, recs in failures[:5]:
            print(f"  family={fam_label}")
            print(f"  word={word}")
            print(f"  partial_records={recs}")
    else:
        print("Failure examples: none")
    print("=" * 70)


if __name__ == "__main__":
    main()
