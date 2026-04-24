#!/usr/bin/env python3
"""
Path A L4 distribution probe.

Runs on the 46,679-cycle Path A population from
`path_a_witness_search_universal.py` and checks the L4 double-(1,1,0)
failure pattern on ternaries with two binary neighbors.
"""

from __future__ import annotations

import importlib.util
import itertools
import sys
from collections import Counter
from dataclasses import dataclass
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


@dataclass(frozen=True)
class TripleRecord:
    i: int
    fires: tuple[int, int, int]
    left_counts: tuple[int, int, int]
    right_counts: tuple[int, int, int]


def fire_steps(word, i: int):
    return [k for k, p in enumerate(word) if p == i]


def interval_fire_count(word, q: int, lo: int, hi: int) -> int:
    return sum(1 for k in range(lo, hi) if word[k] == q)


def arc_counts(word, q: int, f0: int, f1: int, f2: int):
    c0 = interval_fire_count(word, q, f0 + 1, f1)
    c1 = interval_fire_count(word, q, f1 + 1, f2)
    cw = interval_fire_count(word, q, 0, f0) + interval_fire_count(word, q, f2 + 1, len(word))
    return (c0, c1, cw)


def candidate_sites(ms: tuple[int, ...]):
    n = len(ms)
    out = []
    for i, m in enumerate(ms):
        if m != 3:
            continue
        if ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2:
            out.append(i)
    return out


def triples_for_site(word, i: int):
    fires = fire_steps(word, i)
    if len(fires) < 3:
        return []
    if len(fires) == 3:
        return [tuple(fires)]
    return list(itertools.combinations(fires, 3))


def linear_witness_for_triple(word, ms, n, i: int, triple: tuple[int, int, int]) -> bool:
    f0, f1, f2 = triple
    for a1, a2 in ((f0, f1), (f1, f2)):
        for k2 in range(a1 + 1, a2):
            if WITNESS.check_witness(word, ms, n, i, a1, a2, k2) is not None:
                return True
    return False


def analyze_family(fam):
    words = UNIV.path_a_population(fam)
    candidate_cycle_count = 0
    failure_cycle_count = 0
    linear_cycle_count = 0
    triple_count = 0
    failure_triple_count = 0
    linear_ok_triple_count = 0
    failure_examples = []
    linear_miss_examples = []
    site_hist = Counter()

    for word in words:
        cycle_has_candidate = False
        cycle_has_failure = False
        cycle_has_linear = False
        for i in candidate_sites(fam.ms):
            for triple in triples_for_site(word, i):
                cycle_has_candidate = True
                triple_count += 1
                site_hist[i] += 1
                f0, f1, f2 = triple
                li = (i - 1) % fam.n
                ri = (i + 1) % fam.n
                left = arc_counts(word, li, f0, f1, f2)
                right = arc_counts(word, ri, f0, f1, f2)
                bad = left == (1, 1, 0) and right == (1, 1, 0)
                if bad:
                    failure_triple_count += 1
                    cycle_has_failure = True
                    if len(failure_examples) < 5:
                        failure_examples.append(
                            {
                                "word": list(word),
                                "record": TripleRecord(i, triple, left, right),
                            }
                        )
                else:
                    if linear_witness_for_triple(word, fam.ms, fam.n, i, triple):
                        linear_ok_triple_count += 1
                        cycle_has_linear = True
        if cycle_has_candidate:
            candidate_cycle_count += 1
        if cycle_has_linear:
            linear_cycle_count += 1
        if cycle_has_failure:
            failure_cycle_count += 1
        if cycle_has_candidate and (not cycle_has_failure) and (not cycle_has_linear):
            if len(linear_miss_examples) < 5:
                linear_miss_examples.append(list(word))

    return {
        "population": len(words),
        "candidate_cycles": candidate_cycle_count,
        "failure_cycles": failure_cycle_count,
        "linear_cycles": linear_cycle_count,
        "triple_count": triple_count,
        "failure_triples": failure_triple_count,
        "linear_ok_triples": linear_ok_triple_count,
        "site_hist": site_hist,
        "failure_examples": failure_examples,
        "linear_miss_examples": linear_miss_examples,
    }


def main():
    grand_population = 0
    grand_candidate_cycles = 0
    grand_failure_cycles = 0
    grand_linear_cycles = 0
    grand_triples = 0
    grand_failure_triples = 0
    grand_linear_ok = 0
    examples = []
    linear_miss_examples = []

    print("=" * 70)
    print("Path A L4 distribution probe")
    print("=" * 70)
    print()

    for fam in UNIV.FAMILIES:
        res = analyze_family(fam)
        grand_population += res["population"]
        grand_candidate_cycles += res["candidate_cycles"]
        grand_failure_cycles += res["failure_cycles"]
        grand_linear_cycles += res["linear_cycles"]
        grand_triples += res["triple_count"]
        grand_failure_triples += res["failure_triples"]
        grand_linear_ok += res["linear_ok_triples"]
        examples.extend((fam.label, ex) for ex in res["failure_examples"])
        linear_miss_examples.extend((fam.label, ex) for ex in res["linear_miss_examples"])

        print(f"### {fam.label}")
        print(f"  path-a population: {res['population']}")
        print(f"  candidate cycles (has sandwiched ternary): {res['candidate_cycles']}")
        print(f"  candidate cycles with >=1 linear witness at such a ternary: {res['linear_cycles']}")
        print(f"  candidate triples: {res['triple_count']}")
        print(f"  Q1 failure cycles: {res['failure_cycles']}")
        print(f"  Q1 failure triples: {res['failure_triples']}")
        print(f"  Q2 linear-witness nonfailure triples: {res['linear_ok_triples']} / {res['triple_count'] - res['failure_triples']}")
        if res["site_hist"]:
            print(f"  candidate-site histogram: {dict(res['site_hist'])}")
        else:
            print("  candidate-site histogram: {}")
        print()

    print("=" * 70)
    print(f"Grand population: {grand_population}")
    print(f"Candidate cycles: {grand_candidate_cycles}")
    print(f"Candidate cycles with >=1 linear witness: {grand_linear_cycles}")
    print(f"Candidate triples: {grand_triples}")
    print(f"Q1 total failure cycles: {grand_failure_cycles}")
    print(f"Q1 total failure triples: {grand_failure_triples}")
    print(f"Q2 total linear-witness nonfailure triples: {grand_linear_ok} / {grand_triples - grand_failure_triples}")
    if grand_failure_cycles:
        print("Q3 examples:")
        for fam_label, ex in examples[:5]:
            rec = ex["record"]
            print(f"  family={fam_label}")
            print(f"  word={ex['word']}")
            print(f"  i={rec.i}, fires={rec.fires}, left={rec.left_counts}, right={rec.right_counts}")
    else:
        print("Q3 examples: none")
    if linear_miss_examples:
        print("Q2 linear-miss cycle examples:")
        for fam_label, ex in linear_miss_examples[:5]:
            print(f"  family={fam_label}")
            print(f"  word={ex}")
    print("=" * 70)


if __name__ == "__main__":
    main()
