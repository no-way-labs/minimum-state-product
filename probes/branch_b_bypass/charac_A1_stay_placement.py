#!/usr/bin/env python3
"""
Characterize ternary stay placement on the A1 residual population.

Search guidance only. Answers the questions in
`a1_residual_stay_placement_spec_2026-04-13.md`.
"""

from __future__ import annotations

import importlib.util
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


Prev = load_module(
    "a1_nonosc_residual", ROOT / "probes/branch_b_bypass/charac_A1_nonosc_residual.py"
)


def nearest_binary_distance(t: int, binaries: list[int], n: int) -> int:
    return min(min((t - b) % n, (b - t) % n) for b in binaries)


def ternary_class(ms: tuple[int, ...], t: int) -> str:
    left_bin = ms[(t - 1) % len(ms)] == 2
    right_bin = ms[(t + 1) % len(ms)] == 2
    cnt = int(left_bin) + int(right_bin)
    if cnt == 2:
        return "A"
    if cnt == 1:
        return "B"
    return "C"


def stay_positions(word, n: int) -> list[tuple[int, int]]:
    return [(k, word[k]) for k in range(len(word)) if Prev.step_dir(word, k, n) == "stay"]


def binary_fire_indices(word, ms: tuple[int, ...]) -> list[int]:
    return [k for k, p in enumerate(word) if ms[p] == 2]


def binary_interval_containing_stay(k: int, binary_steps: list[int]):
    prevs = [b for b in binary_steps if b < k]
    nexts = [b for b in binary_steps if b > k]
    if not prevs or not nexts:
        return None
    return (prevs[-1], nexts[0])


def highlighted_word(word, n: int) -> list[str]:
    stays = {k for k in range(len(word)) if Prev.step_dir(word, (k - 1) % len(word), n) == "stay"}
    out = []
    for k, p in enumerate(word):
        if k in stays:
            out.append(f"{p}*")
        else:
            out.append(str(p))
    return out


def characterize_cycle(word, fam):
    n = fam.n
    ms = fam.ms
    stays = stay_positions(word, n)
    binaries = Prev.binary_positions(ms)
    binary_steps = binary_fire_indices(word, ms)

    stay_proc_multiset = Counter(p for _, p in stays)
    per_stay = []
    interval_counts = Counter()
    class_presence = set()

    for k, t in stays:
        interval = binary_interval_containing_stay(k, binary_steps)
        if interval is not None:
            interval_counts[interval] += 1
        cls = ternary_class(ms, t)
        class_presence.add(cls)
        per_stay.append(
            {
                "step_index": k,
                "processor": t,
                "distance_to_nearest_binary": nearest_binary_distance(t, binaries, n),
                "is_binary_adjacent": cls in {"A", "B"},
                "class": cls,
                "binary_interval": interval,
                "direction_before": Prev.step_dir(word, (k - 1) % len(word), n),
                "direction_after": Prev.step_dir(word, (k + 1) % len(word), n),
            }
        )

    for item in per_stay:
        item["inside_monotone_block"] = (
            item["direction_before"] == item["direction_after"]
            and item["direction_before"] in {"cw", "ccw"}
        )

    max_interval = max(interval_counts.values(), default=0)
    max_one_ternary = max(stay_proc_multiset.values(), default=0)

    return {
        "word": word,
        "stay_positions": stays,
        "stay_processor_multiset": dict(stay_proc_multiset),
        "per_stay": per_stay,
        "max_stays_in_one_binary_interval": max_interval,
        "max_stays_at_one_ternary": max_one_ternary,
        "class_presence": class_presence,
        "highlighted_word": highlighted_word(word, n),
    }


def main():
    drift = []
    family_data = {}

    for fam in Prev.FAMILIES:
        words = Prev.residual_population(fam)
        if len(words) != fam.expected_residual:
            drift.append(f"{fam.label}: expected {fam.expected_residual}, got {len(words)}")
        cycles = [characterize_cycle(word, fam) for word in words]
        family_data[fam.label] = {"fam": fam, "cycles": cycles}

    if drift:
        print("DRIFT DETECTED: " + "; ".join(drift))
        return

    # Q5 verdict first
    class_totals = {}
    has_class_c = False
    has_class_b = False
    for fam in Prev.FAMILIES:
        totals = Counter()
        cycles = family_data[fam.label]["cycles"]
        for c in cycles:
            for s in c["per_stay"]:
                totals[s["class"]] += 1
        class_totals[fam.label] = totals
        if totals["C"] > 0:
            has_class_c = True
        if totals["B"] > 0:
            has_class_b = True

    if has_class_c:
        verdict = "any class C"
    elif has_class_b:
        verdict = "A+B"
    else:
        verdict = "class-A only"
    print(f"Verdict: {verdict}")
    print()

    # Q1
    for fam in Prev.FAMILIES:
        cycles = family_data[fam.label]["cycles"]
        d_hist = Counter()
        total_stays = 0
        adjacent = 0
        for c in cycles:
            for s in c["per_stay"]:
                total_stays += 1
                if s["is_binary_adjacent"]:
                    adjacent += 1
                d_hist[s["distance_to_nearest_binary"]] += 1
        print(f"Q1 {fam.label}: adjacent {adjacent} / {total_stays}; dist_hist={dict(sorted(d_hist.items()))}")
    print()

    # Q2
    for fam in Prev.FAMILIES:
        cycles = family_data[fam.label]["cycles"]
        ge2 = sum(1 for c in cycles if c["max_stays_at_one_ternary"] >= 2)
        maxv = max(c["max_stays_at_one_ternary"] for c in cycles)
        print(f"Q2 {fam.label}: cycles_with_max>=2 {ge2}; max_observed {maxv}")
    print()

    # Q3
    for fam in Prev.FAMILIES:
        cycles = family_data[fam.label]["cycles"]
        hist = Counter(c["max_stays_in_one_binary_interval"] for c in cycles)
        maxv = max(hist) if hist else 0
        ge3 = sum(1 for c in cycles if c["max_stays_in_one_binary_interval"] >= 3)
        print(f"Q3 {fam.label}: hist={dict(sorted(hist.items()))}; max_observed={maxv}; cycles_with_3plus={ge3}")
    print()

    # Q4
    for fam in Prev.FAMILIES:
        cycles = family_data[fam.label]["cycles"]
        mono = 0
        rev = 0
        for c in cycles:
            for s in c["per_stay"]:
                if s["inside_monotone_block"]:
                    mono += 1
                else:
                    rev += 1
        print(f"Q4 {fam.label}: monotone_interior {mono} / {mono + rev}; reversal_aligned {rev} / {mono + rev}")
    print()

    # Q5
    for fam in Prev.FAMILIES:
        cycles = family_data[fam.label]["cycles"]
        totals = class_totals[fam.label]
        per_cycle = {cls: sum(1 for c in cycles if cls in c["class_presence"]) for cls in ["A", "B", "C"]}
        print(
            f"Q5 {fam.label}: total_stays A/B/C = {totals['A']}/{totals['B']}/{totals['C']}; "
            f"cycles_with_class A/B/C = {per_cycle['A']}/{per_cycle['B']}/{per_cycle['C']} of {len(cycles)}"
        )
    print()

    # Q6
    for idx, fam in enumerate(Prev.FAMILIES):
        cycles = family_data[fam.label]["cycles"]
        sampled_words = Prev.sample_cycles([c["word"] for c in cycles], 5, seed=20260413 + idx)
        cycle_map = {c["word"]: c for c in cycles}
        print(f"Q6 {fam.label} samples:")
        for word in sampled_words:
            c = cycle_map[word]
            annotations = [
                (
                    s["step_index"],
                    s["processor"],
                    s["class"],
                    s["direction_before"],
                    s["direction_after"],
                )
                for s in c["per_stay"]
            ]
            print(
                f"  word={c['highlighted_word']}; "
                f"annotations={annotations}; "
                f"max_stays_in_one_binary_interval={c['max_stays_in_one_binary_interval']}"
            )
        print()


if __name__ == "__main__":
    main()
