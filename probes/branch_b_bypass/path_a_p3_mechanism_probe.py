#!/usr/bin/env python3
"""
Path A P3 mechanism probe.

P3 = single-bin-adj non-pivot families. In all-odd-gap, 3-consec-binary,
and 3-all-spaced families there are no sandwiched (double-bin-adj)
ternaries, so every Path A cycle in these families lands in P3 by
construction.

Goal: characterise the witness mechanism by classifying every witness hit
in the 34,959 P3 cycles. The per-cycle and per-hit classifications are:

  - site role: binary / single-bin-adj-ternary / sandwiched-ternary /
    deep-ternary
  - option: Option1 / Option2 / WrapOption1 / WrapOption2
  - mechanism class:
      * "linear-short" — linear option, suffix length [k2, a2) ≤ 2
      * "linear-long"  — linear option, suffix length > 2
      * "wrap"         — any wrap option
  - silent-side fire count (the ternary neighbor that has to be silent)
  - silent-side largest gap (max run of consecutive non-fires of that proc)

For each non-pivot family, report:

  - per-cycle: at least one single-bin-adj-T witness?
  - per-cycle: minimum option needed (some / wrap-only / linear-only)
  - mechanism distribution over hits
  - mechanism distribution restricted to single-bin-adj-T sites
  - whether all-odd-gap behaves identically to 3-consec-binary etc.
"""

from __future__ import annotations

import importlib.util
import sys
import time
from collections import Counter, defaultdict
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


NON_PIVOT_FAMILIES = [
    f for f in UNIV.FAMILIES if "pivot" not in f.label
]


def site_role(ms, i):
    if ms[i] == 2:
        return "binary"
    n = len(ms)
    left_bin = ms[(i - 1) % n] == 2
    right_bin = ms[(i + 1) % n] == 2
    if left_bin and right_bin:
        return "sandwiched-T"
    if left_bin or right_bin:
        return "single-bin-adj-T"
    return "deep-T"


def silent_side_proc(ms, n, i, option):
    """The processor that the witness option requires to be silent."""
    if option in ("Option1", "WrapOption1"):
        return WITNESS.left_ring(i, n)
    if option in ("Option2", "WrapOption2"):
        return WITNESS.right_ring(i, n)
    return None


def linear_suffix_length(a1, a2, k2):
    """Length of [k2, a2). a1 is unused here but kept for clarity."""
    return a2 - k2


def fire_count_in_word(word, q):
    return sum(1 for x in word if x == q)


def largest_silent_gap(word, q):
    """Cyclic largest gap with no q-fire."""
    L = len(word)
    fires = [k for k, x in enumerate(word) if x == q]
    if not fires:
        return L
    # gaps between consecutive fires (cyclic)
    gaps = []
    for idx in range(len(fires)):
        a = fires[idx]
        b = fires[(idx + 1) % len(fires)]
        gap = (b - a - 1) % L
        gaps.append(gap)
    return max(gaps)


def classify_hit(word, ms, n, hit):
    i, a1_or_a, a2_or_smax, k2_or_none, option = hit
    role = site_role(ms, i)
    silent_proc = silent_side_proc(ms, n, i, option)
    silent_fc = fire_count_in_word(word, silent_proc) if silent_proc is not None else None
    silent_gap = largest_silent_gap(word, silent_proc) if silent_proc is not None else None
    if option in ("Option1", "Option2"):
        suffix_len = linear_suffix_length(a1_or_a, a2_or_smax, k2_or_none)
        if suffix_len <= 2:
            mechanism = "linear-short"
        else:
            mechanism = "linear-long"
    else:
        mechanism = "wrap"
        suffix_len = None
    return {
        "i": i,
        "role": role,
        "option": option,
        "mechanism": mechanism,
        "silent_proc": silent_proc,
        "silent_fc": silent_fc,
        "silent_gap": silent_gap,
        "suffix_len": suffix_len,
    }


def main():
    print("=" * 70)
    print("Path A P3 mechanism probe — non-pivot families")
    print("=" * 70)
    print()

    grand_total = 0
    grand_witnessed = 0
    grand_role_counter = Counter()
    grand_mechanism_counter = Counter()
    grand_option_counter = Counter()

    per_family_summary = []

    for fam in NON_PIVOT_FAMILIES:
        t = time.time()
        words = UNIV.path_a_population(fam)
        print(f"### {fam.label}  ms={fam.ms}", flush=True)
        print(f"  population: {len(words)} ({time.time() - t:.1f}s)", flush=True)

        per_cycle_has_sba = 0
        per_cycle_min_option = Counter()  # 'linear-only' / 'wrap-only' / 'both'
        role_counter = Counter()
        option_counter = Counter()
        mechanism_counter = Counter()
        sba_mechanism_counter = Counter()
        silent_fc_dist = Counter()
        suffix_len_dist = Counter()

        # Mechanism observations
        for word in words:
            hits = WITNESS.search_cycle(word, fam.ms, fam.n)
            if not hits:
                continue
            grand_witnessed += 1
            seen_sba = False
            seen_linear = False
            seen_wrap = False
            cycle_classifications = []
            for hit in hits:
                cls = classify_hit(word, fam.ms, fam.n, hit)
                cycle_classifications.append(cls)
                role_counter[cls["role"]] += 1
                option_counter[cls["option"]] += 1
                mechanism_counter[cls["mechanism"]] += 1
                grand_role_counter[cls["role"]] += 1
                grand_mechanism_counter[cls["mechanism"]] += 1
                grand_option_counter[cls["option"]] += 1
                if cls["role"] == "single-bin-adj-T":
                    seen_sba = True
                    sba_mechanism_counter[cls["mechanism"]] += 1
                if cls["mechanism"] in ("linear-short", "linear-long"):
                    seen_linear = True
                if cls["mechanism"] == "wrap":
                    seen_wrap = True
                if cls["silent_fc"] is not None:
                    silent_fc_dist[cls["silent_fc"]] += 1
                if cls["suffix_len"] is not None:
                    suffix_len_dist[cls["suffix_len"]] += 1
            if seen_sba:
                per_cycle_has_sba += 1
            if seen_linear and seen_wrap:
                per_cycle_min_option["both"] += 1
            elif seen_linear:
                per_cycle_min_option["linear-only"] += 1
            elif seen_wrap:
                per_cycle_min_option["wrap-only"] += 1

        grand_total += len(words)
        print(f"  per-cycle has single-bin-adj-T witness: {per_cycle_has_sba}/{len(words)}")
        print(f"  per-cycle option mix: {dict(per_cycle_min_option)}")
        print(f"  hit role counter: {dict(role_counter)}")
        print(f"  hit option counter: {dict(option_counter)}")
        print(f"  hit mechanism counter: {dict(mechanism_counter)}")
        print(f"  single-bin-adj-T mechanism counter: {dict(sba_mechanism_counter)}")
        print(f"  silent-side fire-count distribution: {dict(silent_fc_dist)}")
        print(f"  linear suffix-length distribution: {dict(suffix_len_dist)}")
        print()

        per_family_summary.append({
            "family": fam.label,
            "population": len(words),
            "per_cycle_has_sba": per_cycle_has_sba,
            "per_cycle_option_mix": dict(per_cycle_min_option),
            "role_counter": dict(role_counter),
            "option_counter": dict(option_counter),
            "mechanism_counter": dict(mechanism_counter),
            "sba_mechanism_counter": dict(sba_mechanism_counter),
            "silent_fc_dist": dict(silent_fc_dist),
            "suffix_len_dist": dict(suffix_len_dist),
        })

    print("=" * 70)
    print(f"Grand total population: {grand_total}")
    print(f"Grand witnessed: {grand_witnessed}")
    print(f"Grand role counter: {dict(grand_role_counter)}")
    print(f"Grand option counter: {dict(grand_option_counter)}")
    print(f"Grand mechanism counter: {dict(grand_mechanism_counter)}")
    print("=" * 70)


if __name__ == "__main__":
    main()
