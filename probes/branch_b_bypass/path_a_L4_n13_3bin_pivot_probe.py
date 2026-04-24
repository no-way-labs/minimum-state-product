#!/usr/bin/env python3
"""
Path A L4 probe — n13 canonical 3-bin pivot.

Closes the outstanding empirical gap in the short-arc alternate-site rule
for 3-bin cluster families. Tests the canonical pivot multiset
(2,3,2,3,2,3,3,3,3,3,3,3,3) at n=13. This is the one family the earlier
probe session did not finish.

Output: raw per-family report plus a final verdict line. Expected shape
from smaller 3-bin cluster members (n7/n9/n11): every Q2c cycle is
resolved by exactly two binary-adjacent ternary alternate sites, one
giving a linear Option2 witness and the other a WrapOption1 witness.
"""

from __future__ import annotations

import importlib.util
import sys
import time
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
WITNESS = load_module(
    "path_a_witness",
    ROOT / "probes/branch_b_bypass/path_a_witness_search.py",
)
REPAIR = load_module(
    "path_a_repair",
    ROOT / "probes/branch_b_bypass/path_a_L4_restricted_repair_probe.py",
)


N13_3BIN_PIVOT = UNIV.Family(
    13, "n13 3-bin pivot", (2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3)
)


def site_role(ms, i):
    if ms[i] == 2:
        return "binary"
    left_bin = ms[(i - 1) % len(ms)] == 2
    right_bin = ms[(i + 1) % len(ms)] == 2
    if left_bin and right_bin:
        return "sandwiched-ternary"
    if left_bin or right_bin:
        return "binary-adjacent-ternary"
    return "deep-ternary"


def main():
    fam = N13_3BIN_PIVOT

    print("=" * 70)
    print(f"Path A L4 n13 3-bin pivot probe — {fam.label}")
    print(f"ms = {fam.ms}")
    print("=" * 70)
    print()

    t_enum = time.time()
    print("[phase 1] enumerating Path A population ...", flush=True)
    words = UNIV.path_a_population(fam)
    print(f"[phase 1] done in {time.time() - t_enum:.1f}s", flush=True)
    print(f"  population: {len(words)}", flush=True)
    print()

    if not REPAIR.L4.candidate_sites(fam.ms):
        print("No sandwiched ternary in ms — nothing to check.")
        return

    t_q2c = time.time()
    print("[phase 2] classifying each cycle by L4 / repair / Q2c status ...", flush=True)
    q1_count = 0
    q2a_count = 0
    q2b_count = 0
    q2c_count = 0
    candidate_count = 0
    candidate_triples = 0
    double_110 = 0

    q2c_site_counter = Counter()
    q2c_option_counter = Counter()
    q2c_role_counter = Counter()
    q2c_examples = []

    tick = time.time()
    for idx, word in enumerate(words):
        if time.time() - tick > 30:
            print(
                f"  ... progress {idx}/{len(words)} "
                f"(elapsed {time.time() - t_q2c:.1f}s)",
                flush=True,
            )
            tick = time.time()
        candidate_count += 1
        has_linear, has_wrap, _ = REPAIR.cycle_status(word, fam)
        if has_linear:
            q2a_count += 1
        if has_wrap:
            q2b_count += 1
        if has_linear or has_wrap:
            continue
        q2c_count += 1
        hits = WITNESS.search_cycle(word, fam.ms, fam.n)
        seen_sites = set()
        for i, a1, a2, k2, option in hits:
            q2c_site_counter[i] += 1
            q2c_option_counter[option] += 1
            if i not in seen_sites:
                q2c_role_counter[site_role(fam.ms, i)] += 1
                seen_sites.add(i)
        if len(q2c_examples) < 5:
            q2c_examples.append((list(word), hits[:10]))

    print(f"[phase 2] done in {time.time() - t_q2c:.1f}s", flush=True)
    print()

    print("### results")
    print(f"  population: {len(words)}")
    print(f"  candidate cycles (has sandwiched ternary): {candidate_count}")
    print(f"  Q2a (linear witness at sandwiched ternary):  {q2a_count}")
    print(f"  Q2b (wrap witness at sandwiched ternary):    {q2b_count}")
    print(f"  Q2c (neither linear nor wrap at sandwiched): {q2c_count}")
    if q2c_count:
        print(f"  Q2c witness site histogram:   {dict(q2c_site_counter)}")
        print(f"  Q2c witness option histogram: {dict(q2c_option_counter)}")
        print(f"  Q2c per-cycle site-role coverage: {dict(q2c_role_counter)}")
        print("  Q2c examples:")
        for word, hits in q2c_examples:
            print(f"    word={word}")
            print(f"    hits={hits}")
    else:
        print("  Q2c is empty — n13 canonical 3-bin pivot has no short-arc failures")

    print()
    print("=" * 70)
    if q2c_count == 0:
        print(
            "VERDICT: n13 canonical 3-bin pivot Q2c=0. "
            "No short-arc class at this n."
        )
    else:
        sites = set(q2c_site_counter.keys())
        options = set(q2c_option_counter.keys())
        expected_opts = {"Option2", "WrapOption1"}
        role_pure_adj_t = set(q2c_role_counter.keys()) == {"binary-adjacent-ternary"}
        print(f"VERDICT: n13 canonical 3-bin pivot Q2c={q2c_count}.")
        print(f"  site count: {len(sites)}")
        print(f"  option set: {options}")
        print(f"  expected alternate-site options present: {expected_opts <= options}")
        print(f"  all Q2c witness sites are binary-adjacent ternaries: {role_pure_adj_t}")
    print("=" * 70)


if __name__ == "__main__":
    main()
