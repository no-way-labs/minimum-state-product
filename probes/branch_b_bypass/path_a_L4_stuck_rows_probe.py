#!/usr/bin/env python3
"""
Path A L4 stuck-rows probe (2026-04-15).

Question: do the 6 "stuck" L4c rows actually occur in pivot / non-pivot
Path A min-CL populations? If not, Architecture B (wrap witness + pivot
over sandwich-Ts) closes cleanly without needing Result 1 / 1' / L4d.

The 6 stuck rows are joint (L-dist, R-dist) pairs where both linear
arcs and the wrap arc fail the pattern {(0,0),(0,2),(2,0)}:

    (d=(1,1,0), e=(1,0,1))      wrap=(0,1)
    (d=(1,1,0), f=(0,1,1))      wrap=(0,1)
    (e=(1,0,1), d=(1,1,0))      wrap=(1,0)
    (e=(1,0,1), f=(0,1,1))      wrap=(1,1)
    (f=(0,1,1), d=(1,1,0))      wrap=(1,0)
    (f=(0,1,1), e=(1,0,1))      wrap=(1,1)

Also records:
- 7 wrap-recoverable failure rows (need wrap arc nonempty to actually
  close — empty wrap disqualifies even when c_w tuple is OK).
- 23 linear-recoverable rows (trivially safe).
- For each cycle: does it have ≥1 "safe" triple at some sandwich-T?
  (Architecture B closure criterion.)
"""

from __future__ import annotations

import importlib.util
import itertools
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

# Extend FAMILIES with the n=13 pivot (closes the earlier empirical gap).
EXTRA_FAMILIES = [
    UNIV.Family(13, "n13 3-bin pivot",
                (2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3)),
]
ALL_FAMILIES = list(UNIV.FAMILIES) + EXTRA_FAMILIES


DISTS = {
    "a": (2, 0, 0),
    "b": (0, 2, 0),
    "c": (0, 0, 2),
    "d": (1, 1, 0),
    "e": (1, 0, 1),
    "f": (0, 1, 1),
}
VALID_PATTERNS = {(0, 0), (0, 2), (2, 0)}
STUCK_ROWS = {
    ("d", "e"), ("d", "f"),
    ("e", "d"), ("e", "f"),
    ("f", "d"), ("f", "e"),
}
WRAP_RECOVERABLE = {
    ("a", "d"), ("b", "d"), ("c", "d"),
    ("d", "a"), ("d", "b"), ("d", "c"),
    ("d", "d"),
}


def dist_label(tup: tuple[int, int, int]) -> str | None:
    for name, v in DISTS.items():
        if v == tup:
            return name
    return None


def fire_steps(word, i: int):
    return [k for k, p in enumerate(word) if p == i]


def interval_fire_count(word, q: int, lo: int, hi: int) -> int:
    return sum(1 for k in range(lo, hi) if word[k] == q)


def arc_counts(word, q: int, f0: int, f1: int, f2: int):
    L = len(word)
    c0 = interval_fire_count(word, q, f0 + 1, f1)
    c1 = interval_fire_count(word, q, f1 + 1, f2)
    cw = interval_fire_count(word, q, 0, f0) + interval_fire_count(word, q, f2 + 1, L)
    return (c0, c1, cw)


def candidate_sites(ms: tuple[int, ...]):
    """Sandwich-T ternaries (ternary with binary neighbors on both sides)."""
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
    return list(itertools.combinations(fires, 3))


def classify_triple(word, n: int, i: int, f0: int, f1: int, f2: int):
    """Return (status, L_name, R_name, wrap_nonempty) for a triple.

    status ∈ {'linear', 'wrap', 'stuck', 'other_failure', 'fc_not_2'}
    'fc_not_2' = one of the neighbors has fireCount != 2 (outside L4c scope)
    """
    L = len(word)
    li = (i - 1) % n
    ri = (i + 1) % n
    left = arc_counts(word, li, f0, f1, f2)
    right = arc_counts(word, ri, f0, f1, f2)
    lname = dist_label(left)
    rname = dist_label(right)
    if lname is None or rname is None:
        return ("fc_not_2", None, None, False)
    # Wrap arc nonempty iff NOT (f0 == 0 AND f2 == L-1)
    wrap_nonempty = not (f0 == 0 and f2 == L - 1)
    # Check linear recoverable
    arc0_ok = (left[0], right[0]) in VALID_PATTERNS
    arc1_ok = (left[1], right[1]) in VALID_PATTERNS
    if arc0_ok or arc1_ok:
        return ("linear", lname, rname, wrap_nonempty)
    # Check wrap recoverable (tuple + nonempty precondition)
    wrap_tuple_ok = (left[2], right[2]) in VALID_PATTERNS
    if wrap_tuple_ok and wrap_nonempty:
        return ("wrap", lname, rname, wrap_nonempty)
    # Check if it's a stuck row
    if (lname, rname) in STUCK_ROWS:
        return ("stuck", lname, rname, wrap_nonempty)
    # Otherwise: wrap tuple ok but wrap arc empty (wrap stay)
    return ("other_failure", lname, rname, wrap_nonempty)


def analyze_family(fam):
    words = UNIV.path_a_population(fam)
    stats = {
        "population": len(words),
        "candidate_cycles": 0,
        "cycles_fully_safe": 0,        # every cycle has ≥1 safe triple
        "cycles_with_stuck_triple": 0,
        "cycles_with_only_failures": 0, # no safe triple anywhere
        "triples_total": 0,
        "triples_linear": 0,
        "triples_wrap": 0,
        "triples_stuck": 0,
        "triples_other_failure": 0,
        "triples_fc_not_2": 0,
        "stuck_row_hist": Counter(),
        "stuck_examples": [],
        # NEW: marginal + joint histograms to catch probe bugs
        "L_dist_hist": Counter(),
        "R_dist_hist": Counter(),
        "joint_dist_hist": Counter(),
    }

    for word in words:
        cycle_has_candidate = False
        cycle_has_safe = False
        cycle_has_stuck = False
        for i in candidate_sites(fam.ms):
            for triple in triples_for_site(word, i):
                cycle_has_candidate = True
                stats["triples_total"] += 1
                status, lname, rname, wrap_nonempty = classify_triple(
                    word, fam.n, i, *triple
                )
                if lname is not None:
                    stats["L_dist_hist"][lname] += 1
                if rname is not None:
                    stats["R_dist_hist"][rname] += 1
                if lname is not None and rname is not None:
                    stats["joint_dist_hist"][(lname, rname)] += 1
                if status == "linear":
                    stats["triples_linear"] += 1
                    cycle_has_safe = True
                elif status == "wrap":
                    stats["triples_wrap"] += 1
                    cycle_has_safe = True
                elif status == "stuck":
                    stats["triples_stuck"] += 1
                    stats["stuck_row_hist"][(lname, rname)] += 1
                    cycle_has_stuck = True
                    if len(stats["stuck_examples"]) < 5:
                        stats["stuck_examples"].append({
                            "word": list(word),
                            "i": i,
                            "triple": triple,
                            "L": lname,
                            "R": rname,
                            "wrap_nonempty": wrap_nonempty,
                        })
                elif status == "other_failure":
                    stats["triples_other_failure"] += 1
                elif status == "fc_not_2":
                    stats["triples_fc_not_2"] += 1
        if cycle_has_candidate:
            stats["candidate_cycles"] += 1
            if cycle_has_safe:
                stats["cycles_fully_safe"] += 1
            else:
                stats["cycles_with_only_failures"] += 1
            if cycle_has_stuck:
                stats["cycles_with_stuck_triple"] += 1

    return stats


def main():
    print("=" * 70)
    print("Path A L4 stuck-rows probe (6 stuck rows + cycle-level safety)")
    print("=" * 70)
    print()

    grand = Counter()
    grand_stuck_hist = Counter()
    grand_stuck_examples = []

    for fam in ALL_FAMILIES:
        stats = analyze_family(fam)
        for k in ("population", "candidate_cycles", "cycles_fully_safe",
                  "cycles_with_stuck_triple", "cycles_with_only_failures",
                  "triples_total", "triples_linear", "triples_wrap",
                  "triples_stuck", "triples_other_failure", "triples_fc_not_2"):
            grand[k] += stats[k]
        grand_stuck_hist.update(stats["stuck_row_hist"])
        grand_stuck_examples.extend(
            (fam.label, ex) for ex in stats["stuck_examples"]
        )

        print(f"### {fam.label}  (n={fam.n}, ms={fam.ms})")
        print(f"  population: {stats['population']}")
        print(f"  candidate cycles (has sandwich-T): {stats['candidate_cycles']}")
        print(f"  cycles fully safe (≥1 safe triple): {stats['cycles_fully_safe']}")
        print(f"  cycles with NO safe triple: {stats['cycles_with_only_failures']}")
        print(f"  cycles with ≥1 stuck triple: {stats['cycles_with_stuck_triple']}")
        print(f"  triples: {stats['triples_total']} "
              f"(linear={stats['triples_linear']}, wrap={stats['triples_wrap']}, "
              f"stuck={stats['triples_stuck']}, "
              f"other_fail={stats['triples_other_failure']}, "
              f"fc≠2={stats['triples_fc_not_2']})")
        if stats["L_dist_hist"]:
            print(f"  L-dist hist: {dict(stats['L_dist_hist'])}")
            print(f"  R-dist hist: {dict(stats['R_dist_hist'])}")
            top_joint = sorted(stats['joint_dist_hist'].items(),
                               key=lambda x: -x[1])[:8]
            print(f"  joint hist (top 8): {top_joint}")
        if stats["stuck_row_hist"]:
            print(f"  stuck rows seen: {dict(stats['stuck_row_hist'])}")
        print()

    print("=" * 70)
    print("GRAND TOTALS")
    print("=" * 70)
    print(f"  total population:           {grand['population']}")
    print(f"  candidate cycles:           {grand['candidate_cycles']}")
    print(f"  cycles fully safe:          {grand['cycles_fully_safe']}")
    print(f"  cycles with no safe triple: {grand['cycles_with_only_failures']}")
    print(f"  cycles with stuck triple:   {grand['cycles_with_stuck_triple']}")
    print()
    print(f"  total triples:    {grand['triples_total']}")
    print(f"  linear-safe:      {grand['triples_linear']}")
    print(f"  wrap-safe:        {grand['triples_wrap']}")
    print(f"  stuck rows:       {grand['triples_stuck']}")
    print(f"  other failures:   {grand['triples_other_failure']}")
    print(f"  fc≠2:             {grand['triples_fc_not_2']}")
    print()
    if grand_stuck_hist:
        print(f"  stuck-row histogram: {dict(grand_stuck_hist)}")
    else:
        print("  stuck-row histogram: EMPTY (no stuck rows observed)")
    print()
    print("=" * 70)
    print("VERDICT")
    print("=" * 70)
    if grand["cycles_with_only_failures"] == 0:
        print("Every candidate cycle has ≥1 safe triple (linear or wrap).")
        print("→ Architecture B (wrap witness + pivot) closes cleanly.")
        print("→ Result 1 / 1' / L4d rotation would be unused dead code.")
    else:
        print(f"{grand['cycles_with_only_failures']} cycles have NO safe triple.")
        print("→ Architecture B needs extra machinery for these.")
        print("→ Result 1 / walker-trap style arguments may still be needed.")
    print()
    if grand["triples_stuck"] == 0:
        print("No stuck rows observed in any candidate triple.")
        print("→ The 6 stuck rows appear structurally impossible in Path A.")
    else:
        print(f"{grand['triples_stuck']} stuck triples observed.")
        print("→ Stuck rows DO occur and need analytical handling.")
        if grand_stuck_examples:
            print()
            print("Examples:")
            for fam_label, ex in grand_stuck_examples[:5]:
                print(f"  family={fam_label}, i={ex['i']}, triple={ex['triple']}, "
                      f"(L,R)=({ex['L']},{ex['R']}), wrap_nonempty={ex['wrap_nonempty']}")
                print(f"    word={ex['word']}")


if __name__ == "__main__":
    main()
