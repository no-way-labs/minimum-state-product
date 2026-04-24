from __future__ import annotations

import argparse
import json
import os
import sys
from itertools import permutations

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from p2_ring import build_dijkstra_solution_3
from scripts import verify_witnesses as vw


TERNARY_PERMS = tuple(permutations((0, 1, 2)))


def witness_builders():
    return {
        5: vw.witness_n5,
        6: vw.witness_n6,
        7: vw.witness_n7,
        8: vw.witness_n8,
    }


def rotation_or_reflection_match(ms: tuple[int, ...], target: tuple[int, ...]) -> bool:
    if len(ms) != len(target):
        return False
    rotations = [ms[i:] + ms[:i] for i in range(len(ms))]
    reversed_ms = tuple(reversed(ms))
    reflections = [reversed_ms[i:] + reversed_ms[:i] for i in range(len(ms))]
    return target in rotations or target in reflections


def processor_triples(ms: tuple[int, ...]) -> list[tuple[int, int, int]]:
    n = len(ms)
    return [(ms[(i - 1) % n], ms[i], ms[(i + 1) % n]) for i in range(n)]


def canonicalize_rule(
    state_counts: tuple[int, ...],
    processor: int,
    rule: dict[tuple[int, int, int], int],
) -> tuple[tuple[tuple[int, int, int], int], ...]:
    n = len(state_counts)
    left_m = state_counts[(processor - 1) % n]
    self_m = state_counts[processor]
    right_m = state_counts[(processor + 1) % n]
    best = None
    for perm in TERNARY_PERMS:
        rows = []
        for key in sorted(rule):
            left, self_state, right = key
            canon_key = (
                perm[left] if left_m == 3 else left,
                perm[self_state] if self_m == 3 else self_state,
                perm[right] if right_m == 3 else right,
            )
            canon_out = perm[rule[key]] if self_m == 3 else rule[key]
            rows.append((canon_key, canon_out))
        candidate = tuple(sorted(rows))
        if best is None or candidate < best:
            best = candidate
    assert best is not None
    return best


def build_report() -> dict:
    report = {
        "witnesses": {},
        "target_orientation_matches": {},
        "triple_groups": {},
        "interior_333_processors": [],
    }

    for n, builder in witness_builders().items():
        state_counts, rules = builder()
        triples = processor_triples(state_counts)
        target = (2, 2, 2, 4) + (3,) * (n - 4)
        report["witnesses"][str(n)] = {
            "state_counts": list(state_counts),
            "triples": [
                {
                    "processor": i,
                    "triple": list(triple),
                }
                for i, triple in enumerate(triples)
            ],
        }
        report["target_orientation_matches"][str(n)] = {
            "target": list(target),
            "matches_rotation_or_reflection": rotation_or_reflection_match(state_counts, target),
        }
        for i, triple in enumerate(triples):
            canonical = canonicalize_rule(state_counts, i, rules[i])
            key = str(triple)
            report["triple_groups"].setdefault(key, []).append(
                {
                    "n": n,
                    "processor": i,
                    "canonical_rule": [[list(ctx), out] for ctx, out in canonical],
                }
            )
            if triple == (3, 3, 3):
                report["interior_333_processors"].append(
                    {
                        "n": n,
                        "processor": i,
                        "canonical_rule": [[list(ctx), out] for ctx, out in canonical],
                    }
                )

    for key, entries in report["triple_groups"].items():
        canons = [entry["canonical_rule"] for entry in entries]
        report["triple_groups"][key] = {
            "occurrences": [{"n": entry["n"], "processor": entry["processor"]} for entry in entries],
            "all_same_after_canonicalization": all(canon == canons[0] for canon in canons[1:]),
        }

    return report


def dijkstra3_middle_rule() -> dict[tuple[int, int, int], int]:
    system = build_dijkstra_solution_3(5)
    return dict(system.rules[1])


def build_one_bulk_family(
    n: int,
    bulk_rule: dict[tuple[int, int, int], int],
) -> tuple[tuple[int, ...], tuple[dict[tuple[int, int, int], int], ...]]:
    if n < 6:
        raise ValueError("family construction requires n >= 6")
    _, n6_rules = vw.witness_n6()
    state_counts = (2, 2, 2, 4) + (3,) * (n - 4)
    rules = [
        dict(n6_rules[0]),
        dict(n6_rules[1]),
        dict(n6_rules[2]),
        dict(n6_rules[3]),
        dict(n6_rules[4]),
    ]
    for _ in range(5, n - 1):
        rules.append(dict(bulk_rule))
    rules.append(dict(n6_rules[5]))
    return state_counts, tuple(rules)


def test_candidate_bulk(
    candidate_name: str,
    bulk_rule: dict[tuple[int, int, int], int],
    n_values: list[int],
) -> list[dict]:
    results = []
    for n in n_values:
        state_counts, rules = build_one_bulk_family(n, bulk_rule)
        ok = vw.verify(f"{candidate_name}-n{n}", state_counts, rules)
        results.append(
            {
                "n": n,
                "state_counts": list(state_counts),
                "verified": ok,
            }
        )
    return results


def print_report(report: dict) -> None:
    print("Upper-bound witness family report")
    print()
    for n_str in sorted(report["witnesses"], key=int):
        witness = report["witnesses"][n_str]
        match = report["target_orientation_matches"][n_str]["matches_rotation_or_reflection"]
        print(f"  n={n_str} state_counts={tuple(witness['state_counts'])} target-match={match}")
        for row in witness["triples"]:
            print(f"    P{row['processor']}: triple={tuple(row['triple'])}")
    print()
    if report["interior_333_processors"]:
        print("  (3,3,3) processors:")
        for row in report["interior_333_processors"]:
            print(f"    n={row['n']} P{row['processor']}")
    else:
        print("  No (3,3,3) processors appear in the proved n=5..8 witnesses.")
    print()
    print("  Canonical triple-group comparison:")
    for triple_key in sorted(report["triple_groups"]):
        group = report["triple_groups"][triple_key]
        if len(group["occurrences"]) < 2:
            continue
        occs = ", ".join(f"n={row['n']} P{row['processor']}" for row in group["occurrences"])
        print(
            f"    triple={triple_key}: same-after-canonicalization="
            f"{group['all_same_after_canonicalization']} [{occs}]"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--json-out",
        help="write the extraction report to JSON",
    )
    parser.add_argument(
        "--test-dijkstra3-middle",
        action="store_true",
        help="test the one-bulk family using the Dijkstra-3 middle rule as a provisional T*",
    )
    parser.add_argument(
        "--n-from",
        type=int,
        default=7,
        help="start of the verification ladder for candidate bulk tests",
    )
    parser.add_argument(
        "--n-to",
        type=int,
        default=10,
        help="end of the verification ladder for candidate bulk tests",
    )
    args = parser.parse_args()

    report = build_report()
    print_report(report)

    if args.test_dijkstra3_middle:
        print()
        print("Testing provisional bulk rule: Dijkstra-3 middle processor")
        results = test_candidate_bulk(
            "dijkstra3-middle",
            dijkstra3_middle_rule(),
            list(range(args.n_from, args.n_to + 1)),
        )
        report["candidate_tests"] = {
            "dijkstra3_middle": results,
        }

    if args.json_out:
        with open(args.json_out, "w") as handle:
            json.dump(report, handle, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
