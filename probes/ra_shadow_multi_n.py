#!/usr/bin/env python3
"""ra_shadow_multi_n.py — Shadow-flip checks across n=5,6,7,8.

This script does two separate things:

1. Search the requested exact tuples
     n=6: (2,2,2,3,3,4)
     n=7: (2,2,2,3,3,3,4)
     n=8: (2,2,2,3,3,3,3,4)
   using a good-targeting completion on mixed-sweep seed cycles.

2. Run the actual shadow-flip test on verified in-repo witnesses:
     n=5: (2,2,2,3,4)
     n=6: (2,2,2,4,3,3)
     n=7: (3,2,2,2,3,4,3)
   plus rotations to move the binary triple.

The search in (1) is the requested "build using the good-targeting construction".
The shadow counts in (2) ensure we still have concrete n=6 and n=7 results even
when the exact tuples in (1) do not verify.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import product as cartesian
from typing import Iterable

from verifier import privileged_set, verify_system
from ra_shadow_m5 import build_m5_96_witness
from cycle_first_search import witness_n6, witness_n7, witness_n8


def make_fs_from_tables(tables):
    fs = []
    for table in tables:
        def make_f(tt):
            def f(left, self_state, right):
                return tt[(left, self_state, right)]

            return f

        fs.append(make_f(table))
    return fs


def rotate_system(ms, tables, shift):
    n = len(ms)
    rotated_ms = tuple(ms[(i + shift) % n] for i in range(n))
    rotated_tables = tuple(tables[(i + shift) % n] for i in range(n))
    return rotated_ms, rotated_tables


def find_binary_triples(ms):
    n = len(ms)
    triples = []
    for start in range(n):
        triple = tuple((start + offset) % n for offset in range(3))
        if all(ms[idx] == 2 for idx in triple):
            triples.append(triple)
    return triples


def flip_shadow(config, procs: Iterable[int]):
    shadow = list(config)
    for proc in procs:
        shadow[proc] = 1 - shadow[proc]
    return tuple(shadow)


def shadow_stats(ms, fs, flip_procs, cycle):
    live_steps = 0
    failing_steps = []
    for step, config in enumerate(cycle):
        shadow = flip_shadow(config, flip_procs)
        privs = privileged_set(shadow, fs, list(ms))
        if privs:
            live_steps += 1
        else:
            failing_steps.append((step, config, shadow))
    return {
        "live_steps": live_steps,
        "total_steps": len(cycle),
        "failing_steps": failing_steps,
    }


def build_mixed_sweep_cycle(ms, order, targets, return_same_order):
    config = [0] * len(ms)
    cycle = [tuple(config)]

    for proc in order:
        config = list(cycle[-1])
        config[proc] = 1 if ms[proc] == 2 else targets[proc]
        cycle.append(tuple(config))

    down_order = order if return_same_order else tuple(reversed(order))
    for proc in down_order:
        config = list(cycle[-1])
        config[proc] = 0
        cycle.append(tuple(config))

    if cycle[-1] != cycle[0]:
        return None
    cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def cyclic_orders(n):
    seen = set()
    for base in (list(range(n)), list(range(n - 1, -1, -1))):
        for shift in range(n):
            order = tuple(base[shift:] + base[:shift])
            if order not in seen:
                seen.add(order)
                yield order


def good_targeting_completion(ms, cycle):
    n = len(ms)
    good_set = set(cycle)
    if len(good_set) != len(cycle):
        return None

    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [config for config in all_configs if config not in good_set]
    non_good_set = set(non_good)

    det = {}
    for idx, config in enumerate(cycle):
        nxt = cycle[(idx + 1) % len(cycle)]
        diffs = [proc for proc in range(n) if config[proc] != nxt[proc]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        for proc in range(n):
            left = config[(proc - 1) % n]
            self_state = config[proc]
            right = config[(proc + 1) % n]
            key = (proc, left, self_state, right)
            out = nxt[proc] if proc == mover else self_state
            if key in det and det[key] != out:
                return None
            det[key] = out

    free_entries = []
    free_set = set()
    for proc in range(n):
        m_left = ms[(proc - 1) % n]
        m_self = ms[proc]
        m_right = ms[(proc + 1) % n]
        for left in range(m_left):
            for self_state in range(m_self):
                for right in range(m_right):
                    key = (proc, left, self_state, right)
                    if key not in det:
                        free_entries.append(key)
                        free_set.add(key)

    triple_index = defaultdict(list)
    for config in non_good:
        for proc in range(n):
            key = (proc, config[(proc - 1) % n], config[proc], config[(proc + 1) % n])
            if key in free_set:
                triple_index[key].append(config)

    edge_costs = {}
    comp = dict(det)
    for key in free_entries:
        proc, _, self_state, _ = key
        matching = triple_index.get(key, [])
        best_out = self_state
        best_good = 0
        best_ng = 0

        for out in range(ms[proc]):
            if out == self_state:
                edge_costs[(key, out)] = 0
                continue

            good_count = 0
            ng_count = 0
            for config in matching:
                new_config = config[:proc] + (out,) + config[proc + 1:]
                if new_config in good_set:
                    good_count += 1
                elif new_config in non_good_set:
                    ng_count += 1
            edge_costs[(key, out)] = ng_count

            if good_count > best_good or (good_count == best_good and ng_count < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng_count

        comp[key] = best_out

    liveness_fixes = 0
    for config in all_configs:
        has_priv = False
        for proc in range(n):
            key = (proc, config[(proc - 1) % n], config[proc], config[(proc + 1) % n])
            if comp.get(key, config[proc]) != config[proc]:
                has_priv = True
                break
        if has_priv:
            continue

        best_key = None
        best_cost = float("inf")
        best_out = None
        for proc in range(n):
            key = (proc, config[(proc - 1) % n], config[proc], config[(proc + 1) % n])
            if key in det:
                continue
            for out in range(ms[proc]):
                if out == config[proc]:
                    continue
                cost = edge_costs.get((key, out), 0)
                if cost < best_cost:
                    best_cost = cost
                    best_key = key
                    best_out = out

        if best_key is not None:
            comp[best_key] = best_out
            liveness_fixes += 1

    tables = []
    for proc in range(n):
        table = {}
        m_left = ms[(proc - 1) % n]
        m_self = ms[proc]
        m_right = ms[(proc + 1) % n]
        for left in range(m_left):
            for self_state in range(m_self):
                for right in range(m_right):
                    key = (proc, left, self_state, right)
                    table[(left, self_state, right)] = comp.get(key, self_state)
        tables.append(table)

    fs = make_fs_from_tables(tables)
    result = verify_system(list(ms), fs, verbose=False)
    return {
        "fs": fs,
        "tables": tuple(tables),
        "verify": result,
        "liveness_fixes": liveness_fixes,
    }


def search_exact_tuple(ms):
    n = len(ms)
    non_binary = [proc for proc, m in enumerate(ms) if m > 2]
    target_ranges = [range(1, ms[proc]) for proc in non_binary]
    tested = 0

    for combo in cartesian(*target_ranges):
        targets = {proc: 1 for proc, m in enumerate(ms) if m == 2}
        for idx, proc in enumerate(non_binary):
            targets[proc] = combo[idx]

        for order in cyclic_orders(n):
            for return_same_order in (True, False):
                cycle = build_mixed_sweep_cycle(ms, order, targets, return_same_order)
                if cycle is None:
                    continue
                tested += 1
                completion = good_targeting_completion(ms, cycle)
                if completion is None:
                    continue
                if completion["verify"]["valid"]:
                    return {
                        "ms": tuple(ms),
                        "tested": tested,
                        "order": order,
                        "targets": tuple(combo),
                        "return_same_order": return_same_order,
                        "completion": completion,
                    }

    return {
        "ms": tuple(ms),
        "tested": tested,
        "order": None,
        "targets": None,
        "return_same_order": None,
        "completion": None,
    }


def print_exact_tuple_report(ms):
    search = search_exact_tuple(ms)
    ms_label = ",".join(str(m) for m in search["ms"])
    if search["completion"] is None:
        print(f"  ms=({ms_label})")
        print(f"    tested mixed-sweep seed cycles: {search['tested']}")
        print("    valid system found: no")
        return

    result = search["completion"]["verify"]
    print(f"  ms=({ms_label})")
    print(f"    tested mixed-sweep seed cycles: {search['tested']}")
    print("    valid system found: yes")
    print(f"    seed order: {search['order']}")
    print(f"    targets: {search['targets']}")
    print(f"    return_same_order: {search['return_same_order']}")
    print(f"    cycle length: {result['cycle_length']}")

    triples = find_binary_triples(search["ms"])
    if triples:
        triple = triples[0]
        flip = (triple[0], triple[2])
        stats = shadow_stats(search["ms"], search["completion"]["fs"], flip, result["cycle"])
        print(f"    binary triple: {triple}")
        print(f"    flip: {flip}")
        print(f"    shadow privilege: {stats['live_steps']}/{stats['total_steps']}")


def print_witness_shadow(label, ms, tables):
    fs = make_fs_from_tables(tables)
    result = verify_system(list(ms), fs, verbose=False)
    if not result["valid"]:
        raise SystemExit(f"{label} failed verify_system(); aborting.")

    triples = find_binary_triples(ms)
    if len(triples) != 1:
        raise SystemExit(f"{label} expected exactly one binary triple, got {triples}")

    triple = triples[0]
    flip = (triple[0], triple[2])
    stats = shadow_stats(ms, fs, flip, result["cycle"])

    print(f"  {label}")
    print(f"    ms={ms}")
    print(f"    binary triple={triple}")
    print(f"    flip={flip}")
    print(f"    verify_system.cycle_length={result['cycle_length']}")
    print(f"    shadow privilege={stats['live_steps']}/{stats['total_steps']}")
    if stats["failing_steps"]:
        print(f"    failing steps={len(stats['failing_steps'])}")
    else:
        print("    failing steps=0")


def main():
    print("Shadow flip tests across n=5,6,7,8")
    print("=" * 72)
    print()

    print("Part 1: Requested exact tuples via mixed-sweep good-targeting")
    print("-" * 72)
    for ms in (
        (2, 2, 2, 3, 3, 4),
        (2, 2, 2, 3, 3, 3, 4),
        (2, 2, 2, 3, 3, 3, 3, 4),
    ):
        print_exact_tuple_report(ms)
    print()

    print("Part 2: Verified witness shadow counts")
    print("-" * 72)

    m5_tables, _ = build_m5_96_witness()
    print_witness_shadow("n=5 baseline", (2, 2, 2, 3, 4), tuple(m5_tables))

    ms6, tables6 = witness_n6()
    print_witness_shadow("n=6 witness triple at {0,1,2}", ms6, tables6)
    ms6_tail, tables6_tail = rotate_system(ms6, tables6, 3)
    print_witness_shadow("n=6 rotated triple at {3,4,5}", ms6_tail, tables6_tail)

    ms7, tables7 = witness_n7()
    print_witness_shadow("n=7 witness triple at {1,2,3}", ms7, tables7)
    ms7_front, tables7_front = rotate_system(ms7, tables7, 1)
    print_witness_shadow("n=7 rotated triple at {0,1,2}", ms7_front, tables7_front)
    ms7_tail, tables7_tail = rotate_system(ms7, tables7, 4)
    print_witness_shadow("n=7 rotated triple at {4,5,6}", ms7_tail, tables7_tail)
    print()

    print("Part 3: n=8 note")
    print("-" * 72)
    ms8, tables8 = witness_n8()
    fs8 = make_fs_from_tables(tables8)
    result8 = verify_system(list(ms8), fs8, verbose=False)
    print(f"  verified in-repo n=8 witness ms={ms8}")
    print(f"    verify_system.valid={result8['valid']}")
    print(f"    verify_system.cycle_length={result8['cycle_length']}")
    print("    binary triple: none")
    print("    shadow flip test for a consecutive-binary triple: not applicable")


if __name__ == "__main__":
    main()
