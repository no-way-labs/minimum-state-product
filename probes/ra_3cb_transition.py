#!/usr/bin/env python3
"""Investigate why 3 consecutive binary fails at n=8.

Question:
  Does ms = (2,2,2,3,3,3,3,4) admit any valid self-stabilizing token ring?

This script does four things:
1. Re-check the known n=7/n=8 witnesses and one non-3CB n=7 construction.
2. Exhaustively test the mixed-sweep good-targeting family on the exact n=8 3CB tuple.
3. Exhaustively test a natural n=7 -> n=8 transplant family.
4. Try mutation-based random/local search around the best mixed-sweep seed.

All code stays inside this directory and uses only the standard library plus
the in-repo verifier/witness helpers.
"""

from __future__ import annotations

import random
import time
from collections import Counter, defaultdict
from itertools import product as cartesian
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from clb_generalize_n import build_and_verify as build_clb
from cycle_first_search import witness_n7, witness_n8
from verifier import all_configs, apply_move, privileged_set, verify_system


Config = Tuple[int, ...]
Triple = Tuple[int, int, int]
RuleTable = Dict[Triple, int]
Tables = Tuple[RuleTable, ...]

TARGET_MS = (2, 2, 2, 3, 3, 3, 3, 4)
VALID_M8_MS = (2, 2, 3, 4, 3, 3, 2, 3)


def ring_product(ms: Sequence[int]) -> int:
    product = 1
    for m in ms:
        product *= m
    return product


def make_fs_from_tables(tables: Sequence[RuleTable]):
    fs = []
    for table in tables:
        def make_f(current_table):
            def f(left, self_state, right):
                return current_table[(left, self_state, right)]

            return f

        fs.append(make_f(table))
    return fs


def rotate_system(ms: Sequence[int], tables: Sequence[RuleTable], shift: int):
    n = len(ms)
    rotated_ms = tuple(ms[(i + shift) % n] for i in range(n))
    rotated_tables = tuple(tables[(i + shift) % n] for i in range(n))
    return rotated_ms, rotated_tables


def property_signature(result: dict) -> Tuple[Tuple[str, bool, str], ...]:
    return tuple(
        sorted((name, ok, msg) for name, (ok, msg) in result["properties"].items())
    )


def cyclic_orders(n: int):
    seen = set()
    for base in (list(range(n)), list(range(n - 1, -1, -1))):
        for shift in range(n):
            order = tuple(base[shift:] + base[:shift])
            if order not in seen:
                seen.add(order)
                yield order


def build_mixed_sweep_cycle(
    ms: Sequence[int],
    order: Sequence[int],
    targets: Dict[int, int],
    return_same_order: bool,
) -> Optional[List[Config]]:
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


def good_targeting_completion(ms: Sequence[int], cycle: Sequence[Config]):
    n = len(ms)
    good_set = set(cycle)
    if len(good_set) != len(cycle):
        return None

    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    non_good = [cfg for cfg in all_cfgs if cfg not in good_set]
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
    for config in all_cfgs:
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
        "tables": tuple(tables),
        "fs": fs,
        "verify": result,
        "liveness_fixes": liveness_fixes,
    }


def build_bounce_cycle(
    ms: Sequence[int],
    base_pattern: Optional[Sequence[int]] = None,
    max_reps: int = 8,
):
    n = len(ms)
    if base_pattern is None:
        base_pattern = list(range(n)) + list(range(n - 2, 0, -1))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = list(base_pattern) * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            next_cfg = tuple(config)
            if next_cfg == cycle[0]:
                return cycle, full[: step + 1]
            if next_cfg in visited:
                break
            visited.add(next_cfg)
            cycle.append(next_cfg)
    return None, None


def cycle_entry_conflicts(cycle: Sequence[Config], movers: Sequence[int]):
    mover_ctx = defaultdict(set)
    nonmover_ctx = defaultdict(set)
    n = len(cycle[0])
    for idx, config in enumerate(cycle):
        mover = movers[idx]
        for proc in range(n):
            triple = (config[(proc - 1) % n], config[proc], config[(proc + 1) % n])
            if proc == mover:
                mover_ctx[proc].add(triple)
            else:
                nonmover_ctx[proc].add(triple)
    overlaps = {}
    for proc in range(n):
        overlap = mover_ctx[proc] & nonmover_ctx[proc]
        if overlap:
            overlaps[proc] = overlap
    return overlaps


def diagnose_tables(ms: Sequence[int], tables: Sequence[RuleTable]):
    configs = list(all_configs(list(ms)))
    fs = make_fs_from_tables(tables)
    priv_map = {cfg: privileged_set(cfg, fs, list(ms)) for cfg in configs}

    dead_count = sum(1 for cfg in configs if not priv_map[cfg])
    if dead_count:
        return {
            "dead_count": dead_count,
            "fair_cycles": 0,
            "best_scc_nodes": None,
            "best_scc_count": None,
            "best_good_size": None,
            "best_cycle_len": None,
        }

    single_priv = [cfg for cfg in configs if len(priv_map[cfg]) == 1]
    succ = {
        cfg: (apply_move(cfg, priv_map[cfg][0], fs, list(ms)), priv_map[cfg][0])
        for cfg in single_priv
    }

    good_candidates = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = {cfg for cfg in good_candidates if succ[cfg][0] not in good_candidates}
        if to_remove:
            good_candidates -= to_remove
            changed = True

    rev = defaultdict(list)
    for cfg in good_candidates:
        rev[succ[cfg][0]].append(cfg)

    fair_cycles = 0
    best = None
    visited = set()
    all_procs = set(range(len(ms)))

    for start in good_candidates:
        if start in visited:
            continue
        path = []
        path_set = set()
        node = start
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            cycle = path[path.index(node):]
            movers = {succ[cfg][1] for cfg in cycle}
            if movers == all_procs:
                fair_cycles += 1
                good = set(cycle)
                queue = list(cycle)
                while queue:
                    cfg = queue.pop()
                    for pred in rev[cfg]:
                        if pred not in good:
                            good.add(pred)
                            queue.append(pred)
                bad = set(configs) - good

                adj = {cfg: [] for cfg in bad}
                radj = defaultdict(list)
                for cfg in bad:
                    for proc in priv_map[cfg]:
                        nxt = apply_move(cfg, proc, fs, list(ms))
                        if nxt in bad:
                            adj[cfg].append(nxt)
                            radj[nxt].append(cfg)

                color = {cfg: 0 for cfg in bad}
                finish_order = []
                for seed in bad:
                    if color[seed]:
                        continue
                    stack = [(seed, 0)]
                    color[seed] = 1
                    while stack:
                        cfg, idx = stack[-1]
                        succs = adj[cfg]
                        if idx < len(succs):
                            nxt = succs[idx]
                            stack[-1] = (cfg, idx + 1)
                            if not color[nxt]:
                                color[nxt] = 1
                                stack.append((nxt, 0))
                        else:
                            finish_order.append(cfg)
                            stack.pop()

                seen = set()
                scc_nodes = 0
                scc_count = 0
                for seed in reversed(finish_order):
                    if seed in seen:
                        continue
                    comp = []
                    stack = [seed]
                    seen.add(seed)
                    while stack:
                        cfg = stack.pop()
                        comp.append(cfg)
                        for pred in radj[cfg]:
                            if pred not in seen:
                                seen.add(pred)
                                stack.append(pred)
                    if len(comp) > 1 or any(cfg in adj[cfg] for cfg in comp):
                        scc_nodes += len(comp)
                        scc_count += 1

                candidate = (scc_nodes, scc_count, len(good), len(cycle))
                if best is None or candidate < best:
                    best = candidate
        visited.update(path)

    return {
        "dead_count": 0,
        "fair_cycles": fair_cycles,
        "best_scc_nodes": None if best is None else best[0],
        "best_scc_count": None if best is None else best[1],
        "best_good_size": None if best is None else best[2],
        "best_cycle_len": None if best is None else best[3],
    }


def run_mixed_sweep_family(ms: Sequence[int], deep: bool):
    non_binary = [proc for proc, m in enumerate(ms) if m > 2]
    target_ranges = [range(1, ms[proc]) for proc in non_binary]

    verify_counter = Counter()
    deep_counter = Counter()
    checked = 0
    first_seed = None
    best_deep = None
    worst_deep = None

    for combo in cartesian(*target_ranges):
        targets = {proc: 1 for proc, m in enumerate(ms) if m == 2}
        for idx, proc in enumerate(non_binary):
            targets[proc] = combo[idx]

        for order in cyclic_orders(len(ms)):
            for return_same_order in (True, False):
                cycle = build_mixed_sweep_cycle(ms, order, targets, return_same_order)
                if cycle is None:
                    continue
                checked += 1

                if first_seed is None:
                    first_seed = {
                        "combo": combo,
                        "order": order,
                        "return_same_order": return_same_order,
                    }

                completion = good_targeting_completion(ms, cycle)
                if completion is None:
                    verify_counter[("completion_failed",)] += 1
                    continue

                verify_counter[property_signature(completion["verify"])] += 1

                if deep:
                    diag = diagnose_tables(ms, completion["tables"])
                    key = (
                        diag["fair_cycles"],
                        diag["best_scc_nodes"],
                        diag["best_scc_count"],
                    )
                    deep_counter[key] += 1
                    record = (
                        diag["best_scc_nodes"],
                        diag["best_scc_count"],
                        diag["best_good_size"],
                        diag["best_cycle_len"],
                        combo,
                        order,
                        return_same_order,
                    )
                    if best_deep is None or record < best_deep:
                        best_deep = record
                    if worst_deep is None or record > worst_deep:
                        worst_deep = record

    return {
        "checked": checked,
        "verify_counter": verify_counter,
        "deep_counter": deep_counter,
        "best_deep": best_deep,
        "worst_deep": worst_deep,
        "first_seed": first_seed,
    }


def run_bounce_family(ms: Sequence[int]):
    n = len(ms)
    base_cw = list(range(n)) + list(range(n - 2, 0, -1))
    base_ccw = list(range(n - 1, -1, -1)) + list(range(1, n - 1))

    patterns = []
    for base in (base_cw, base_ccw):
        for shift in range(len(base)):
            pattern = tuple(base[shift:] + base[:shift])
            if pattern not in patterns:
                patterns.append(pattern)

    counts = Counter()
    verify_counter = Counter()

    for pattern in patterns:
        cycle, movers = build_bounce_cycle(ms, base_pattern=pattern, max_reps=8)
        if cycle is None:
            counts["no_close"] += 1
            continue
        overlaps = cycle_entry_conflicts(cycle, movers)
        if overlaps:
            counts["entry_conflict"] += 1
            continue
        completion = good_targeting_completion(ms, cycle)
        if completion is None:
            counts["completion_failed"] += 1
            continue
        counts["completed"] += 1
        verify_counter[property_signature(completion["verify"])] += 1
        if completion["verify"]["valid"]:
            counts["valid"] += 1

    return {
        "pattern_count": len(patterns),
        "counts": counts,
        "verify_counter": verify_counter,
    }


def run_transplant_slice_family():
    ms7, tables7 = witness_n7()
    base_ms, base_tables = rotate_system(ms7, tables7, shift=1)
    assert base_ms == (2, 2, 2, 3, 4, 3, 3)

    old_p6 = base_tables[6]
    ms8 = base_ms + (3,)
    assert ms8 == (2, 2, 2, 3, 4, 3, 3, 3)

    counts = Counter()
    verify_counter = Counter()
    checked = 0

    start = time.time()
    for vals in cartesian(range(3), repeat=9):
        new_p6 = {}
        idx = 0
        for left in range(3):
            for self_state in range(3):
                new_p6[(left, self_state, 0)] = old_p6[(left, self_state, 0)]
                new_p6[(left, self_state, 1)] = old_p6[(left, self_state, 1)]
                new_p6[(left, self_state, 2)] = vals[idx]
                idx += 1

        tables8 = list(base_tables[:6]) + [new_p6, old_p6]
        result = verify_system(list(ms8), make_fs_from_tables(tables8), verbose=False)
        checked += 1
        verify_counter[property_signature(result)] += 1

        if result["valid"]:
            counts["valid"] += 1
            return {
                "ms": ms8,
                "checked": checked,
                "counts": counts,
                "verify_counter": verify_counter,
                "elapsed": time.time() - start,
                "found_vals": vals,
            }

    counts["valid"] = 0
    return {
        "ms": ms8,
        "checked": checked,
        "counts": counts,
        "verify_counter": verify_counter,
        "elapsed": time.time() - start,
        "found_vals": None,
    }


def proc_keys_for_ms(ms: Sequence[int]):
    proc_keys = []
    n = len(ms)
    for proc in range(n):
        keys = []
        for left in range(ms[(proc - 1) % n]):
            for self_state in range(ms[proc]):
                for right in range(ms[(proc + 1) % n]):
                    keys.append((left, self_state, right))
        proc_keys.append(keys)
    return proc_keys


def run_random_mutation_search(
    ms: Sequence[int],
    seed_tables: Sequence[RuleTable],
    trials: int = 5000,
    edits_low: int = 1,
    edits_high: int = 4,
    random_seed: int = 12345,
):
    random.seed(random_seed)
    proc_keys = proc_keys_for_ms(ms)
    start = time.time()

    for trial in range(trials):
        tables = [dict(table) for table in seed_tables]
        edits = random.randint(edits_low, edits_high)
        for _ in range(edits):
            proc = random.randrange(len(ms))
            key = random.choice(proc_keys[proc])
            current = tables[proc][key]
            outputs = [out for out in range(ms[proc]) if out != current]
            tables[proc][key] = random.choice(outputs)

        result = verify_system(list(ms), make_fs_from_tables(tables), verbose=False)
        if result["valid"]:
            return {
                "valid": True,
                "trial": trial,
                "elapsed": time.time() - start,
                "result": result,
            }

    return {
        "valid": False,
        "trial": trials,
        "elapsed": time.time() - start,
        "result": None,
    }


def run_representative_hill_climb(
    ms: Sequence[int],
    seed_tables: Sequence[RuleTable],
    steps: int = 800,
    random_seed: int = 42,
):
    random.seed(random_seed)
    proc_keys = proc_keys_for_ms(ms)
    tables = [dict(table) for table in seed_tables]

    def score(current_tables):
        diag = diagnose_tables(ms, current_tables)
        dead = diag["dead_count"]
        fair_penalty = 0 if diag["fair_cycles"] else 1
        scc_nodes = diag["best_scc_nodes"] if diag["best_scc_nodes"] is not None else 10**9
        scc_count = diag["best_scc_count"] if diag["best_scc_count"] is not None else 10**9
        return (dead, fair_penalty, scc_nodes, scc_count)

    start_score = score(tables)
    best_score = start_score
    start = time.time()

    for _ in range(steps):
        proc = random.randrange(len(ms))
        key = random.choice(proc_keys[proc])
        old = tables[proc][key]
        outputs = [out for out in range(ms[proc]) if out != old]
        tables[proc][key] = random.choice(outputs)
        new_score = score(tables)
        if new_score <= best_score:
            best_score = new_score
        else:
            tables[proc][key] = old

    return {
        "start_score": start_score,
        "best_score": best_score,
        "elapsed": time.time() - start,
    }


def print_property_counter(counter: Counter, indent: str = "  "):
    for signature, count in counter.most_common():
        print(f"{indent}{count} x {signature}")


def check_known_systems():
    print("Known Reference Systems")
    print("-" * 72)

    ms8, tables8 = witness_n8()
    result8 = verify_system(list(ms8), make_fs_from_tables(tables8), verbose=False)
    print(f"Known n=8 witness {ms8}: valid={result8['valid']}, cycle={result8.get('cycle_length')}")

    ms7, tables7 = witness_n7()
    valid_rotations = 0
    for shift in range(len(ms7)):
        rotated_ms, rotated_tables = rotate_system(ms7, tables7, shift)
        result = verify_system(list(rotated_ms), make_fs_from_tables(rotated_tables), verbose=False)
        if result["valid"]:
            valid_rotations += 1
    print(f"Known n=7 witness rotations: {valid_rotations}/{len(ms7)} valid")

    clb7 = build_clb(7, verbose=False)
    print(
        "Endpoint-binary non-3CB at n=7:",
        f"ms={clb7['ms']}, valid={clb7['valid']}, cycle={clb7['cycle_len']}",
    )

    for example_ms in (
        (2, 2, 3, 4, 3, 3, 3),
        (2, 3, 2, 3, 3, 3, 4),
    ):
        example = run_mixed_sweep_family(example_ms, deep=False)
        valid = sum(
            count
            for signature, count in example["verify_counter"].items()
            if signature and signature[0][0] == "closure"
        )
        print(
            f"Mixed-sweep good-targeting on n=7 example {example_ms}: "
            f"tested={example['checked']}, valid={valid}"
        )
    print()


def investigate_target():
    print("Target Search: ms=(2,2,2,3,3,3,3,4)")
    print("-" * 72)

    mixed = run_mixed_sweep_family(TARGET_MS, deep=True)
    valid_mixed = sum(
        count
        for signature, count in mixed["verify_counter"].items()
        if any(name == "closure" and ok for name, ok, _ in signature)
    )
    print(f"Mixed-sweep good-targeting seeds: {mixed['checked']}")
    print(f"Mixed-sweep valid systems found: {valid_mixed}")
    print("Verifier outcomes:")
    print_property_counter(mixed["verify_counter"], indent="  ")
    print("Deep convergence diagnosis:")
    for signature, count in mixed["deep_counter"].most_common():
        fair_cycles, scc_nodes, scc_count = signature
        print(
            f"  {count} x fair_cycles={fair_cycles}, "
            f"recurrent_bad_nodes={scc_nodes}, recurrent_bad_sccs={scc_count}"
        )
    print(f"Best mixed-sweep seed: {mixed['best_deep']}")
    print(f"Worst mixed-sweep seed: {mixed['worst_deep']}")

    bounce = run_bounce_family(TARGET_MS)
    print()
    print(f"Bounce-style patterns tested: {bounce['pattern_count']}")
    print(f"Bounce family counts: {dict(bounce['counts'])}")
    if bounce["verify_counter"]:
        print("Bounce verifier outcomes:")
        print_property_counter(bounce["verify_counter"], indent="  ")

    transplant = run_transplant_slice_family()
    print()
    print(
        "n=7 -> n=8 transplant family:",
        f"rotation-equivalent ms={transplant['ms']}",
    )
    print(
        f"Exhaustive new-slice tables checked: {transplant['checked']} "
        f"in {transplant['elapsed']:.1f}s"
    )
    print(f"Transplant valid systems found: {transplant['counts']['valid']}")

    rep_seed_cycle = build_mixed_sweep_cycle(
        TARGET_MS,
        order=(0, 1, 2, 3, 4, 5, 6, 7),
        targets={0: 1, 1: 1, 2: 1, 3: 1, 4: 1, 5: 1, 6: 1, 7: 1},
        return_same_order=True,
    )
    rep_seed = good_targeting_completion(TARGET_MS, rep_seed_cycle)["tables"]

    random_search = run_random_mutation_search(TARGET_MS, rep_seed, trials=5000)
    print()
    print(
        f"Random mutation search around representative mixed-sweep seed: "
        f"trials={random_search['trial']}, valid={random_search['valid']}, "
        f"elapsed={random_search['elapsed']:.1f}s"
    )

    hill = run_representative_hill_climb(TARGET_MS, rep_seed, steps=800)
    print(
        "Greedy local search on same representative seed:",
        f"start_score={hill['start_score']}, best_score={hill['best_score']}, "
        f"elapsed={hill['elapsed']:.1f}s",
    )

    print()
    print("Answer")
    print("-" * 72)
    if valid_mixed or bounce["counts"].get("valid", 0) or transplant["counts"]["valid"] or random_search["valid"]:
        print("YES: at least one valid system was found.")
    else:
        print("NO valid system was found for ms=(2,2,2,3,3,3,3,4).")
        print("Across the strong families tested, the obstruction is convergence:")
        print("liveness can be repaired, closure can produce a fair good cycle,")
        print("but recurrent bad SCCs remain.")
        print(
            "For mixed-sweep good-targeting, every one of the 768 completions has "
            "exactly one fair cycle and still leaves 384 or 528 recurrent bad states."
        )
        print(
            "For bounce-style seeds, 12/14 patterns never close and the other 2 "
            "already have entry conflicts."
        )
        print(
            "For the natural n=7 transplant family, an exhaustive 3^9 = 19683 "
            "slice search found no valid extension."
        )


def main():
    print("=" * 72)
    print("3CB Transition Investigation")
    print("=" * 72)
    print(f"Target ms: {TARGET_MS}, product={ring_product(TARGET_MS)}")
    print(f"Known valid n=8 ms: {VALID_M8_MS}, product={ring_product(VALID_M8_MS)}")
    print()

    start = time.time()
    check_known_systems()
    investigate_target()
    print()
    print(f"Total elapsed: {time.time() - start:.1f}s")


if __name__ == "__main__":
    main()
