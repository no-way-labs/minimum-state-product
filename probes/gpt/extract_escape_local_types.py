from __future__ import annotations

import argparse
import json
import os
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product as cartesian

sys.path.append(os.path.dirname(__file__))

import verify_lower_bound as vlb


WINDOW_OFFSETS = (-2, -1, 0, 1, 2)
KIND_NAMES = {2: "binary", 3: "ternary", 4: "quaternary"}


@dataclass(frozen=True)
class CycleInstance:
    case: str
    case_id: str
    n: int
    ms: tuple[int, ...]
    cycle: tuple[tuple[int, ...], ...]


def center_local_context_key(m_window: tuple[int, ...], state_window: tuple[int, ...], sample: dict) -> tuple:
    return (m_window[1:4], state_window[1:4])


def center_zero_nonzero_key(
    m_window: tuple[int, ...], state_window: tuple[int, ...], sample: dict
) -> tuple:
    return (m_window[1:4], tuple(0 if value == 0 else 1 for value in state_window[1:4]))


def center_kind_state_triple_key(
    m_window: tuple[int, ...], state_window: tuple[int, ...], sample: dict
) -> tuple:
    return (sample["forced_proc_kind"], state_window[1:4])


def m_window_only_key(m_window: tuple[int, ...], state_window: tuple[int, ...], sample: dict) -> tuple:
    return m_window


QUOTIENT_SPECS = (
    (
        "center_local_context",
        "centered local context (m_{i-1..i+1}, p_{i-1..i+1})",
        center_local_context_key,
    ),
    (
        "center_zero_nonzero",
        "centered m-triple plus 0/nonzero pattern on p_{i-1..i+1}",
        center_zero_nonzero_key,
    ),
    (
        "center_kind_state_triple",
        "forced processor kind plus centered state triple",
        center_kind_state_triple_key,
    ),
    (
        "m_window_only",
        "radius-2 architecture window m_{i-2..i+2}",
        m_window_only_key,
    ),
)


def kind_name(m: int) -> str:
    return KIND_NAMES.get(m, f"{m}-ary")


def signed_offset(n: int, src: int, dst: int) -> int:
    delta = (dst - src) % n
    if delta > n // 2:
        delta -= n
    return delta


def nearest_offset(ms: tuple[int, ...], center: int, target_m: int) -> int | None:
    offsets = [
        signed_offset(len(ms), center, idx)
        for idx, value in enumerate(ms)
        if value == target_m and idx != center
    ]
    if not offsets:
        return None
    return min(offsets, key=lambda off: (abs(off), off))


def all_configs(ms: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    return tuple(cartesian(*[range(m) for m in ms]))


def iter_uniform_cycles(n_min: int = 5, n_max: int = 8):
    for n in range(n_min, n_max + 1):
        target = 32 * (3 ** (n - 4))
        for num_bin in range(3, n + 1):
            product = (2 ** num_bin) * (3 ** (n - num_bin))
            if product >= target:
                continue

            classes = vlb.get_rotation_classes(n, num_bin, max_consec=3)
            for cls in classes:
                ms = tuple(cls)
                nb_procs = [i for i in range(n) if ms[i] > 2]
                bin_procs = [i for i in range(n) if ms[i] == 2]

                nb_ranges = [range(1, ms[p]) for p in nb_procs]
                nb_combos = list(cartesian(*nb_ranges)) if nb_ranges else [()]

                for combo in nb_combos:
                    nb_vals = {}
                    for i, p in enumerate(nb_procs):
                        nb_vals[p] = combo[i]
                    for p in bin_procs:
                        nb_vals[p] = 1

                    cyc = vlb.construct_sweep_cycle(list(ms), n, nb_vals)
                    if cyc is None:
                        continue
                    ok, _det, _msg = vlb.check_cycle_consistency(cyc, n, list(ms))
                    if not ok:
                        continue

                    combo_label = ",".join(str(nb_vals[p]) for p in nb_procs) if nb_procs else "none"
                    yield CycleInstance(
                        case="uniform",
                        case_id=f"uniform:n={n}:ms={','.join(map(str, ms))}:nb={combo_label}",
                        n=n,
                        ms=ms,
                        cycle=tuple(cyc),
                    )


def iter_n9_canonical_cycle():
    n = 9
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    nb_vals = {i: 1 for i in range(n)}
    cyc = vlb.construct_sweep_cycle(list(ms), n, nb_vals)
    if cyc is None:
        return
    ok, _det, _msg = vlb.check_cycle_consistency(cyc, n, list(ms))
    if not ok:
        return
    yield CycleInstance(
        case="n9-canonical",
        case_id="n9-canonical:ms=2,2,2,3,3,3,3,3,3:nb=1,1,1,1,1,1",
        n=n,
        ms=ms,
        cycle=tuple(cyc),
    )


def iter_nonuniform_cycles(n_min: int = 5, n_max: int = 7):
    from itertools import permutations

    for n in range(n_min, min(n_max + 1, 8)):
        ms = tuple([2] * 3 + [3] * (n - 3))
        nb_vals = {i: 1 for i in range(n)}
        tested_pairs = set()

        for up_perm in permutations(range(n)):
            for down_type in ["same", "reverse", "forward"]:
                if down_type == "same":
                    down_perm = list(up_perm)
                elif down_type == "reverse":
                    down_perm = list(reversed(up_perm))
                else:
                    down_perm = list(range(n))

                pair_key = (up_perm, tuple(down_perm))
                if pair_key in tested_pairs:
                    continue
                tested_pairs.add(pair_key)

                cyc = vlb.construct_sweep_cycle(list(ms), n, nb_vals, list(up_perm), down_perm)
                if cyc is None:
                    continue
                ok, _det, _msg = vlb.check_cycle_consistency(cyc, n, list(ms))
                if not ok:
                    continue

                yield CycleInstance(
                    case="nonuniform",
                    case_id=(
                        f"nonuniform:n={n}:up={','.join(map(str, up_perm))}:"
                        f"down={','.join(map(str, down_perm))}"
                    ),
                    n=n,
                    ms=ms,
                    cycle=tuple(cyc),
                )


def iter_length11_n5_cycles():
    n = 5
    for ms in [(2, 2, 2, 3, 3), (2, 2, 3, 2, 3)]:
        bin_procs = [i for i in range(n) if ms[i] == 2]
        ter_procs = [i for i in range(n) if ms[i] == 3]

        for tri_proc in ter_procs:
            other_ter = [p for p in ter_procs if p != tri_proc]
            if len(other_ter) != 1:
                continue
            other_ter = other_ter[0]

            for v_other in range(1, 3):
                move_defs = {}
                idx = 0
                for p in bin_procs:
                    move_defs[idx] = (p, 1)
                    idx += 1
                tri_a = idx
                move_defs[idx] = (tri_proc, 1)
                idx += 1
                tri_b = idx
                move_defs[idx] = (tri_proc, 2)
                idx += 1
                ot_up = idx
                move_defs[idx] = (other_ter, v_other)
                idx += 1
                bin_down_start = idx
                for p in bin_procs:
                    move_defs[idx] = (p, 0)
                    idx += 1
                tri_c = idx
                move_defs[idx] = (tri_proc, 0)
                idx += 1
                ot_down = idx
                move_defs[idx] = (other_ter, 0)
                idx += 1

                deps = {}
                for i, _p in enumerate(bin_procs):
                    deps[bin_down_start + i] = frozenset([i])
                deps[tri_b] = frozenset([tri_a])
                deps[tri_c] = frozenset([tri_b])
                deps[ot_down] = frozenset([ot_up])

                seen = set()

                def backtrack(done, config, cycle):
                    if len(done) == 11:
                        cycle_list = list(cycle)
                        if cycle_list[-1] != cycle_list[0]:
                            return
                        cycle_list = cycle_list[:-1]
                        if len(set(cycle_list)) != len(cycle_list):
                            return
                        for ci in range(len(cycle_list)):
                            c = cycle_list[ci]
                            c_next = cycle_list[(ci + 1) % len(cycle_list)]
                            if sum(1 for j in range(n) if c[j] != c_next[j]) != 1:
                                return
                        ck = tuple(cycle_list)
                        if ck in seen:
                            return
                        seen.add(ck)
                        ok, _det, _msg = vlb.check_cycle_consistency(cycle_list, n, list(ms))
                        if not ok:
                            return
                        yield CycleInstance(
                            case="length11",
                            case_id=(
                                f"length11:n=5:ms={','.join(map(str, ms))}:"
                                f"tri={tri_proc}:other={other_ter}:v={v_other}:"
                                f"cycle={len(seen)}"
                            ),
                            n=n,
                            ms=tuple(ms),
                            cycle=tuple(cycle_list),
                        )
                        return

                    for m_idx in range(11):
                        if m_idx in done:
                            continue
                        if m_idx in deps and not deps[m_idx].issubset(done):
                            continue
                        proc, new_val = move_defs[m_idx]
                        if config[proc] == new_val:
                            continue
                        old_val = config[proc]
                        config[proc] = new_val
                        cycle.append(tuple(config))
                        yield from backtrack(done | frozenset([m_idx]), config, cycle)
                        config[proc] = old_val
                        cycle.pop()

                config = [0] * n
                cycle = [tuple(config)]
                yield from backtrack(frozenset(), config, cycle)


def iter_mixed_quaternary_cycles(n_min: int = 6, n_max: int = 8):
    from itertools import permutations as perms

    mixed_cases = []
    for n in range(n_min, n_max + 1):
        target = 32 * (3 ** (n - 4))
        for num_bin in range(4, n):
            remaining = n - num_bin
            if remaining < 1:
                continue
            for num_quat in range(1, remaining + 1):
                num_ter = remaining - num_quat
                product = (2 ** num_bin) * (4 ** num_quat) * (3 ** num_ter)
                if product >= target:
                    continue
                seen_classes = set()
                vals = [2] * num_bin + [4] * num_quat + [3] * num_ter
                for perm in set(perms(vals)):
                    ok = True
                    for start in range(n):
                        count = 0
                        for offset in range(n):
                            if perm[(start + offset) % n] == 2:
                                count += 1
                            else:
                                break
                            if count > 3:
                                ok = False
                                break
                        if not ok:
                            break
                    if not ok:
                        continue
                    rotations = [perm[i:] + perm[:i] for i in range(n)]
                    canonical = min(rotations)
                    if canonical not in seen_classes:
                        seen_classes.add(canonical)
                        mixed_cases.append((n, tuple(canonical)))

    for n, ms in mixed_cases:
        nb_procs = [i for i in range(n) if ms[i] > 2]
        bin_procs = [i for i in range(n) if ms[i] == 2]
        nb_ranges = [range(1, ms[p]) for p in nb_procs]
        nb_combos = list(cartesian(*nb_ranges)) if nb_ranges else [()]

        for combo in nb_combos:
            nb_vals = {}
            for i, p in enumerate(nb_procs):
                nb_vals[p] = combo[i]
            for p in bin_procs:
                nb_vals[p] = 1

            cyc = vlb.construct_sweep_cycle(list(ms), n, nb_vals)
            if cyc is None:
                continue
            ok, _det, _msg = vlb.check_cycle_consistency(cyc, n, list(ms))
            if not ok:
                continue

            combo_label = ",".join(str(nb_vals[p]) for p in nb_procs) if nb_procs else "none"
            yield CycleInstance(
                case="mixed-quaternary",
                case_id=f"mixed:n={n}:ms={','.join(map(str, ms))}:nb={combo_label}",
                n=n,
                ms=ms,
                cycle=tuple(cyc),
            )


def make_type_key(ms: tuple[int, ...], config: tuple[int, ...], proc: int) -> tuple:
    m_window = tuple(ms[(proc + off) % len(ms)] for off in WINDOW_OFFSETS)
    state_window = tuple(config[(proc + off) % len(ms)] for off in WINDOW_OFFSETS)
    return (m_window, state_window)


def sample_record(
    instance: CycleInstance,
    config: tuple[int, ...],
    proc: int,
    new_val: int,
    center_escape: bool,
    escape_procs: tuple[int, ...],
) -> dict:
    n = instance.n
    ms = instance.ms
    m_window = tuple(ms[(proc + off) % n] for off in WINDOW_OFFSETS)
    state_window = tuple(config[(proc + off) % n] for off in WINDOW_OFFSETS)
    return {
        "case": instance.case,
        "case_id": instance.case_id,
        "n": n,
        "ms": list(ms),
        "config": list(config),
        "forced_proc": proc,
        "forced_proc_kind": kind_name(ms[proc]),
        "forced_new_val": new_val,
        "m_window": list(m_window),
        "state_window": list(state_window),
        "local_binary_offsets": [off for off in WINDOW_OFFSETS if ms[(proc + off) % n] == 2],
        "local_quaternary_offsets": [off for off in WINDOW_OFFSETS if ms[(proc + off) % n] == 4],
        "nearest_quaternary_offset": nearest_offset(ms, proc, 4),
        "nearest_binary_offset": nearest_offset(ms, proc, 2),
        "center_escape": center_escape,
        "escaping_forced_processors": list(escape_procs),
        "escaping_forced_offsets": [signed_offset(n, proc, other) for other in escape_procs],
    }


def analyze_cycle(
    instance: CycleInstance,
    summary: dict,
    jsonl_handle=None,
) -> None:
    ms = instance.ms
    n = instance.n
    cycle = instance.cycle
    ok, det, msg = vlb.check_cycle_consistency(list(cycle), n, list(ms))
    if not ok:
        raise RuntimeError(f"inconsistent cycle leaked into analysis: {instance.case_id}: {msg}")

    good_set = set(cycle)
    stats_n = summary["per_n"][n]
    stats_n["consistent_cycles"] += 1

    for config in all_configs(ms):
        if config in good_set:
            continue

        forced = []
        for proc in range(n):
            left = config[(proc - 1) % n]
            self_state = config[proc]
            right = config[(proc + 1) % n]
            key = (proc, left, self_state, right)
            if key not in det or det[key] == self_state:
                continue
            new_val = det[key]
            new_config = list(config)
            new_config[proc] = new_val
            new_config_t = tuple(new_config)
            forced.append((proc, new_val, new_config_t not in good_set))

        if not forced:
            continue

        escape_procs = tuple(proc for proc, _new_val, escapes in forced if escapes)
        if not escape_procs:
            raise RuntimeError(f"escape lemma failed unexpectedly at {instance.case_id} config={config}")

        stats_n["forced_configs"] += 1
        summary["totals"]["forced_configs"] += 1

        for proc, new_val, escapes in forced:
            stats_n["forced_instances"] += 1
            summary["totals"]["forced_instances"] += 1

            type_key = make_type_key(ms, config, proc)
            type_stats = stats_n["types"][type_key]
            type_stats["occurrences"] += 1
            type_stats["case_counts"][instance.case] += 1
            type_stats["proc_kind_counts"][kind_name(ms[proc])] += 1
            type_stats["center_escape_counts"][str(escapes)] += 1
            type_stats["forced_new_val_counts"][str(new_val)] += 1
            type_stats["escape_offset_counts"][tuple(signed_offset(n, proc, other) for other in escape_procs)] += 1
            type_stats["n_values"].add(n)
            if not type_stats["examples"]:
                type_stats["examples"].append(
                    sample_record(instance, config, proc, new_val, escapes, escape_procs)
                )

            if jsonl_handle is not None:
                record = sample_record(instance, config, proc, new_val, escapes, escape_procs)
                jsonl_handle.write(json.dumps(record, sort_keys=True) + "\n")


def simplify_type_stats(type_stats: dict) -> dict:
    return {
        "occurrences": type_stats["occurrences"],
        "case_counts": dict(type_stats["case_counts"]),
        "proc_kind_counts": dict(type_stats["proc_kind_counts"]),
        "center_escape_counts": dict(type_stats["center_escape_counts"]),
        "forced_new_val_counts": dict(type_stats["forced_new_val_counts"]),
        "escape_offset_counts": {str(k): v for k, v in type_stats["escape_offset_counts"].items()},
        "examples": type_stats["examples"],
    }


def merge_type_stats(dst: dict, src: dict) -> None:
    dst["occurrences"] += src["occurrences"]
    dst["case_counts"].update(src["case_counts"])
    dst["proc_kind_counts"].update(src["proc_kind_counts"])
    dst["center_escape_counts"].update(src["center_escape_counts"])
    dst["forced_new_val_counts"].update(src["forced_new_val_counts"])
    dst["escape_offset_counts"].update(src["escape_offset_counts"])
    dst["n_values"].update(src["n_values"])
    if not dst["examples"] and src["examples"]:
        dst["examples"].append(src["examples"][0])


def summarize_partition(partition_by_n: dict[int, dict], description: str | None = None) -> dict:
    out = {
        "description": description,
        "per_n": {},
        "stabilization": {},
    }

    class_sets = {}
    all_classes = set()
    for n, classes in sorted(partition_by_n.items()):
        class_sets[n] = set(classes)
        all_classes |= class_sets[n]
        center_escape_profiles = Counter()
        deterministic_output_classes = 0
        for class_stats in classes.values():
            has_true = bool(class_stats["center_escape_counts"].get("True"))
            has_false = bool(class_stats["center_escape_counts"].get("False"))
            if has_true and has_false:
                center_escape_profiles["mixed"] += 1
            elif has_true:
                center_escape_profiles["always_true"] += 1
            elif has_false:
                center_escape_profiles["always_false"] += 1
            if len(class_stats["forced_new_val_counts"]) == 1:
                deterministic_output_classes += 1
        out["per_n"][str(n)] = {
            "distinct_class_count": len(classes),
            "center_escape_profile_counts": dict(center_escape_profiles),
            "classes_with_deterministic_forced_output": deterministic_output_classes,
            "classes": {
                str(key): simplify_type_stats(class_stats)
                for key, class_stats in sorted(classes.items(), key=lambda kv: str(kv[0]))
            },
        }

    ns = sorted(class_sets)
    if ns:
        universal = set.intersection(*(class_sets[n] for n in ns))
    else:
        universal = set()

    new_classes = {}
    seen_so_far = set()
    last_n_with_new_class = None
    for n in ns:
        new_here = class_sets[n] - seen_so_far
        if new_here:
            last_n_with_new_class = n
        new_classes[str(n)] = sorted(str(key) for key in new_here)
        seen_so_far |= class_sets[n]

    varying_escape = []
    varying_output = []
    stable_center_escape = 0
    stable_escape = 0
    stable_output = 0
    for key in all_classes:
        center_behaviors = set()
        escape_offset_behaviors = set()
        output_values = set()
        for n in ns:
            class_stats = partition_by_n[n].get(key)
            if class_stats is None:
                continue
            if class_stats["center_escape_counts"].get("True"):
                center_behaviors.add(True)
            if class_stats["center_escape_counts"].get("False"):
                center_behaviors.add(False)
            escape_offset_behaviors |= set(class_stats["escape_offset_counts"])
            output_values |= {int(value) for value in class_stats["forced_new_val_counts"]}
        if len(center_behaviors) == 1:
            stable_center_escape += 1
        if len(center_behaviors) == 1 and len(escape_offset_behaviors) == 1:
            stable_escape += 1
        else:
            varying_escape.append(str(key))
        if len(output_values) == 1:
            stable_output += 1
        else:
            varying_output.append(str(key))

    out["stabilization"] = {
        "n_values": ns,
        "distinct_class_counts": {str(n): len(class_sets[n]) for n in ns},
        "new_classes_by_n": new_classes,
        "universal_class_count": len(universal),
        "universal_classes": sorted(str(key) for key in universal),
        "observed_class_count": len(all_classes),
        "observed_classes_with_stable_center_escape": stable_center_escape,
        "observed_classes_with_stable_escape_mechanism": stable_escape,
        "observed_classes_with_deterministic_forced_output": stable_output,
        "observed_classes_with_varying_escape_mechanism": varying_escape,
        "observed_classes_with_varying_forced_output": varying_output,
        "last_n_with_new_class": last_n_with_new_class,
        "stabilized_through_observed_range": bool(ns) and last_n_with_new_class is not None and last_n_with_new_class < ns[-1],
    }
    return out


def finalize_summary(summary: dict) -> dict:
    out = {
        "totals": summary["totals"],
        "per_n": {},
        "stabilization": {},
        "quotients": {},
    }

    type_sets = {}
    m_window_sets = {}
    for n, stats_n in sorted(summary["per_n"].items()):
        type_sets[n] = set(stats_n["types"])
        m_window_sets[n] = {key[0] for key in stats_n["types"]}
        center_escape_profiles = Counter()
        for type_stats in stats_n["types"].values():
            has_true = bool(type_stats["center_escape_counts"].get("True"))
            has_false = bool(type_stats["center_escape_counts"].get("False"))
            if has_true and has_false:
                center_escape_profiles["mixed"] += 1
            elif has_true:
                center_escape_profiles["always_true"] += 1
            elif has_false:
                center_escape_profiles["always_false"] += 1
        out["per_n"][str(n)] = {
            "consistent_cycles": stats_n["consistent_cycles"],
            "forced_configs": stats_n["forced_configs"],
            "forced_instances": stats_n["forced_instances"],
            "distinct_type_count": len(stats_n["types"]),
            "distinct_m_window_count": len(m_window_sets[n]),
            "m_windows": sorted(str(mw) for mw in m_window_sets[n]),
            "center_escape_profile_counts": dict(center_escape_profiles),
            "types": {
                str(key): simplify_type_stats(type_stats)
                for key, type_stats in sorted(stats_n["types"].items(), key=lambda kv: (kv[0][0], kv[0][1]))
            },
        }

    ns = sorted(type_sets)
    if ns:
        universal = set.intersection(*(type_sets[n] for n in ns))
    else:
        universal = set()

    new_types = {}
    new_m_windows = {}
    seen_so_far = set()
    seen_m_windows = set()
    for n in ns:
        new_here = type_sets[n] - seen_so_far
        new_types[str(n)] = sorted(str(key) for key in new_here)
        seen_so_far |= type_sets[n]
        new_mw_here = m_window_sets[n] - seen_m_windows
        new_m_windows[str(n)] = sorted(str(mw) for mw in new_mw_here)
        seen_m_windows |= m_window_sets[n]

    varying_escape = []
    stable_escape = 0
    stable_center_escape = 0
    for key in universal:
        behaviors = set()
        offset_behaviors = set()
        center_behaviors = set()
        for n in ns:
            type_stats = summary["per_n"][n]["types"][key]
            behaviors |= set(type_stats["center_escape_counts"])
            offset_behaviors |= set(type_stats["escape_offset_counts"])
            if type_stats["center_escape_counts"].get("True"):
                center_behaviors.add(True)
            if type_stats["center_escape_counts"].get("False"):
                center_behaviors.add(False)
        if len(center_behaviors) == 1:
            stable_center_escape += 1
        if len(behaviors) == 1 and len(offset_behaviors) == 1:
            stable_escape += 1
        else:
            varying_escape.append(str(key))

    out["stabilization"] = {
        "n_values": ns,
        "distinct_type_counts": {str(n): len(type_sets[n]) for n in ns},
        "distinct_m_window_counts": {str(n): len(m_window_sets[n]) for n in ns},
        "new_types_by_n": new_types,
        "new_m_windows_by_n": new_m_windows,
        "universal_type_count": len(universal),
        "universal_types": sorted(str(key) for key in universal),
        "universal_types_with_stable_center_escape": stable_center_escape,
        "universal_types_with_stable_escape_mechanism": stable_escape,
        "universal_types_with_varying_escape_mechanism": varying_escape,
    }

    for quotient_name, description, key_fn in QUOTIENT_SPECS:
        quotient_by_n = {}
        for n, stats_n in summary["per_n"].items():
            quotient_classes = defaultdict(empty_type_stats)
            for raw_key, raw_stats in stats_n["types"].items():
                sample = raw_stats["examples"][0]
                quotient_key = key_fn(raw_key[0], raw_key[1], sample)
                merge_type_stats(quotient_classes[quotient_key], raw_stats)
            quotient_by_n[n] = quotient_classes
        out["quotients"][quotient_name] = summarize_partition(quotient_by_n, description)
    return out


def empty_type_stats():
    return {
        "occurrences": 0,
        "case_counts": Counter(),
        "proc_kind_counts": Counter(),
        "center_escape_counts": Counter(),
        "forced_new_val_counts": Counter(),
        "escape_offset_counts": Counter(),
        "n_values": set(),
        "examples": [],
    }


def print_summary(out: dict) -> None:
    print("Escape local-type summary")
    print(f"  Forced configs checked:   {out['totals']['forced_configs']}")
    print(f"  Forced proc instances:    {out['totals']['forced_instances']}")
    print()
    for n_str, stats in out["per_n"].items():
        print(
            f"  n={n_str}: cycles={stats['consistent_cycles']} "
            f"forced_configs={stats['forced_configs']} "
            f"forced_instances={stats['forced_instances']} "
            f"distinct_types={stats['distinct_type_count']} "
            f"distinct_m_windows={stats['distinct_m_window_count']}"
        )
    print()
    stab = out["stabilization"]
    print(f"  Universal types across {stab['n_values']}: {stab['universal_type_count']}")
    print(
        "  Universal types with stable center escape: "
        f"{stab['universal_types_with_stable_center_escape']}"
    )
    print(
        "  Universal types with stable escape mechanism: "
        f"{stab['universal_types_with_stable_escape_mechanism']}"
    )
    print(
        "  Universal types with varying escape mechanism: "
        f"{len(stab['universal_types_with_varying_escape_mechanism'])}"
    )
    print()
    for n_str, type_list in stab["new_types_by_n"].items():
        print(f"  New types first seen at n={n_str}: {len(type_list)}")
    for n_str, m_window_list in stab["new_m_windows_by_n"].items():
        print(f"  New m_windows first seen at n={n_str}: {len(m_window_list)}")
    print()
    for quotient_name, quotient in out["quotients"].items():
        qstab = quotient["stabilization"]
        counts = ", ".join(
            f"n={n_str}:{count}" for n_str, count in qstab["distinct_class_counts"].items()
        )
        print(f"  Quotient {quotient_name}: {quotient['description']}")
        print(f"    Distinct classes: {counts}")
        for n_str, class_list in qstab["new_classes_by_n"].items():
            print(f"    New classes first seen at n={n_str}: {len(class_list)}")
        print(
            "    Observed classes with deterministic forced output: "
            f"{qstab['observed_classes_with_deterministic_forced_output']}/"
            f"{qstab['observed_class_count']}"
        )
        print(
            "    Observed classes with stable center escape: "
            f"{qstab['observed_classes_with_stable_center_escape']}/"
            f"{qstab['observed_class_count']}"
        )
        print(
            "    Last n with a new class: "
            f"{qstab['last_n_with_new_class']} "
            f"(stabilized through observed range: {qstab['stabilized_through_observed_range']})"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        choices=["uniform", "full"],
        default="uniform",
        help="cycle family to analyze; default matches the 514,840-config Escape Lemma dataset",
    )
    parser.add_argument(
        "--include-n9-canonical",
        action="store_true",
        help="also analyze one canonical n=9 uniform-sweep cycle as a supplementary data point",
    )
    parser.add_argument(
        "--json-out",
        help="write aggregated summary JSON to this path",
    )
    parser.add_argument(
        "--jsonl-out",
        help="write one JSON line per forced processor instance to this path",
    )
    args = parser.parse_args()

    summary = {
        "totals": {
            "forced_configs": 0,
            "forced_instances": 0,
        },
        "per_n": defaultdict(
            lambda: {
                "consistent_cycles": 0,
                "forced_configs": 0,
                "forced_instances": 0,
                "types": defaultdict(empty_type_stats),
            }
        ),
    }

    jsonl_handle = open(args.jsonl_out, "w") if args.jsonl_out else None
    try:
        for instance in iter_uniform_cycles():
            analyze_cycle(instance, summary, jsonl_handle)
        if args.dataset == "full":
            for instance in iter_nonuniform_cycles():
                analyze_cycle(instance, summary, jsonl_handle)
            for instance in iter_length11_n5_cycles():
                analyze_cycle(instance, summary, jsonl_handle)
            for instance in iter_mixed_quaternary_cycles():
                analyze_cycle(instance, summary, jsonl_handle)
        if args.include_n9_canonical:
            for instance in iter_n9_canonical_cycle():
                analyze_cycle(instance, summary, jsonl_handle)
    finally:
        if jsonl_handle is not None:
            jsonl_handle.close()

    out = finalize_summary(summary)
    print_summary(out)

    if args.json_out:
        with open(args.json_out, "w") as handle:
            json.dump(out, handle, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
