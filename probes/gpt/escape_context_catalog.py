from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict


def center_local_context_key(example: dict) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    m_window = tuple(example["m_window"])
    state_window = tuple(example["state_window"])
    return (m_window[1:4], state_window[1:4])


def make_entry(key: tuple[tuple[int, int, int], tuple[int, int, int]]) -> dict:
    return {
        "context_key": key,
        "forced_proc_kind": "unknown",
        "n_values": set(),
        "occurrences_by_n": Counter(),
        "raw_type_counts_by_n": Counter(),
        "observed_forced_outputs": set(),
        "raw_types_with_multiple_outputs": 0,
        "outer_m_pairs": Counter(),
        "outer_state_pairs": Counter(),
        "raw_windows": [],
    }


def serialize_entry(entry: dict) -> dict:
    return {
        "context_key": [list(entry["context_key"][0]), list(entry["context_key"][1])],
        "forced_proc_kind": entry["forced_proc_kind"],
        "n_values": sorted(entry["n_values"]),
        "occurrences_by_n": {str(n): entry["occurrences_by_n"][n] for n in sorted(entry["occurrences_by_n"])},
        "raw_type_counts_by_n": {
            str(n): entry["raw_type_counts_by_n"][n] for n in sorted(entry["raw_type_counts_by_n"])
        },
        "observed_forced_outputs": sorted(entry["observed_forced_outputs"]),
        "raw_types_with_multiple_outputs": entry["raw_types_with_multiple_outputs"],
        "outer_m_pairs": {str(k): v for k, v in sorted(entry["outer_m_pairs"].items())},
        "outer_state_pairs": {str(k): v for k, v in sorted(entry["outer_state_pairs"].items())},
        "raw_windows": sorted(
            entry["raw_windows"],
            key=lambda row: (row["n"], row["m_window"], row["state_window"]),
        ),
    }


def format_key(key: tuple[tuple[int, int, int], tuple[int, int, int]]) -> str:
    return f"m={key[0]} state={key[1]}"


def build_catalog(summary: dict) -> dict:
    entries: dict[tuple[tuple[int, int, int], tuple[int, int, int]], dict] = {}
    group_counts = Counter()

    for n_str, stats in summary["per_n"].items():
        n = int(n_str)
        for type_data in stats["types"].values():
            example = type_data["examples"][0]
            key = center_local_context_key(example)
            entry = entries.setdefault(key, make_entry(key))
            entry["forced_proc_kind"] = example["forced_proc_kind"]
            entry["n_values"].add(n)
            entry["occurrences_by_n"][n] += type_data["occurrences"]
            entry["raw_type_counts_by_n"][n] += 1
            outputs = sorted(int(v) for v in type_data["forced_new_val_counts"])
            entry["observed_forced_outputs"].update(outputs)
            if len(outputs) > 1:
                entry["raw_types_with_multiple_outputs"] += 1
            outer_m_pair = (example["m_window"][0], example["m_window"][4])
            outer_state_pair = (example["state_window"][0], example["state_window"][4])
            entry["outer_m_pairs"][outer_m_pair] += 1
            entry["outer_state_pairs"][outer_state_pair] += 1
            entry["raw_windows"].append(
                {
                    "n": n,
                    "m_window": list(example["m_window"]),
                    "state_window": list(example["state_window"]),
                    "occurrences": type_data["occurrences"],
                    "forced_outputs": outputs,
                }
            )

    for key in entries:
        group_counts[key[0]] += 1

    serialized_entries = [serialize_entry(entries[key]) for key in sorted(entries)]
    return {
        "source_n_values": sorted(int(n_str) for n_str in summary["per_n"]),
        "class_count": len(serialized_entries),
        "group_counts_by_m_triple": {
            str(k): group_counts[k] for k in sorted(group_counts)
        },
        "entries": serialized_entries,
    }


def write_markdown(catalog: dict, path: str) -> None:
    grouped = defaultdict(list)
    for entry in catalog["entries"]:
        grouped[tuple(entry["context_key"][0])].append(entry)

    lines = [
        "# Centered Local-Context Escape Catalog",
        "",
        f"Observed n-values: {catalog['source_n_values']}",
        f"Observed classes: {catalog['class_count']}",
        "",
        "## Group Counts by Centered m-Triple",
        "",
    ]
    for m_triple, entries in sorted(grouped.items()):
        lines.append(f"- `{m_triple}`: {len(entries)} classes")

    for m_triple in sorted(grouped):
        lines.extend(["", f"## Centered m-Triple `{m_triple}`", ""])
        for entry in sorted(grouped[m_triple], key=lambda row: (tuple(row["context_key"][1]), row["forced_proc_kind"])):
            context = format_key((tuple(entry["context_key"][0]), tuple(entry["context_key"][1])))
            lines.append(f"### `{context}`")
            lines.append("")
            lines.append(f"- Forced processor kind: `{entry['forced_proc_kind']}`")
            lines.append(f"- Present at n: `{entry['n_values']}`")
            lines.append(f"- Raw type counts by n: `{entry['raw_type_counts_by_n']}`")
            lines.append(f"- Occurrences by n: `{entry['occurrences_by_n']}`")
            lines.append(f"- Observed forced outputs: `{entry['observed_forced_outputs']}`")
            lines.append(
                f"- Raw windows with multiple outputs: `{entry['raw_types_with_multiple_outputs']}`"
            )
            lines.append(f"- Outer m pairs observed: `{entry['outer_m_pairs']}`")
            lines.append(f"- Outer state pairs observed: `{entry['outer_state_pairs']}`")
            sample_windows = entry["raw_windows"][:4]
            for raw in sample_windows:
                lines.append(
                    "- Sample raw window: "
                    f"`n={raw['n']} m={tuple(raw['m_window'])} state={tuple(raw['state_window'])} "
                    f"outputs={tuple(raw['forced_outputs'])} occ={raw['occurrences']}`"
                )
            if len(entry["raw_windows"]) > len(sample_windows):
                lines.append(f"- Additional raw windows omitted: `{len(entry['raw_windows']) - len(sample_windows)}`")

    with open(path, "w") as handle:
        handle.write("\n".join(lines) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--input",
        default="probes/gpt/escape_local_types_summary_n9.json",
        help="input JSON summary from extract_escape_local_types.py",
    )
    parser.add_argument(
        "--json-out",
        default="probes/gpt/escape_center_local_context_catalog.json",
        help="where to write the centered-local-context catalog JSON",
    )
    parser.add_argument(
        "--md-out",
        default="probes/gpt/escape_center_local_context_catalog.md",
        help="where to write the centered-local-context catalog markdown",
    )
    args = parser.parse_args()

    with open(args.input) as handle:
        summary = json.load(handle)

    catalog = build_catalog(summary)
    with open(args.json_out, "w") as handle:
        json.dump(catalog, handle, indent=2, sort_keys=True)
    write_markdown(catalog, args.md_out)

    print("Centered local-context catalog")
    print(f"  Source n-values: {catalog['source_n_values']}")
    print(f"  Classes:         {catalog['class_count']}")
    for m_triple, count in catalog["group_counts_by_m_triple"].items():
        print(f"  {m_triple}: {count}")


if __name__ == "__main__":
    main()
