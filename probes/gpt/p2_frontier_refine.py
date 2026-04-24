from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed


SCREENED_RE = re.compile(r"screened=(\d+)\s+survivors=(\d+)\s+elapsed=([0-9.]+)s")


def parse_prefix(prefix_text: str) -> tuple[int, ...]:
    return tuple(int(part) for part in prefix_text.split(","))


def format_prefix(prefix: tuple[int, ...]) -> str:
    return ",".join(str(part) for part in prefix)


def child_prefixes(base_prefixes: list[tuple[int, ...]], processor_count: int) -> list[tuple[int, ...]]:
    children: list[tuple[int, ...]] = []
    for base in base_prefixes:
        for processor in range(processor_count):
            children.append(base + (processor,))
    return children


def screen_prefix_subprocess(
    state_counts: tuple[int, ...],
    mover_prefix: tuple[int, ...],
    time_limit: float,
    max_cycles: int,
) -> tuple[tuple[int, ...], int, int, float]:
    args = [
        sys.executable,
        "probes/gpt/p2_cycle_screen.py",
        format_prefix(state_counts),
        "--time-limit",
        str(time_limit),
        "--max-cycles",
        str(max_cycles),
        "--mover-prefix",
        format_prefix(mover_prefix),
    ]
    completed = subprocess.run(args, capture_output=True, text=True, check=False)
    output = completed.stdout + completed.stderr
    matches = SCREENED_RE.findall(output)
    if not matches:
        raise RuntimeError(f"could not parse screen output for prefix {mover_prefix}:\n{output}")
    screened, survivors, elapsed = matches[-1]
    return mover_prefix, int(screened), int(survivors), float(elapsed)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("base_prefixes", nargs="+", help="comma-separated base mover prefixes")
    parser.add_argument("--time-limit", type=float, default=3600.0)
    parser.add_argument("--max-cycles", type=int, default=100_000_000)
    parser.add_argument("--max-workers", type=int, default=7)
    args = parser.parse_args()

    state_counts = parse_prefix(args.state_counts)
    base_prefixes = [parse_prefix(text) for text in args.base_prefixes]
    processor_count = len(state_counts)
    started = time.time()

    children = child_prefixes(base_prefixes, processor_count)
    print(
        f"screening {len(children)} depth-{len(base_prefixes[0]) + 1} prefixes "
        f"from {len(base_prefixes)} base prefixes for {state_counts} "
        f"with time_limit={args.time_limit}s"
    , flush=True)

    base_totals = {
        base: {"done": 0, "screened": 0, "survivors": 0}
        for base in base_prefixes
    }

    with ThreadPoolExecutor(max_workers=args.max_workers) as executor:
        future_map = {
            executor.submit(
                screen_prefix_subprocess,
                state_counts,
                child,
                args.time_limit,
                args.max_cycles,
            ): child
            for child in children
        }
        for future in as_completed(future_map):
            child, screened, survivors, elapsed = future.result()
            base = child[:-1]
            totals = base_totals[base]
            totals["done"] += 1
            totals["screened"] += screened
            totals["survivors"] += survivors
            print(
                f"prefix={format_prefix(child)} screened={screened} "
                f"survivors={survivors} elapsed={elapsed:.3f}s"
            , flush=True)
            if totals["done"] == processor_count:
                print(
                    f"base={format_prefix(base)} done={totals['done']} "
                    f"screened={totals['screened']} survivors={totals['survivors']}"
                , flush=True)

    total_screened = sum(int(item["screened"]) for item in base_totals.values())
    total_survivors = sum(int(item["survivors"]) for item in base_totals.values())
    print(
        f"total bases={len(base_prefixes)} prefixes={len(children)} "
        f"screened={total_screened} survivors={total_survivors} "
        f"elapsed={time.time()-started:.3f}s"
    , flush=True)


if __name__ == "__main__":
    main()
