from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import product

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

SCREENED_RE = re.compile(r"screened=(\d+)\s+survivors=(\d+)\s+elapsed=([0-9.]+)s")


def screen_prefix_subprocess(
    state_counts: tuple[int, ...],
    mover_prefix: tuple[int, ...],
    time_limit: float,
    max_cycles: int,
) -> tuple[tuple[int, ...], int, int, float, str]:
    args = [
        sys.executable,
        "probes/gpt/p2_cycle_screen.py",
        ",".join(str(part) for part in state_counts),
        "--time-limit",
        str(time_limit),
        "--max-cycles",
        str(max_cycles),
        "--mover-prefix",
        ",".join(str(part) for part in mover_prefix),
    ]
    completed = subprocess.run(args, capture_output=True, text=True, check=False)
    output = completed.stdout + completed.stderr
    matches = SCREENED_RE.findall(output)
    if not matches:
        raise RuntimeError(f"could not parse screen output for prefix {mover_prefix}:\n{output}")
    screened, survivors, elapsed = matches[-1]
    return mover_prefix, int(screened), int(survivors), float(elapsed), output


def all_prefixes(processor_count: int, prefix_length: int) -> list[tuple[int, ...]]:
    return [tuple(prefix) for prefix in product(range(processor_count), repeat=prefix_length)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--prefix-length", type=int, default=1)
    parser.add_argument("--base-prefix", help="comma-separated fixed mover prefix to extend")
    parser.add_argument("--time-limit", type=float, default=300.0)
    parser.add_argument("--max-cycles", type=int, default=50_000_000)
    parser.add_argument("--max-workers", type=int, default=None)
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    base_prefix: tuple[int, ...] = ()
    if args.base_prefix:
        base_prefix = tuple(int(part) for part in args.base_prefix.split(","))
    prefixes = [base_prefix + suffix for suffix in all_prefixes(len(state_counts), args.prefix_length)]
    began = time.time()
    total_screened = 0
    total_survivors = 0

    print(
        f"screening {len(prefixes)} mover prefixes of length {len(base_prefix) + args.prefix_length} "
        f"for {state_counts} with time_limit={args.time_limit}s"
    )
    max_workers = args.max_workers or len(prefixes)
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_map = {
            executor.submit(screen_prefix_subprocess, state_counts, prefix, args.time_limit, args.max_cycles): prefix
            for prefix in prefixes
        }
        for future in as_completed(future_map):
            prefix, screened, survivors, elapsed, _ = future.result()
            total_screened += screened
            total_survivors += survivors
            print(
                f"prefix={','.join(str(part) for part in prefix)} "
                f"screened={screened} survivors={survivors} elapsed={elapsed:.3f}s"
            )

    print(
        f"total prefixes={len(prefixes)} screened={total_screened} "
        f"survivors={total_survivors} elapsed={time.time()-began:.3f}s"
    )


if __name__ == "__main__":
    main()
