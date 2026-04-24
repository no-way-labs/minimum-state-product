from __future__ import annotations

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))

from p2_completion_search import has_fatal_forced_cycle_singletons
from p2_good_cycle_search import enumerate_good_cycles, local_context


def forced_rule_map(cycle, movers):
    rule_map = {}
    extended = cycle[1:] + cycle[:1]
    for config, mover, nxt in zip(cycle, movers, extended, strict=True):
        for processor in range(len(config)):
            key = (processor, local_context(config, processor))
            required = nxt[processor] if processor == mover else config[processor]
            existing = rule_map.get(key)
            if existing is not None and existing != required:
                raise ValueError("inconsistent cycle")
            rule_map[key] = required
    return rule_map


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--time-limit", type=float, default=30.0)
    parser.add_argument("--max-cycles", type=int, default=1000)
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    start = time.time()
    total = 0
    survivors = 0

    for cycle, movers in enumerate_good_cycles(state_counts, time_limit=args.time_limit, max_cycles=args.max_cycles):
        total += 1
        cycle_set = frozenset(cycle)
        forced_map = forced_rule_map(cycle, movers)
        if not has_fatal_forced_cycle_singletons(state_counts, cycle_set, forced_map):
            survivors += 1
            print(f"cycle {total}: no fatal forced recurrent component; length={len(cycle)} movers={movers}")
            for config, mover in zip(cycle, movers, strict=True):
                print(f"  {config} --P{mover}-->")
            print(f"  {cycle[0]}")
            break

    print(f"screened={total} survivors={survivors} elapsed={time.time()-start:.3f}s")
    if survivors == 0:
        print("every screened good cycle already forces a recurrent component that cannot be a fair good cycle")


if __name__ == "__main__":
    main()
