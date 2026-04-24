from __future__ import annotations

import argparse
import os
import sys
import time

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from scripts.p2_completion_search import all_keys, has_fatal_forced_cycle, iter_configs, search_completion
from scripts.p2_good_cycle_search import enumerate_good_cycles, local_context


def forced_domains(state_counts, cycle, movers):
    domains = {key: frozenset(range(state_counts[key[0]])) for key in all_keys(state_counts)}
    extended = cycle[1:] + cycle[:1]
    for config, mover, nxt in zip(cycle, movers, extended, strict=True):
        for processor in range(len(state_counts)):
            key = (processor, local_context(config, processor))
            required = nxt[processor] if processor == mover else config[processor]
            domains[key] = frozenset({required})
    return domains


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--screen-time-limit", type=float, default=30.0)
    parser.add_argument("--completion-time-limit", type=float, default=30.0)
    parser.add_argument("--max-cycles", type=int, default=10000)
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    configs = iter_configs(state_counts)
    started = time.time()
    screened = 0

    for cycle, movers in enumerate_good_cycles(state_counts, time_limit=args.screen_time_limit, max_cycles=args.max_cycles):
        screened += 1
        cycle_set = frozenset(cycle)
        domains = forced_domains(state_counts, cycle, movers)
        if has_fatal_forced_cycle(state_counts, cycle_set, configs, domains):
            continue

        print(f"trying survivor cycle {screened} length={len(cycle)}")
        result = search_completion(state_counts, time_limit=args.completion_time_limit, cycle=cycle, movers=movers)
        print(result.message)
        print(
            f"screened={screened} elapsed={time.time()-started:.3f}s "
            f"completion_nodes={result.stats.nodes} completion_backtracks={result.stats.backtracks}"
        )
        if result.system is not None:
            print("found valid system")
            return

    print(f"no valid completion found among {screened} screened cycles in {time.time()-started:.3f}s")


if __name__ == "__main__":
    main()
