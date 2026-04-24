"""
Bridge: use GPT's cycle enumerator with our SMT completion.
Parse GPT cycle output and feed into complete_with_smt.
"""

import sys
import time
from p2_good_cycle_search import enumerate_good_cycles, search_good_cycle
from complete_96 import complete_with_smt


def run_n8_search(state_counts, time_limit=120.0, max_cycles=500, smt_timeout=300000):
    """Enumerate cycles with GPT's enumerator, complete with our SMT."""
    print(f"ms={list(state_counts)}, product={eval('*'.join(str(m) for m in state_counts))}")
    print(f"Enumerating cycles (time_limit={time_limit}s, max_cycles={max_cycles})...")

    ms = list(state_counts)
    started = time.time()
    tested = 0
    survivors = 0

    for cycle, movers in enumerate_good_cycles(state_counts, time_limit=time_limit, max_cycles=max_cycles):
        tested += 1
        cycle_list = [list(c) for c in cycle]

        t0 = time.time()
        result = complete_with_smt(ms, cycle_list, timeout_ms=smt_timeout, verbose=False)
        t_smt = time.time() - t0

        if result:
            print(f"\n*** VALID! Cycle #{tested} (len={len(cycle)}) in {t_smt:.1f}s ***")
            print(f"M_8 <= {result['product']} CONFIRMED!")
            print(f"ms={result['ms']}, cycle_length={result['cycle_length']}")

            fname = f"n8_product{result['product']}_result.txt"
            with open(fname, "w") as f:
                f.write(f"ms={result['ms']}\n")
                f.write(f"product={result['product']}\n")
                f.write(f"cycle_length={result['cycle_length']}\n")
                f.write(f"good_cycle={result['cycle']}\n\n")
                for key, val in sorted(result['fs_values'].items()):
                    f.write(f"f[{key[0]}]({key[1]},{key[2]},{key[3]}) = {val}\n")
            print(f"Saved to {fname}")
            return result

        status = "UNSAT" if result is None else "?"
        if tested % 5 == 0 or tested <= 3:
            elapsed = time.time() - started
            print(f"  Cycle {tested}: len={len(cycle)} {status} ({t_smt:.1f}s) [total {elapsed:.0f}s]")

    elapsed = time.time() - started
    print(f"\nNo valid completion in {tested} cycles ({elapsed:.0f}s)")
    return None


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated")
    parser.add_argument("--time-limit", type=float, default=120.0)
    parser.add_argument("--max-cycles", type=int, default=500)
    parser.add_argument("--smt-timeout", type=int, default=300000)
    args = parser.parse_args()

    sc = tuple(int(x) for x in args.state_counts.split(","))
    run_n8_search(sc, args.time_limit, args.max_cycles, args.smt_timeout)
