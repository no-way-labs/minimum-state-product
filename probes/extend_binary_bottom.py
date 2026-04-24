"""
Test whether the binary-bottom construction (replace P0 with 2-state)
extends to n=6,7,8,...

For each n, exhaustively search over 2^(m_L * 2 * m_R) = 2^18 functions
for the binary bottom processor, with all other processors using Dijkstra S3.
"""

import time
from verifier import verify_system
from targeted_search import dijkstra_s3_bottom, dijkstra_s3_top, dijkstra_s3_middle


def search_binary_bottom(n: int, verbose: bool = True):
    """Search for binary bottom processor compatible with S3 rest."""
    ms = [3] * n
    ms[0] = 2
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"n={n}, ms={ms}, product={total} (vs 3^{n}={3**n})")

    # P0's inputs: L from P_{n-1} (3-state), S from P0 (2-state), R from P1 (3-state)
    inputs = [(l, s, r) for l in range(3) for s in range(2) for r in range(3)]
    num_inputs = len(inputs)  # always 18
    total_funcs = 2 ** num_inputs

    # Build S3 functions for other processors
    fs_fixed = {}
    for i in range(1, n):
        if i == n - 1:
            fs_fixed[i] = dijkstra_s3_top
        else:
            fs_fixed[i] = dijkstra_s3_middle

    start = time.time()
    found = []

    for bits in range(total_funcs):
        d = {}
        for idx, inp in enumerate(inputs):
            d[inp] = (bits >> idx) & 1

        def f0(L, S, R, d=d):
            return d[(L, S, R)]

        fs = [f0] + [fs_fixed[i] for i in range(1, n)]
        result = verify_system(ms, fs)

        if result['valid']:
            elapsed = time.time() - start
            found.append((bits, result['cycle_length']))
            if verbose:
                print(f"  FOUND! bits={bits:#x}, cycle_len={result['cycle_length']}, {elapsed:.1f}s")

        if (bits + 1) % 50000 == 0:
            elapsed = time.time() - start
            rate = (bits + 1) / elapsed
            remaining = (total_funcs - bits - 1) / rate
            if verbose:
                print(f"  {bits+1}/{total_funcs} ({100*(bits+1)/total_funcs:.1f}%), "
                      f"{elapsed:.0f}s, ~{remaining:.0f}s remaining, {len(found)} found so far")

    elapsed = time.time() - start
    if verbose:
        print(f"\n  Total: {len(found)} valid functions out of {total_funcs} ({elapsed:.1f}s)")
        if found:
            cycle_lengths = sorted(set(cl for _, cl in found))
            print(f"  Cycle lengths found: {cycle_lengths}")

    return found


def search_binary_top(n: int, verbose: bool = True):
    """Search for binary top processor compatible with S3 rest."""
    ms = [3] * n
    ms[n-1] = 2
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"n={n}, ms={ms}, product={total} (binary top)")

    # P_{n-1}'s inputs: L from P_{n-2} (3-state), S (2-state), R from P0 (3-state)
    inputs = [(l, s, r) for l in range(3) for s in range(2) for r in range(3)]
    total_funcs = 2 ** len(inputs)

    fs_fixed = {}
    for i in range(n - 1):
        if i == 0:
            fs_fixed[i] = dijkstra_s3_bottom
        else:
            fs_fixed[i] = dijkstra_s3_middle

    start = time.time()
    found = []

    for bits in range(total_funcs):
        d = {}
        for idx, inp in enumerate(inputs):
            d[inp] = (bits >> idx) & 1

        def ftop(L, S, R, d=d):
            return d[(L, S, R)]

        fs = [fs_fixed[i] for i in range(n - 1)] + [ftop]
        result = verify_system(ms, fs)

        if result['valid']:
            elapsed = time.time() - start
            found.append((bits, result['cycle_length']))
            if verbose:
                print(f"  FOUND! bits={bits:#x}, cycle_len={result['cycle_length']}, {elapsed:.1f}s")

        if (bits + 1) % 50000 == 0:
            elapsed = time.time() - start
            if verbose:
                print(f"  {bits+1}/{total_funcs} ({100*(bits+1)/total_funcs:.1f}%), "
                      f"{elapsed:.0f}s, {len(found)} found")

    elapsed = time.time() - start
    if verbose:
        print(f"  Total: {len(found)} valid functions ({elapsed:.1f}s)")
    return found


if __name__ == "__main__":
    print("=" * 60)
    print("EXTENDING BINARY-BOTTOM CONSTRUCTION TO LARGER n")
    print("=" * 60)
    print()

    for n in range(5, 9):
        print(f"\n{'='*40}")
        print(f"n={n}: Binary bottom, S3 rest")
        print(f"{'='*40}")
        found = search_binary_bottom(n)

        if not found:
            print(f"\n  Binary bottom FAILS for n={n}")
            print(f"  Trying binary top instead...")
            found_top = search_binary_top(n)
            if found_top:
                print(f"  Binary TOP works for n={n}!")
            else:
                print(f"  Binary top also fails for n={n}")
        print()
