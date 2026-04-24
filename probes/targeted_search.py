"""
Targeted search: try to beat 3^n by replacing one 3-state processor
with a 2-state processor while keeping the others at Dijkstra Solution 3.

For n=5, ms=(3,3,3,3,3) gives product 243.
If we can make one processor 2-state: ms has product 2*3^4 = 162.

Strategy: fix n-1 processors to Solution 3 rules, exhaustively search
over the 2-state processor's transition function.
"""

import itertools
import time
from verifier import verify_system


def dijkstra_s3_bottom(L, S, R):
    """Dijkstra Solution 3 bottom machine (P0)."""
    if (S + 1) % 3 == R:
        return (S - 1) % 3
    return S


def dijkstra_s3_top(L, S, R):
    """Dijkstra Solution 3 top machine (P_{n-1})."""
    if L == R and (L + 1) % 3 != S:
        return (L + 1) % 3
    return S


def dijkstra_s3_middle(L, S, R):
    """Dijkstra Solution 3 middle machine."""
    if (S + 1) % 3 == L:
        return L
    if (S + 1) % 3 == R:
        return R
    return S


def enumerate_binary_functions(num_inputs):
    """Generate all binary (2-output) transition functions for given input count."""
    # Each input (L,S,R) tuple maps to 0 or 1
    # Return as dict
    return range(2 ** num_inputs)


def bits_to_func(bits, inputs, m_self=2):
    """Convert integer bit pattern to a transition function dict."""
    d = {}
    for idx, inp in enumerate(inputs):
        d[inp] = (bits >> idx) & 1
    return d


def search_one_binary(n: int, binary_pos: int, verbose: bool = True):
    """
    Search for a valid system where processor binary_pos is 2-state
    and all others use Dijkstra Solution 3 (3-state).

    Returns the valid transition function if found, None otherwise.
    """
    ms = [3] * n
    ms[binary_pos] = 2
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"Searching n={n}, binary_pos={binary_pos}, ms={ms}, product={total}")

    # Build transition functions for non-binary processors
    fs_fixed = {}
    for i in range(n):
        if i == binary_pos:
            continue
        if i == 0:
            fs_fixed[i] = dijkstra_s3_bottom
        elif i == n - 1:
            fs_fixed[i] = dijkstra_s3_top
        else:
            fs_fixed[i] = dijkstra_s3_middle

    # Enumerate inputs for the binary processor
    m_L = ms[(binary_pos - 1) % n]
    m_S = ms[binary_pos]  # = 2
    m_R = ms[(binary_pos + 1) % n]
    inputs = [(l, s, r) for l in range(m_L) for s in range(m_S) for r in range(m_R)]
    num_inputs = len(inputs)
    total_funcs = 2 ** num_inputs

    if verbose:
        print(f"  Binary processor sees {num_inputs} inputs, {total_funcs} candidate functions")

    start = time.time()
    valid_count = 0

    for bits in range(total_funcs):
        func_dict = bits_to_func(bits, inputs)

        def binary_f(L, S, R, d=func_dict):
            return d[(L, S, R)]

        # Build full function list
        fs = []
        for i in range(n):
            if i == binary_pos:
                fs.append(binary_f)
            else:
                fs.append(fs_fixed[i])

        result = verify_system(ms, fs)
        if result['valid']:
            valid_count += 1
            elapsed = time.time() - start
            if verbose:
                print(f"  FOUND valid system! bits={bits:#x}, time={elapsed:.1f}s")
                print(f"  Cycle length: {result['cycle_length']}")
                print(f"  Function table:")
                for inp in inputs:
                    out = func_dict[inp]
                    priv = "PRIV" if out != inp[1] else ""
                    print(f"    f({inp[0]},{inp[1]},{inp[2]}) = {out}  {priv}")
            return {
                'ms': ms,
                'product': total,
                'binary_pos': binary_pos,
                'func_dict': func_dict,
                'verification': result,
            }

        if (bits + 1) % 10000 == 0:
            elapsed = time.time() - start
            rate = (bits + 1) / elapsed
            remaining = (total_funcs - bits - 1) / rate
            if verbose:
                print(f"  {bits+1}/{total_funcs} ({100*(bits+1)/total_funcs:.1f}%), "
                      f"{elapsed:.0f}s elapsed, ~{remaining:.0f}s remaining")

    elapsed = time.time() - start
    if verbose:
        print(f"  No valid system found ({total_funcs} functions checked, {elapsed:.1f}s)")
    return None


def search_one_binary_all_positions(n: int, verbose: bool = True):
    """Try making each processor position binary, one at a time."""
    for pos in range(n):
        result = search_one_binary(n, pos, verbose)
        if result:
            return result
        print()
    return None


def search_two_binary(n: int, pos1: int, pos2: int, verbose: bool = True):
    """
    Search where two processors are 2-state and the rest are Dijkstra S3 (3-state).
    Both binary processors' functions are searched.

    This is only feasible if the combined search space is manageable.
    """
    ms = [3] * n
    ms[pos1] = 2
    ms[pos2] = 2
    total = 1
    for m in ms:
        total *= m

    # Compute search space
    inputs1 = [(l, s, r) for l in range(ms[(pos1-1)%n])
               for s in range(ms[pos1]) for r in range(ms[(pos1+1)%n])]
    inputs2 = [(l, s, r) for l in range(ms[(pos2-1)%n])
               for s in range(ms[pos2]) for r in range(ms[(pos2+1)%n])]

    space1 = 2 ** len(inputs1)
    space2 = 2 ** len(inputs2)
    total_space = space1 * space2

    if verbose:
        print(f"Searching n={n}, binary positions=({pos1},{pos2}), ms={ms}, product={total}")
        print(f"  P{pos1}: {len(inputs1)} inputs, {space1} functions")
        print(f"  P{pos2}: {len(inputs2)} inputs, {space2} functions")
        print(f"  Total search space: {total_space}")

    if total_space > 10**9:
        if verbose:
            print(f"  SKIPPING: search space too large")
        return None

    # Build fixed functions
    fs_fixed = {}
    for i in range(n):
        if i in (pos1, pos2):
            continue
        if i == 0:
            fs_fixed[i] = dijkstra_s3_bottom
        elif i == n - 1:
            fs_fixed[i] = dijkstra_s3_top
        else:
            fs_fixed[i] = dijkstra_s3_middle

    start = time.time()
    checked = 0

    for bits1 in range(space1):
        d1 = bits_to_func(bits1, inputs1)

        def f1(L, S, R, d=d1):
            return d[(L, S, R)]

        for bits2 in range(space2):
            d2 = bits_to_func(bits2, inputs2)

            def f2(L, S, R, d=d2):
                return d[(L, S, R)]

            fs = []
            for i in range(n):
                if i == pos1:
                    fs.append(f1)
                elif i == pos2:
                    fs.append(f2)
                else:
                    fs.append(fs_fixed[i])

            result = verify_system(ms, fs)
            checked += 1

            if result['valid']:
                elapsed = time.time() - start
                if verbose:
                    print(f"  FOUND! bits1={bits1:#x}, bits2={bits2:#x}, time={elapsed:.1f}s")
                    print(f"  Cycle length: {result['cycle_length']}")
                return {
                    'ms': ms,
                    'product': total,
                    'binary_positions': (pos1, pos2),
                    'func_dicts': (d1, d2),
                    'verification': result,
                }

            if checked % 100000 == 0:
                elapsed = time.time() - start
                rate = checked / elapsed
                remaining = (total_space - checked) / rate
                if verbose:
                    print(f"  {checked}/{total_space} ({100*checked/total_space:.1f}%), "
                          f"{elapsed:.0f}s, ~{remaining:.0f}s left")

    elapsed = time.time() - start
    if verbose:
        print(f"  Not found ({checked} checked, {elapsed:.1f}s)")
    return None


if __name__ == "__main__":
    n = 5

    print("=" * 60)
    print(f"TARGETED SEARCH: Can we beat 3^{n} = {3**n} for n={n}?")
    print(f"Strategy: Replace one 3-state processor with 2-state")
    print(f"Product would be 2 * 3^{n-1} = {2 * 3**(n-1)}")
    print("=" * 60)
    print()

    result = search_one_binary_all_positions(n, verbose=True)

    if result:
        print(f"\n*** SUCCESS: product = {result['product']} < {3**n} ***")
    else:
        print(f"\nCannot beat {3**n} by replacing a single processor.")
        print("Solution 3 rules for n-1 processors are too rigid.")
        print()
        print("This doesn't prove M_5 = 3^5 — the other processors'")
        print("rules might also need to change.")
