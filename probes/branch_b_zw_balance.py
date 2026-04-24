"""
Branch B sub-claim B3: ZW balance check.

Scenario (b-start form):
- Walker's 3-G-traversal section: b -> c -> b -> c
- Inside: s1 (b), s1+M (c, first), s1+2M (b, second), s1+3M (c, second)
- M = I + 1, where I = number of interior mids of G (all ternary)
- Inside moves: 2M cw (traversals 1, 3) + M ccw (traversal 2) = 3M total
- Inside fires: 2 b + 2 c + 3I mid = 3M + 1 (one per inside index)

Outside region R_out = ring \ closure(G).
- Outside moves: L - 3M total
- For each p in R_out, fc_outside[p] = m_p (since p doesn't appear inside)

ZW: total cw = total ccw
- Inside cw = 2M, inside ccw = M
- Outside cw = c_out, outside ccw = d_out (plus 2 boundary moves both cw)
- Total cw = 2M + 2 + c_out
- Total ccw = M + d_out
- ZW => d_out - c_out = M + 2 = I + 3

Walker's outside trajectory starts at position I+2 (right c) just after s1+3M
and ends at position n-1 (e = left b) just before s1.

Net cw displacement from I+2 to n-1 via outside: walker must cover exactly
(n-1) - (I+2) = n - I - 3 positions cw (if no wrap), OR that + k*n for k-wrap.

Under local trajectory (k = 0): c_out - d_out = n - I - 3.
Combined with ZW: (M+2) = -(n - I - 3) => I + 3 + n - I - 3 = 0 => n = 0. FALSE.

Under k = -1 wrap: c_out - d_out = n - I - 3 - n = -I - 3.
Combined with ZW: d_out - c_out = I + 3. Consistent!

Under k = +1 wrap: c_out - d_out = n - I - 3 + n = 2n - I - 3.
Combined with ZW: d_out - c_out = I + 3 - 2n. Needs 2n = 0. FALSE.

So only k = -1 is consistent. This means walker's outside trajectory must
make 1 net ccw wrap around the ring.

But walker at step s1 + 3M + 1 = I + 2 (right c), and walker's first outside
move options: cw (I+3), ccw (I+1 = c, forbidden), stay (forbidden). So walker
must start by going cw.

For the net displacement to be k=-1 ccw wrap, walker must do: some cw moves,
reverse (at some binary), net ccw to overall wrap.

Verify feasibility numerically: find (n, I, #binaries in R_out, moduli)
such that:
  - Walker's outside can have net = -(I+3) moves cw (= I+3 ccw)
  - Each R_out position visited its m_p times
  - Consistent with sub-threshold
"""

def feasibility_check(n, I, r_out_moduli):
    """
    n: ring size
    I: interior mids of G (all ternary)
    r_out_moduli: list of moduli for positions in R_out (|R_out| = n - I - 2)
    """
    assert len(r_out_moduli) == n - I - 2
    assert all(m >= 2 for m in r_out_moduli)
    
    # Total cycle length
    # G contribution: b (m=2) + c (m=2) + I ternary mids (m=3 each) = 4 + 3I
    L = (4 + 3 * I) + sum(r_out_moduli)
    M = I + 1
    
    # Outside moves count (internal, not boundary)
    internal_outside_moves = L - 3*M - 2
    
    # Need d_out - c_out = I + 3 (from ZW)
    # And c_out + d_out = internal_outside_moves
    # => c_out = (internal_outside_moves - (I+3)) / 2
    # => d_out = (internal_outside_moves + (I+3)) / 2
    
    gap_sum = internal_outside_moves - (I + 3)
    if gap_sum < 0 or gap_sum % 2 != 0:
        return None, f"c_out negative or non-integer: {gap_sum/2}"
    
    c_out = gap_sum // 2
    d_out = (internal_outside_moves + I + 3) // 2
    
    # Walker's fires in outside must match m_p for each R_out position
    outside_fires = sum(r_out_moduli)
    # Outside indices = L - 3M - 1 (fires per outside index)
    outside_indices = L - 3*M - 1
    
    # For walker's outside trajectory to have the required c_out cw and d_out ccw
    # moves while visiting each R_out position fc[p] = m_p times and being
    # a sequence of monotone B2B traversals of outer gaps, we need:
    # - Total moves = c_out + d_out + 2 boundary = L - 3M ✓ (by construction)
    # - Walker visits each R_out position exactly m_p times ✓ (by construction)
    
    # But wait: walker's fires per INDEX in outside includes one fire. Outside
    # indices = L - 3M - 1. Outside fires = sum m_p for p in R_out = outside_fires.
    # These should equal: outside_indices should equal outside_fires.
    
    if outside_indices != outside_fires:
        return None, f"Fire count mismatch: outside_indices={outside_indices} != outside_fires={outside_fires}"
    
    # Also check sub-threshold: product < 4 * 3^(n-2) for n >= 9
    # (In general, threshold depends on n)
    product = 1
    # G contributes 2 (b) + 2 (c) + 3^I (ternary mids)
    product *= 2 * 2 * (3 ** I)
    for m in r_out_moduli:
        product *= m
    
    if n >= 9:
        threshold = 4 * (3 ** (n - 2))
        if product >= threshold:
            return None, f"product {product} >= threshold {threshold}"
    
    return {
        "L": L,
        "M": M,
        "c_out": c_out,
        "d_out": d_out,
        "product": product,
        "threshold": 4 * (3 ** (n-2)) if n >= 9 else None,
    }, None


def find_configurations(n, max_I):
    """Search for feasible configurations."""
    from itertools import product as iproduct
    
    results = []
    for I in range(0, max_I + 1):
        if n - I - 2 < 1:
            continue
        r_out_size = n - I - 2
        # Try all combinations of moduli in {2, 3, 4}
        for moduli in iproduct([2, 3], repeat=r_out_size):
            # At least 1 binary in R_out to make hasGe3Binary (b, c, + at least 1)
            if moduli.count(2) < 1:
                continue
            result, err = feasibility_check(n, I, list(moduli))
            if result is not None:
                results.append((I, list(moduli), result))
    
    return results


if __name__ == "__main__":
    print("Searching for feasible Branch B stretched-self-return configurations at n=9:\n")
    configs = find_configurations(9, max_I=7)
    if not configs:
        print("NONE found -- stretched self-return scenario is impossible at n=9 under all constraints.")
    else:
        print(f"Found {len(configs)} feasible configurations:")
        for I, moduli, result in configs[:20]:
            print(f"  I={I}, R_out moduli={moduli}")
            print(f"    L={result['L']}, c_out={result['c_out']}, d_out={result['d_out']}, product={result['product']}")
    
    print("\nAt n=11:\n")
    configs = find_configurations(11, max_I=9)
    if not configs:
        print("NONE found at n=11")
    else:
        print(f"Found {len(configs)} at n=11. First few:")
        for I, moduli, result in configs[:10]:
            print(f"  I={I}, R_out moduli={moduli}, L={result['L']}")
