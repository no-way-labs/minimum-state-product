#!/usr/bin/env python3
"""Exploration 4b: Constructive large-L cycle via Gray code.

At ms=(2,...,2), the game graph is Q_n. Since m_p=2, every fire at p
outputs 1-c[p] (the only other value). So the det is trivially consistent:
det(p, a, b, d) = 1-b for every move entry.

A Gray code gives a Hamiltonian cycle on Q_n (length 2^n). We can extract
subcycles of any even length by short-circuiting.

This probe:
1. Constructs Gray code Hamiltonian cycle on {0,1}^n
2. Extracts subcycles of various lengths
3. Verifies they are fair (each processor fires ≥ 1)
4. Computes |SK| for each
5. Finds the exact L boundary where |SK| < 2^(n-1)
"""
from itertools import product as iproduct
from collections import defaultdict, Counter


def gray_code(n):
    """Generate reflected Gray code for n bits."""
    if n == 0:
        return [()]
    if n == 1:
        return [(0,), (1,)]
    prev = gray_code(n - 1)
    return [(0,) + p for p in prev] + [(1,) + p for p in reversed(prev)]


def extract_subcycle(full_cycle, length, start=0):
    """Extract a subcycle of given length from a Hamiltonian cycle.

    Strategy: take `length` consecutive configs from the full cycle,
    then close the cycle by a direct edge (possible since Q_n is
    vertex-transitive and any two adjacent configs differ by 1 bit).

    Actually, for an even-length subcycle: take consecutive configs
    from the Hamiltonian cycle. The first and last must be connected
    (differ by 1 bit). This works if we pick the right segment.
    """
    N = len(full_cycle)
    # Try all starting positions
    for s in range(N):
        path = [full_cycle[(s + i) % N] for i in range(length)]
        # Check if path[-1] and path[0] differ by exactly 1 bit
        diff = sum(1 for a, b in zip(path[-1], path[0]) if a != b)
        if diff == 1:
            return path
    return None


def build_det(cycle, n):
    """Build the det from a cycle at ms=(2,...,2).

    At ms=(2,...,2), every fire at p outputs 1-c[p].
    """
    det = {}
    movers = []
    for t in range(len(cycle)):
        c_curr = cycle[t]
        c_next = cycle[(t + 1) % len(cycle)]
        # Find the position that changed
        diffs = [i for i in range(n) if c_curr[i] != c_next[i]]
        assert len(diffs) == 1, f"Step {t}: configs differ at {len(diffs)} positions"
        p = diffs[0]
        movers.append(p)
        # Move entry
        key = (p, c_curr[(p - 1) % n], c_curr[p], c_curr[(p + 1) % n])
        val = c_next[p]
        if key in det:
            assert det[key] == val, f"Det conflict at step {t}"
        det[key] = val
        # Non-mover entries
        for q in range(n):
            if q == p:
                continue
            kq = (q, c_curr[(q - 1) % n], c_curr[q], c_curr[(q + 1) % n])
            if kq in det:
                assert det[kq] == c_curr[q], f"Non-mover conflict at step {t}, pos {q}"
            det[kq] = c_curr[q]
    return det, movers


def compute_sk(n, cycle, det):
    """Compute |SK| for ms=(2,...,2)."""
    cycle_set = set(cycle)
    all_configs = set(iproduct(*([range(2)] * n)))
    ng = all_configs - cycle_set

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    out_edges = defaultdict(list)
    for c in ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in ng:
                    out_edges[c].append(nc)

    remaining = set(ng)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in out_edges.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks

    return len(remaining)


def main():
    for n in [5, 6]:
        print(f"\n{'='*72}")
        print(f"n={n}: Constructing Gray code subcycles")
        print(f"{'='*72}")

        gc = gray_code(n)
        N = len(gc)
        print(f"  Gray code length: {N} (= 2^{n})")
        print(f"  2^(n-1) = {2**(n-1)}")

        # Verify it's a valid cycle
        for t in range(N):
            c1, c2 = gc[t], gc[(t + 1) % N]
            diff = sum(1 for a, b in zip(c1, c2) if a != b)
            assert diff == 1, f"Gray code not valid at step {t}"

        target = 2 ** (n - 1)

        print(f"\n  L   |NG|  fair?  |SK|  2^(n-1)  slack  violation?")
        for L in range(2 * n, N + 1, 2):
            cycle = extract_subcycle(gc, L)
            if cycle is None:
                # Try other starting positions more carefully
                found = False
                for shift in range(N):
                    for offset in range(N):
                        path = [gc[(offset + i) % N] for i in range(L)]
                        diff = sum(1 for a, b in zip(path[-1], path[0]) if a != b)
                        if diff == 1:
                            cycle = path
                            found = True
                            break
                    if found:
                        break
                if not found:
                    print(f"  {L:3d}  ---  no valid subcycle found")
                    continue

            # Check fairness
            movers_count = Counter()
            for t in range(L):
                c1, c2 = cycle[t], cycle[(t + 1) % L]
                for p in range(n):
                    if c1[p] != c2[p]:
                        movers_count[p] += 1
            fair = all(movers_count[p] >= 1 for p in range(n))

            if not fair:
                print(f"  {L:3d}  {N-L:4d}  NO    ---  (skipping unfair cycle)")
                continue

            # Build det and compute SK
            try:
                det, movers = build_det(cycle, n)
                sk = compute_sk(n, cycle, det)
                ng_size = N - L
                slack = sk - target
                flag = " VIOLATION!" if sk < target else ""
                print(f"  {L:3d}  {ng_size:4d}  YES   {sk:4d}  {target:6d}  "
                      f"{slack:+5d}{flag}")
            except AssertionError as e:
                print(f"  {L:3d}  ---  det conflict: {e}")


if __name__ == "__main__":
    main()
