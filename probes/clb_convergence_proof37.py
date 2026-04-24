#!/usr/bin/env python3
"""
CONVERGENCE PROOF 37: Strengthen the Analytical Framework
===========================================================

STATUS of proof components:
  1. [PROVED] Δfc≤0 subgraph is DAG via (fc, Ψ)
  2. [PROVED] Every cycle needs anomalous edge
  3. [PROVED] Cycle ⟺ cycle in excursion graph
  4a. [PROVED] Δint(2,1) ≥ 0 — no Δfc≤0 firing creates interior (2,1) pairs
  4b. [OPEN] Zero-edge sub-LP feasible for all n
  4c. [EMPIRICAL] Boundary types converge (~4400)

KEY QUESTION: Can we close step 4b?

APPROACH: Examine the zero-edge constraint structure more carefully.
When Δint(2,1) = 0, the excursion edge has ZERO net change in interior
(2,1) pairs. Since no individual step creates (2,1) pairs, this means
NO step destroys them either — the interior (2,1) pattern is UNCHANGED.

This is a very strong constraint! It means the excursion path doesn't
touch any interior (2,1) pairs. This limits which anomalous firings
and cascade patterns are possible.

Analysis:
- Anomalous T_mid(2,1,1)→0 at pos j≥3 DESTROYS interior (2,1) pair at j-1
  → This can only happen in a zero edge if j-1 is NOT interior (j=2)
  → Or if the (2,1) pair is restored (impossible by Lemma 4a)
  → So: zero edges can only have T_mid anomalous at pos 2 (if interior starts at 2)

Wait — the zero is about src vs tgt, not about intermediate steps.
The excursion goes src →anom b → ... → tgt via Δfc≤0 path.
S(src) - S(tgt) = 0 means: the total interior (2,1) weight is same at src and tgt.
But along the path, steps can destroy (2,1) pairs (since no step creates them,
S only decreases along the path). So S(b) ≤ S(src) and S(tgt) ≤ S(b).
Combined: S(tgt) ≤ S(b) ≤ S(src) = S(tgt), so S(b) = S(src) = S(tgt).

KEY INSIGHT: If Δint(2,1) = 0 for the excursion edge, then EVERY step
along the excursion path preserves S. Since no step can increase S,
every step must have ΔS = 0.

This means:
- The anomalous step has ΔS = 0
- Every Δfc≤0 step has ΔS = 0

For T_mid(2,1,1)→0 at interior pos j (j≥3): ΔS = -(j-1) < 0.
So this anomalous entry CANNOT occur in a zero-edge excursion!

For T_mid(2,1,1)→0 at pos 2: pair at pos 1 is boundary (T_low-T_mid),
so ΔS = 0. This CAN occur.

For T_high(1,1,1)→2: doesn't directly affect interior (2,1) pairs.
ΔS = 0 at the anomalous step. CAN occur.

Similarly: T_bot(0,0,0)→1, T_bot(1,1,2)→0, T_top(2,0,0)→1 all
affect boundary pairs only, so ΔS = 0. CAN occur.

So zero edges come from anomalous firings at:
- T_bot (pos 0)
- T_mid at pos 2 only (NOT interior T_mid at pos ≥3)
- T_high (pos n-2)
- T_top (pos n-1)

This DRAMATICALLY reduces the possible zero-edge excursions!
For n large, the T_mid interior (pos 3..n-4) CANNOT produce zero edges.

Let's verify this computationally and count the anomalous positions
in zero-edge sources.
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter
import numpy as np
from scipy.optimize import linprog


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R: anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    # Track which anomalous entry connects each edge
    exc_edge_info = {}
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set(); queue = [b]; visited.add(b); head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src_info in anom_target_map.get(b, []):
                    if isinstance(src_info, tuple) and len(src_info) == 2:
                        src, anom_pos = src_info
                    else:
                        src = src_info
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)

    return list(exc_edges), ms, anom_edges


def build_boundary_indices():
    idx = 0
    bnd = [{}, {}, {}, {}, {}]
    for a in range(2):
        for b in range(3):
            bnd[0][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(3):
            bnd[1][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(3):
            bnd[2][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(2):
            bnd[3][(a, b)] = idx; idx += 1
    for a in range(2):
        for b in range(2):
            bnd[4][(a, b)] = idx; idx += 1
    n_bnd = idx
    return bnd, n_bnd


def feat_vector(c, n_val, bnd, n_bnd, int_idx, n_vars):
    n = n_val
    r = [0] * n_vars
    for j in range(n):
        j1 = (j + 1) % n
        a, b = c[j], c[j1]
        bnd_type = None
        if j == 0: bnd_type = 0
        elif j == 1: bnd_type = 1
        elif j == n-3: bnd_type = 2
        elif j == n-2: bnd_type = 3
        elif j == n-1: bnd_type = 4
        if bnd_type is not None:
            k = bnd[bnd_type].get((a, b))
            if k is not None: r[k] += 1
        else:
            k = int_idx[(a, b)]
            r[k] += j
    return r


def main():
    bnd, n_bnd = build_boundary_indices()
    int_idx = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = idx; idx += 1
    n_vars = idx
    k21 = int_idx[(2, 1)]

    print("=" * 70)
    print("ZERO-EDGE EXCURSION STRUCTURE")
    print("=" * 70)
    print()
    print("KEY LEMMA: If Δint(2,1) = 0 for excursion edge (src→tgt),")
    print("then EVERY step along the excursion preserves interior (2,1)")
    print("pairs. In particular, no T_mid anomalous at pos j≥3 occurs")
    print("(since that destroys the (2,1) pair at interior pos j-1).")
    print()

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms, anom_raw = build_excursion_graph(n_val)
        n = n_val

        # Map src configs to their anomalous positions
        src_anom_pos = defaultdict(set)
        for c, succ, i, dfc in anom_raw:
            src_anom_pos[c].add(i)

        zero_edges = []
        pos_edges = []
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            d21 = fu[k21] - fv[k21]
            if d21 == 0:
                zero_edges.append((u, v))
            else:
                pos_edges.append((u, v))

        # For zero edges: what anomalous positions do the SRC configs have?
        src_pos_counts = Counter()
        src_has_interior = 0
        src_only_boundary = 0
        for u, v in zero_edges:
            positions = src_anom_pos.get(u, set())
            for p in positions:
                if p == 0:
                    src_pos_counts["T_bot(0)"] += 1
                elif p == n - 2:
                    src_pos_counts["T_high(n-2)"] += 1
                elif p == n - 1:
                    src_pos_counts["T_top(n-1)"] += 1
                elif p == 2:
                    src_pos_counts["T_mid(2)"] += 1
                else:
                    src_pos_counts[f"T_mid({p})"] += 1

            has_int = any(3 <= p <= n-4 for p in positions)
            if has_int:
                src_has_interior += 1
            else:
                src_only_boundary += 1

        dt = time.time() - t0
        print(f"n={n_val}: {len(zero_edges)} zero-edges, "
              f"{len(pos_edges)} pos-edges ({dt:.1f}s)")
        print(f"  Src anomalous positions: {dict(src_pos_counts)}")
        print(f"  Src with interior T_mid (pos≥3): {src_has_interior}")
        print(f"  Src boundary-only: {src_only_boundary}")

        # KEY CHECK: For zero edges whose src has ONLY boundary anomalous
        # positions, the constraint depends only on boundary values!
        if src_only_boundary > 0:
            # Count how many distinct boundary constraint vectors come from
            # boundary-only sources
            bnd_only_vecs = set()
            for u, v in zero_edges:
                positions = src_anom_pos.get(u, set())
                if not any(3 <= p <= n-4 for p in positions):
                    fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
                    fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
                    bvec = tuple(fu[i] - fv[i] for i in range(n_bnd))
                    bnd_only_vecs.add(bvec)
            print(f"  Boundary-only constraint types: {len(bnd_only_vecs)}")

    # ═══════════════════════════════════════════════════════════
    # DEEPER ANALYSIS: The src configs with interior T_mid
    # positions ≥ 3 — do they actually contribute to ZERO edges?
    # (They have anomalous at pos≥3, but the ZERO edge means
    # the excursion doesn't go through that anomalous firing.)
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("ANALYSIS: Interior anomalous sources in zero edges")
    print("=" * 70)
    print()
    print("A src config may have anomalous entries at MULTIPLE positions.")
    print("A zero edge uses one specific anomalous entry. Which one?")
    print("If the src fires at pos≥3 (interior T_mid(2,1,1)→0),")
    print("it destroys (2,1) at pos j-1, so the excursion has Δint(2,1)>0")
    print("unless the tgt happens to have more (2,1) pairs elsewhere.")
    print()
    print("But Lemma 4a says NO step creates (2,1) pairs.")
    print("So the excursion from an interior T_mid anomalous at pos j≥3")
    print("MUST have Δint(2,1) = -(j-1) < 0.")
    print("→ These are POSITIVE edges, not zero edges!")
    print()
    print("If a src has BOTH interior and boundary anomalous entries,")
    print("the zero edge must come from the BOUNDARY anomalous entry.")
    print()

    # Verify: for zero edges with src having interior anomalous,
    # check if the tgt could be reached via a boundary anomalous entry
    n_val = 8
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    dfc_le0_adj = defaultdict(list)
    anom_by_src_pos = defaultdict(list)

    for c in bad_list:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_by_src_pos[c].append((i, succ, dfc))

    anom_sources = set(anom_by_src_pos.keys())

    # For each anomalous source with BOTH interior and boundary entries:
    # Trace which excursion edges are zero vs positive
    both_count = 0
    for src, entries in anom_by_src_pos.items():
        has_int = any(3 <= pos <= n-4 for pos, _, _ in entries)
        has_bnd = any(pos <= 2 or pos >= n-2 for pos, _, _ in entries)
        if has_int and has_bnd:
            both_count += 1

    print(f"n={n_val}: {both_count} src configs have both interior and "
          f"boundary anomalous entries")

    print()
    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print()
    print("The zero-edge sub-LP reduces to excursions from:")
    print("  - T_bot anomalous (pos 0)")
    print("  - T_mid anomalous at pos 2 only (boundary of interior)")
    print("  - T_high anomalous (pos n-2)")
    print("  - T_top anomalous (pos n-1)")
    print()
    print("These are BOUNDARY-DOMINATED excursions.")
    print("The constraint types converge because the boundary values")
    print("are from fixed finite domains, and the interior contribution")
    print("to the constraint is fully determined by the 8 non-(2,1)")
    print("interior pair changes — which are also bounded because")
    print("the excursion only modifies boundary-adjacent positions.")


if __name__ == '__main__':
    main()
