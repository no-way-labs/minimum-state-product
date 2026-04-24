#!/usr/bin/env python3
"""SKMH Explorations 4-6 combined probe.

E4 (f): cell-count-sensitive invariants
  Tabulate full f-vector c_0,...,c_d of NG(C) and check whether any
  cell-count-based quantity (χ, normalized f-vector, Hilbert polynomial
  evaluated at -1 / 1 / 2, Σ(-1)^k c_k/M, etc.) discriminates
  sub/at/super-threshold.

E5 (g): Herlihy content under processor-color labeling
  For each vertex c, assign a color χ(c) in [n] (several candidates).
  Count "monochromatic top cells" and "properly-colored max-simplices"
  by orientation. See whether content discriminates.

E6 (i): Z/n-equivariant Euler characteristic on symmetric ms
  For ms with full Z/n symmetry (all m_i equal), count Z/n-fixed points
  and equivariant Euler. Compare discriminating power.

All three on the same cycles / same cell enumeration — share code.
"""
from __future__ import annotations
import importlib.util
import itertools
import os
import sys
import time
from collections import defaultdict
import numpy as np
import math

def _factorial(n):
    return math.factorial(n)

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_CLAUDE = os.path.normpath(os.path.join(_HERE, "..", "..", "..", "claude"))

spec = importlib.util.spec_from_file_location(
    "probe_a",
    os.path.join(_CLAUDE,
                 "probe_sk_hamming1_empty_discriminator_2026-04-17.py"))
probe_a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe_a)
enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart


def M_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def _partitions(total, n, caps):
    if n == 0:
        if total == 0:
            yield ()
        return
    for d0 in range(min(caps[0], total) + 1):
        for tail in _partitions(total - d0, n - 1, caps[1:]):
            yield (d0,) + tail


def enumerate_cells_up_to(ms, max_dim):
    n = len(ms)
    for total_dim in range(max_dim + 1):
        caps = [m - 1 for m in ms]
        for dvec in _partitions(total_dim, n, caps):
            face_sets = [
                list(itertools.combinations(range(ms[i]), dvec[i] + 1))
                for i in range(n)
            ]
            for combo in itertools.product(*face_sets):
                yield total_dim, combo


def cell_vertices(cell):
    return list(itertools.product(*cell))


def cell_in_ng(cell, cycle_set):
    for v in itertools.product(*cell):
        if v in cycle_set:
            return False
    return True


# ===== E4: cell-count invariants =====

def f_vector_ng(ms, cycle, max_dim=None):
    ambient = sum(m - 1 for m in ms)
    if max_dim is None:
        max_dim = ambient
    cycle_set = set(tuple(c) for c in cycle)
    counts = [0] * (max_dim + 1)
    for dim, cell in enumerate_cells_up_to(ms, max_dim):
        if cell_in_ng(cell, cycle_set):
            counts[dim] += 1
    return counts, ambient


# ===== E5: Herlihy content =====

def coloring_parity_mod_n(config, n, ms):
    return sum(config) % n


def coloring_argmax(config, n, ms):
    # argmax ties broken by lowest index
    best = 0
    best_val = -1
    for i, v in enumerate(config):
        rel = v / max(ms[i] - 1, 1)  # normalize to [0,1]
        if rel > best_val:
            best_val = rel
            best = i
    return best


def coloring_weighted_sum(config, n, ms):
    # Σ i * c[i] mod n — position-weighted
    return sum(i * v for i, v in enumerate(config)) % n


def count_properly_colored_top(ms, cycle, coloring_fn):
    """Count properly-colored n-simplices (top-dim cells) in NG.

    A "top-dim" cell here: choose S ⊂ [n] with |S| = n (all positions).
    At each position, choose |F_i| = 2 (edge). So the cell is an
    n-dim cube shape with 2^n vertices. Not quite n-simplex.

    Alternative: choose |F_i| = 1 at n-|S| positions, |F_j| = m_j at
    one position forming an (m_j-1)-simplex. Not uniform n-simplex.

    For Herlihy-content style, we want n-simplices specifically.
    Use the diagonal embedding: a simplex formed by (v_0, v_0+e_1,
    v_0+e_1+e_2, ..., v_0+e_1+...+e_n) using unit bumps at each
    position in order. Iterate over starting config and unit bump
    choices.

    Count those lying in NG with proper Sperner coloring.
    """
    n = len(ms)
    cycle_set = set(tuple(c) for c in cycle)
    proper = 0
    monochromatic = defaultdict(int)  # color -> count
    for v0 in itertools.product(*[range(m) for m in ms]):
        # Check all permutations of bump order for generality.
        for perm in itertools.permutations(range(n)):
            vertices = [tuple(v0)]
            cur = list(v0)
            ok = True
            for p in perm:
                if cur[p] + 1 >= ms[p]:
                    ok = False
                    break
                cur[p] += 1
                vertices.append(tuple(cur))
            if not ok:
                continue
            if any(v in cycle_set for v in vertices):
                continue
            colors = [coloring_fn(v, n, ms) for v in vertices]
            if len(set(colors)) == len(vertices):
                proper += 1
            if len(set(colors)) == 1:
                monochromatic[colors[0]] += 1
    # normalize: each simplex is counted n! times (one per permutation)
    return {
        "proper_simplices": proper // max(1, _factorial(n)),
        "monochromatic_by_color": {int(c): v // max(1, _factorial(n))
                                   for c, v in monochromatic.items()},
        "total_monochromatic": sum(monochromatic.values()) //
                               max(1, _factorial(n)),
    }


# ===== E6: Z/n-equivariant on symmetric ms =====

def zn_fixed_points_ng(ms, cycle):
    """Count Z/n rotation-fixed configs in NG (only meaningful for
    ms all-equal).
    """
    n = len(ms)
    if len(set(ms)) != 1:
        return None  # Z/n doesn't act properly
    m = ms[0]
    cycle_set = set(tuple(c) for c in cycle)
    fixed_under_k = {}  # rotation-by-k: #configs fixed
    for k in range(n):
        fixed = 0
        fixed_ng = 0
        # a config c is fixed by rotation k iff c[i] = c[(i+k) % n] for all i
        # equivalently c is periodic with period gcd(k, n)
        from math import gcd
        period = gcd(k, n) if k > 0 else n
        # each orbit of period p has free choices in [m]^p
        n_fixed = m ** period
        # count those in NG
        for base in itertools.product(range(m), repeat=period):
            config = tuple(base[(i % period)] for i in range(n))
            if config not in cycle_set:
                fixed_ng += 1
        fixed_under_k[k] = (n_fixed, fixed_ng)
    # Burnside: |NG / (Z/n)| = (1/n) Σ_k |NG^k|
    orbits_ng = sum(info[1] for info in fixed_under_k.values()) / n
    return {
        "ms_all_equal": True,
        "m": m,
        "fixed_under_rotation": fixed_under_k,
        "orbits_ng": orbits_ng,
    }


# ===== Driver =====

def run_multiset(n, ms, prod, max_cycles=3):
    threshold = M_n_sharp(n)
    tag = ("sub" if prod < threshold
           else "at" if prod == threshold else "super")
    L_max = 3 * n + 6
    cycles = enumerate_cycles_multistart(
        ms, n, L_min=6, L_max=L_max,
        time_budget=30.0, max_cycles=max_cycles)
    results = []
    for i, (cyc, movers, det) in enumerate(cycles):
        ambient = sum(m - 1 for m in ms)
        if ambient <= 6:
            fv_max = ambient
        elif ambient <= 9:
            fv_max = 5
        else:
            fv_max = 4
        t0 = time.time()
        fv, _ = f_vector_ng(ms, cyc, max_dim=fv_max)
        t_f = time.time() - t0

        # E5 content on small ms only (expensive)
        content = None
        if ambient <= 8:
            t0 = time.time()
            content = {}
            for cname, cfn in [
                ("parity", coloring_parity_mod_n),
                ("argmax", coloring_argmax),
                ("weighted", coloring_weighted_sum),
            ]:
                content[cname] = count_properly_colored_top(ms, cyc, cfn)
            t_c = time.time() - t0
        else:
            t_c = 0.0

        # E6 equivariant only for all-equal ms
        equiv = zn_fixed_points_ng(ms, cyc)

        chi = sum(((-1) ** k) * fv[k] for k in range(len(fv)))
        total_cells = sum(fv)

        results.append({
            "n": n, "ms": ms, "prod": prod, "tag": tag,
            "cycle_idx": i, "L": len(cyc),
            "f_vector": fv,
            "fv_max_dim": fv_max,
            "chi": chi,
            "total_cells": total_cells,
            "content": content,
            "equiv": equiv,
            "t_f_seconds": round(t_f, 2),
            "t_content_seconds": round(t_c, 2),
        })
    return results


def main():
    prod_ms = [
        (5, (2, 2, 2, 2, 2), 32),
        (5, (2, 2, 2, 2, 3), 48),
        (5, (2, 2, 2, 3, 3), 72),
        (5, (2, 2, 3, 3, 3), 108),
        (5, (2, 2, 2, 3, 4), 96),
        (6, (2, 2, 2, 2, 3, 3), 144),
        (6, (2, 2, 2, 3, 3, 3), 216),
        (6, (2, 2, 2, 3, 3, 4), 288),
        (5, (3, 3, 3, 3, 3), 243),  # symmetric, super-threshold
        (5, (2, 2, 2, 2, 2), 32),  # repeat of symmetric binary
    ]
    seen = set()
    all_results = []
    for n, ms, prod in prod_ms:
        if (n, ms) in seen:
            continue
        seen.add((n, ms))
        print(f"\n[E4-6] === ms={ms} n={n} ∏={prod} "
              f"(M_n*={M_n_sharp(n)}) ===")
        res = run_multiset(n, ms, prod, max_cycles=3)
        all_results.extend(res)
        for r in res:
            fv = r["f_vector"]
            print(f"  cycle{r['cycle_idx']} L={r['L']} tag={r['tag']}")
            print(f"    f-vector: {fv}")
            print(f"    χ(NG partial): {r['chi']}  "
                  f"total_cells: {r['total_cells']}")
            if r["content"]:
                for cname, cdata in r["content"].items():
                    print(f"    content/{cname}: proper_simp={cdata['proper_simplices']} "
                          f"mono_total={cdata['total_monochromatic']}")
            if r["equiv"]:
                e = r["equiv"]
                print(f"    equiv: m={e['m']} orbits_ng={e['orbits_ng']} "
                      f"fixed(k=0..n-1)={[info for info in e['fixed_under_rotation'].values()]}")

    # E4 aggregate
    print("\n[E4] ===== f-vector normalizations =====")
    print(f"{'ms':<18} {'tag':<5} {'L':>3} {'ambient':>7} {'c_0':>6} "
          f"{'c_1':>6} {'c_2':>6} {'χ_part':>7} {'c_0/M':>7}")
    for r in all_results:
        ms_str = str(r["ms"])
        M = r["prod"]
        fv = r["f_vector"]
        c0 = fv[0] if len(fv) > 0 else 0
        c1 = fv[1] if len(fv) > 1 else 0
        c2 = fv[2] if len(fv) > 2 else 0
        print(f"{ms_str:<18} {r['tag']:<5} {r['L']:>3} "
              f"{sum(m-1 for m in r['ms']):>7} "
              f"{c0:>6} {c1:>6} {c2:>6} {r['chi']:>7} "
              f"{c0/M:>7.3f}")

    # E5 aggregate
    print("\n[E5] ===== Herlihy content by coloring =====")
    print(f"{'ms':<18} {'tag':<5} {'L':>3} "
          f"{'parity/prop':>12} {'argmax/prop':>12} "
          f"{'weighted/prop':>14}")
    for r in all_results:
        if not r["content"]:
            continue
        p_p = r["content"]["parity"]["proper_simplices"]
        p_a = r["content"]["argmax"]["proper_simplices"]
        p_w = r["content"]["weighted"]["proper_simplices"]
        print(f"{str(r['ms']):<18} {r['tag']:<5} {r['L']:>3} "
              f"{p_p:>12} {p_a:>12} {p_w:>14}")

    # E6 aggregate (symmetric ms only)
    print("\n[E6] ===== equivariant data (symmetric ms) =====")
    for r in all_results:
        if r["equiv"]:
            e = r["equiv"]
            print(f"  {r['ms']} L={r['L']} tag={r['tag']} "
                  f"orbits_ng={e['orbits_ng']} m={e['m']}")

    return all_results


if __name__ == "__main__":
    main()
