#!/usr/bin/env python3
"""E23 — HKR Index Lemma / Manifold Sperner / signed Content probe.

Goal
----
Test whether the HKR "Content" invariant (Def 12.3.3, Index Lemma 12.3.5)
discriminates sub-threshold good cycles from at/super-threshold good cycles.

Why this is the last binary discriminator
-----------------------------------------
All prior SK probes (E2-E22) failed to produce a sub-vs-at-threshold
signal. The Index Lemma is the canonical topological obstruction in the
HKR book for asynchronous shared-memory impossibility (WSB, 2n-renaming).
Content is a signed count; "Content = 0 everywhere" would mean Index Lemma
has no bite for us; "Content forced to nonzero by sub-threshold regime"
would reopen the Lean lower bound.

Setting fit (CAVEAT, see final verdict)
---------------------------------------
Book: M = Ch^N σ (iterated chromatic subdivision of an n-simplex),
      binary coloring b : V(M) → {0,1}, content C(M, b) counts
      n-simplices monochromatic under b, SIGNED by orientation.

Ours: good cycle C = c_0, c_1, ..., c_{L-1} in Config = ∏_p Z_{m_p}.
      The cycle is a 1-manifold (closed loop); not a subdivided n-simplex.
      Firing events: at step k, mover position p_k, src triple (L_k,S_k,R_k),
      target value t_k ≠ S_k.

Construction candidates
-----------------------
(A) 1-manifold chain (trivial, but reveals any parity structure).
    - Vertices: steps 0..L-1 on the cycle.
    - Binary colorings b(k) derived from det / mover / source structure.
    - "Content" = number of sign changes of b around the loop.
    - Closed loop ⟹ #sign changes is even. Test:
        * Does #changes / 2 separate sub vs at threshold?
        * Does it have a canonical value forced by ms product?

(B) 2-torus (position × step).
    - Vertices V = {(p, k) : p ∈ [n], k ∈ [L]}.
    - Triangulate the torus; orient coherently.
    - Coloring c : V → Δ^2: three-color by value class (small/mid/large).
    - Count oriented 2-simplices properly colored vs monochromatic.
    - Sub vs at threshold: count differs?

(C) Source-triple 1-complex with richer coloring.
    - Vertices = firing events i.
    - Edges i → i+1. Binary colorings:
        * b1(i) = 1 iff p_i is even
        * b2(i) = 1 iff target t_i = 0
        * b3(i) = 1 iff S_i < m_{p_i}/2
        * b4(i) = parity(# of binary positions in (L_i, S_i, R_i))
    - Content = signed sign-change count mod various moduli.

(D) "Monochromatic simplex count with boundary" analog.
    - Treat cycle as a 1-skeleton in ∏ Δ^{m_p - 1}.
    - Count monochromatic 1-edges (i.e., firing transitions where a specific
      binary prop holds on both endpoints) signed by cycle orientation.

We run A–C. Each is O(L · n) per record, ≤ 1s per cycle. Tripwire-gated.

Verdict rules
-------------
GREEN: (a) Content forced to a nonzero value in sub-threshold records
       (and (b) forced differently or to zero at at/super-threshold).
       Implies an algebraic obstruction — promote to Lean.
YELLOW: Partial signal; one coloring separates but evidence thin.
RED: All colorings give identical distributions sub vs at.
"""
from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct


# ----- thresholds --------------------------------------------------------

def m_n(n: int) -> int:
    """M_n sharp: 32·3^(n-4) for 5≤n≤8, 4·3^(n-2) for n≥9."""
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


# ----- multiset enumeration ----------------------------------------------

def enumerate_multisets(n: int, max_product_strict: int, at_threshold: bool = False):
    """If at_threshold: multisets with ∏m_i == M_n exactly.
       Else: multisets with ∏m_i < M_n (strict)."""
    Mn = m_n(n)
    out = []

    def rec(i, prefix, prod):
        if i == n:
            if at_threshold:
                if prod == Mn:
                    out.append(tuple(prefix))
            else:
                if prod < Mn:
                    out.append(tuple(prefix))
            return
        # Upper bound: at_threshold allows =, strict requires <
        upper = Mn if at_threshold else (Mn)
        for m in range(2, upper + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            # Prune: if new_prod · min_remaining > Mn (at_threshold: strict >),
            # (strict: >=) no extension works.
            if at_threshold:
                if new_prod * min_remaining > Mn:
                    break
            else:
                if new_prod * min_remaining >= Mn:
                    break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()

    rec(0, [], 1)
    return out


# ----- cycle enumeration -------------------------------------------------

def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    """DFS cycle enumerator (seed-forced det, simple fair cycles)."""
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]
            Sp = config[p]
            Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]
                    Si = config[i]
                    Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False
                        break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config)
                nc[p] = new_val
                nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


# ----- INDEX-LEMMA-INSPIRED COLORINGS + CONTENT COMPUTATIONS -------------

def compute_A_1manifold_signchanges(cycle, movers, det, ms, n):
    """Construction A: 1-manifold, binary coloring from many candidates,
    content = signed sign-change count on the closed loop.

    For a closed 1-manifold, a binary labeling b: [L] → {0,1} has a natural
    "number of sign changes around the loop", which is necessarily EVEN.
    We report #changes and #changes // 2 (mod various moduli).

    In the HKR index lemma setting (dim 1, binary coloring), content = 0 for
    closed manifold (∂ = ∅). We instead track #changes to see if it's a
    nontrivial invariant.
    """
    L = len(cycle)
    results = {}

    # Candidate binary colorings
    colorings = {}

    # b_moverparity: mover position parity
    colorings['moverparity'] = [movers[k] % 2 for k in range(L)]

    # b_targetzero: target value at firing k equals 0
    targets = []
    for k in range(L):
        p = movers[k]
        next_c = cycle[(k + 1) % L]
        targets.append(next_c[p])
    colorings['targetzero'] = [1 if t == 0 else 0 for t in targets]

    # b_sourcesmall: source value S_k < m_{p_k}/2
    colorings['sourcesmall'] = []
    for k in range(L):
        p = movers[k]
        Sv = cycle[k][p]
        colorings['sourcesmall'].append(1 if Sv < ms[p] / 2.0 else 0)

    # b_binaryfire: mover is a binary position (ms[p]=2)
    colorings['binaryfire'] = [1 if ms[movers[k]] == 2 else 0 for k in range(L)]

    # b_triplebinparity: parity of (# binary among (L_k,S_k,R_k) bin positions)
    # Here "binary" meaning value is in {0,1} at ternary+ proc (trivially true
    # at binary proc). Use bin-proc indicator instead.
    colorings['leftbin'] = []
    for k in range(L):
        p = movers[k]
        colorings['leftbin'].append(1 if ms[(p - 1) % n] == 2 else 0)

    # b_det_direction: target > source at binary positions, 0 elsewhere
    colorings['targetup'] = []
    for k in range(L):
        p = movers[k]
        Sv = cycle[k][p]
        Tv = cycle[(k + 1) % L][p]
        colorings['targetup'].append(1 if Tv > Sv else 0)

    # b_firstbindetpos: mover position in {0,1,...,floor(n/2)}
    colorings['firsthalf'] = [1 if movers[k] < n / 2.0 else 0 for k in range(L)]

    for name, b in colorings.items():
        changes = sum(1 for k in range(L) if b[k] != b[(k + 1) % L])
        # Parity of changes -- must be 0 for any closed loop
        # (for 2-valued coloring on a cycle the change count is always even).
        half_changes = changes // 2
        results[name] = {
            'changes': changes,
            'halfchanges': half_changes,
            'halfchanges_mod_n': half_changes % n,
            'halfchanges_mod_np1': half_changes % (n + 1),
            'ones': sum(b),
            'ones_mod_n': sum(b) % n,
        }
    return results


def compute_B_2complex_signed_content(cycle, movers, det, ms, n):
    """Construction B: 2-complex on position × step (n × L torus-like).

    We lay out the cycle as a 2D grid (p ∈ [n], k ∈ [L]) with cell (p,k) =
    c_k[p]. Triangulate each unit square (p,k)—(p+1,k)—(p+1,k+1)—(p,k+1) into
    two triangles T^+_{p,k} = {(p,k),(p+1,k),(p+1,k+1)} and
                 T^-_{p,k} = {(p,k),(p+1,k+1),(p,k+1)},
    orient both with +1 sign using the standard counterclockwise convention.

    Binary coloring: b(p, k) = 1 iff c_k[p] ≥ ms[p]/2  (value "high").
    (And variants below.)

    For each oriented triangle, check:
    - "Monochromatic under b": all three vertices have same b value.
    - Signed count = (+1) - (-1) based on triangle orientation parity.

    We compute the signed count of "1-monochromatic" triangles and
    "0-monochromatic" triangles and their difference.

    This is an ANALOG of Content restricted to binary-mono 2-simplices;
    HKR's Lemma 12.4.3 says C(Ch^N σ, 0(·)) = 1 and C(Ch^N σ, 1(·)) = (-1)^n,
    which is a signed count of monochromatic simplices.
    """
    L = len(cycle)
    results = {}

    def build_bcolor(ms, cycle, scheme):
        b = {}
        for k in range(L):
            for p in range(n):
                v = cycle[k][p]
                if scheme == 'high':
                    b[(p, k)] = 1 if v >= ms[p] / 2.0 else 0
                elif scheme == 'nonzero':
                    b[(p, k)] = 1 if v != 0 else 0
                elif scheme == 'parity':
                    b[(p, k)] = v % 2
                elif scheme == 'mover_in_triangle':
                    # b = 1 iff this (p,k) cell is a mover event (p == movers[k])
                    b[(p, k)] = 1 if (p == movers[k]) else 0
        return b

    for scheme in ['high', 'nonzero', 'parity', 'mover_in_triangle']:
        b = build_bcolor(ms, cycle, scheme)
        # Enumerate oriented 2-cells
        mono0_plus = mono0_minus = 0
        mono1_plus = mono1_minus = 0
        nonmono = 0
        for k in range(L):
            for p in range(n):
                kn = (k + 1) % L
                pn = (p + 1) % n  # position is a ring (token ring)
                # Wait: positions are on a RING (p connects to p±1 mod n),
                # and steps are on a RING (cycle is closed).
                # So (p,k) is on a 2-torus in (p mod n) × (k mod L).

                v00 = b[(p, k)]
                v10 = b[(pn, k)]
                v01 = b[(p, kn)]
                v11 = b[(pn, kn)]

                # T+ = {(p,k),(pn,k),(pn,kn)}  orientation +1
                if v00 == v10 == v11:
                    if v00 == 1:
                        mono1_plus += 1
                    else:
                        mono0_plus += 1
                else:
                    nonmono += 1
                # T- = {(p,k),(pn,kn),(p,kn)}  orientation (+1 matching torus)
                if v00 == v11 == v01:
                    if v00 == 1:
                        mono1_minus += 1
                    else:
                        mono0_minus += 1
                else:
                    nonmono += 1

        # Signed counts: in a consistently oriented torus, both T+ and T- have
        # +1 orientation; but they contribute to opposite "which vertex is
        # missing" in the Face_i sense. We use a simple signed diff:
        #   signed_mono0 = mono0_plus - mono0_minus
        #   signed_mono1 = mono1_plus - mono1_minus
        results[scheme] = {
            'mono0_plus': mono0_plus, 'mono0_minus': mono0_minus,
            'mono1_plus': mono1_plus, 'mono1_minus': mono1_minus,
            'signed_mono0': mono0_plus - mono0_minus,
            'signed_mono1': mono1_plus - mono1_minus,
            'mono0_total': mono0_plus + mono0_minus,
            'mono1_total': mono1_plus + mono1_minus,
            'nonmono': nonmono,
        }
    return results


def compute_C_sourcetriple_ring(cycle, movers, det, ms, n):
    """Construction C: source-triple 1-complex with multiple colorings.

    Vertices = firing events k ∈ [L], edges k → k+1 (cyclic).
    Multiple binary colorings; for each, report sign-change count AND
    a "triple signed alternation" statistic:
       T(b) = Σ_k (-1)^k · b(k)  (signed sum)
    which is an Index-Lemma-flavored signed count.

    Also, a modulus invariant:
       M(b) := Σ_k b(k) · (-1)^{p_k}  (signed by mover parity)

    These are candidate "contents" for the 1-simplex ring structure.
    """
    L = len(cycle)
    results = {}

    colorings = {}
    colorings['sourcebinary'] = []
    for k in range(L):
        p = movers[k]
        # mover value in {0,1} (binary at ms[p]=2 is always this; at m≥3 it's half)
        Sv = cycle[k][p]
        colorings['sourcebinary'].append(1 if Sv in (0, 1) else 0)

    colorings['targetbinary'] = []
    for k in range(L):
        p = movers[k]
        Tv = cycle[(k + 1) % L][p]
        colorings['targetbinary'].append(1 if Tv in (0, 1) else 0)

    colorings['tripleallbin'] = []
    for k in range(L):
        p = movers[k]
        Lv = cycle[k][(p - 1) % n]
        Sv = cycle[k][p]
        Rv = cycle[k][(p + 1) % n]
        colorings['tripleallbin'].append(
            1 if (Lv in (0, 1) and Sv in (0, 1) and Rv in (0, 1)) else 0
        )

    colorings['moverposmod2'] = [movers[k] % 2 for k in range(L)]
    colorings['moverposmod3'] = [1 if movers[k] % 3 == 0 else 0 for k in range(L)]

    for name, b in colorings.items():
        changes = sum(1 for k in range(L) if b[k] != b[(k + 1) % L])
        T_signed = sum((-1) ** k * b[k] for k in range(L))
        M_signed = sum(((-1) ** movers[k]) * b[k] for k in range(L))
        results[name] = {
            'ones': sum(b),
            'changes': changes,
            'T_signed': T_signed,
            'M_signed': M_signed,
            'T_mod_n': T_signed % (2 * n),
            'M_mod_n': M_signed % (2 * n),
        }
    return results


# ----- driver ------------------------------------------------------------

def regime_tag(ms, n):
    prod = 1
    for m in ms:
        prod *= m
    Mn = m_n(n)
    if prod < Mn:
        return 'sub'
    elif prod == Mn:
        return 'at'
    else:
        return 'super'


def process_multisets(n, multisets, L_max, time_budget, max_cycles, label):
    records = []
    t0 = time.time()
    total_ms = len(multisets)
    for idx, ms in enumerate(multisets):
        cycles = enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles)
        for cycle, movers, det in cycles:
            L = len(movers)
            # Require length at least n (fair), but accept any L ≥ n that
            # covers all positions.
            if len(set(movers)) != n:
                continue
            rec = {
                'n': n,
                'ms': list(ms),
                'L': L,
                'regime': label,
                'product': 1,
                'A': compute_A_1manifold_signchanges(cycle, movers, det, ms, n),
                'B': compute_B_2complex_signed_content(cycle, movers, det, ms, n),
                'C': compute_C_sourcetriple_ring(cycle, movers, det, ms, n),
            }
            prod = 1
            for m in ms:
                prod *= m
            rec['product'] = prod
            records.append(rec)
        if (idx + 1) % max(1, total_ms // 10) == 0 or idx == total_ms - 1:
            print(f"  [{label}][{idx+1}/{total_ms}]  t={time.time()-t0:.0f}s  "
                  f"records={len(records)}", flush=True)
    return records


def summarize(records, label):
    """Per (coloring, n) report distribution of key statistics."""
    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    summary = {}
    for n in sorted(by_n):
        recs = by_n[n]
        summary[n] = {'count': len(recs), 'A': {}, 'B': {}, 'C': {}}

        if not recs:
            continue

        # A colorings
        a_colorings = list(recs[0]['A'].keys())
        for col in a_colorings:
            halfchanges = Counter(r['A'][col]['halfchanges'] for r in recs)
            ones = Counter(r['A'][col]['ones'] for r in recs)
            halfchanges_mod_n = Counter(r['A'][col]['halfchanges_mod_n'] for r in recs)
            summary[n]['A'][col] = {
                'halfchanges_dist': dict(halfchanges.most_common(10)),
                'ones_dist': dict(ones.most_common(10)),
                'halfchanges_mod_n_dist': dict(halfchanges_mod_n.most_common(10)),
                'halfchanges_min': min(r['A'][col]['halfchanges'] for r in recs),
                'halfchanges_max': max(r['A'][col]['halfchanges'] for r in recs),
            }

        # B colorings
        b_colorings = list(recs[0]['B'].keys())
        for col in b_colorings:
            smono0 = Counter(r['B'][col]['signed_mono0'] for r in recs)
            smono1 = Counter(r['B'][col]['signed_mono1'] for r in recs)
            m0_total = Counter(r['B'][col]['mono0_total'] for r in recs)
            m1_total = Counter(r['B'][col]['mono1_total'] for r in recs)
            summary[n]['B'][col] = {
                'signed_mono0_dist': dict(smono0.most_common(10)),
                'signed_mono1_dist': dict(smono1.most_common(10)),
                'mono0_total_dist': dict(m0_total.most_common(10)),
                'mono1_total_dist': dict(m1_total.most_common(10)),
            }

        # C colorings
        c_colorings = list(recs[0]['C'].keys())
        for col in c_colorings:
            tmodn = Counter(r['C'][col]['T_mod_n'] for r in recs)
            mmodn = Counter(r['C'][col]['M_mod_n'] for r in recs)
            tsigned = Counter(r['C'][col]['T_signed'] for r in recs)
            summary[n]['C'][col] = {
                'T_mod_n_dist': dict(tmodn.most_common(10)),
                'M_mod_n_dist': dict(mmodn.most_common(10)),
                'T_signed_dist': dict(tsigned.most_common(10)),
            }
    return summary


def compare_sub_at(sub_records, at_records):
    """Key discriminator check: for each coloring, does the distribution of
    {halfchanges, signed_mono0, T_mod_n, ...} differ between sub and at?
    """
    def per_coloring_distribution(records, construction, coloring, stat):
        c = Counter()
        for r in records:
            c[r[construction][coloring][stat]] += 1
        return c

    report = []
    constructions = {
        'A': [('moverparity', 'halfchanges'), ('moverparity', 'halfchanges_mod_n'),
              ('targetzero', 'halfchanges'), ('sourcesmall', 'halfchanges'),
              ('binaryfire', 'halfchanges'), ('targetup', 'halfchanges'),
              ('firsthalf', 'halfchanges')],
        'B': [('high', 'signed_mono0'), ('high', 'signed_mono1'),
              ('nonzero', 'signed_mono0'), ('nonzero', 'signed_mono1'),
              ('parity', 'signed_mono0'), ('mover_in_triangle', 'signed_mono0'),
              ('high', 'mono0_total'), ('high', 'mono1_total')],
        'C': [('sourcebinary', 'T_mod_n'), ('sourcebinary', 'T_signed'),
              ('targetbinary', 'T_signed'), ('tripleallbin', 'T_signed'),
              ('moverposmod2', 'T_signed'), ('moverposmod3', 'T_signed')],
    }
    for cons, pairs in constructions.items():
        for col, stat in pairs:
            sub_dist = per_coloring_distribution(sub_records, cons, col, stat)
            at_dist = per_coloring_distribution(at_records, cons, col, stat)
            sub_support = set(sub_dist.keys())
            at_support = set(at_dist.keys())
            sub_only = sub_support - at_support
            at_only = at_support - sub_support
            shared = sub_support & at_support
            report.append({
                'construction': cons,
                'coloring': col,
                'stat': stat,
                'sub_n': sum(sub_dist.values()),
                'at_n': sum(at_dist.values()),
                'sub_support': sorted(sub_support),
                'at_support': sorted(at_support),
                'sub_only': sorted(sub_only),
                'at_only': sorted(at_only),
                'shared': sorted(shared),
                'sub_top5': dict(sub_dist.most_common(5)),
                'at_top5': dict(at_dist.most_common(5)),
            })
    return report


def verdict_from_report(report):
    """Heuristic verdict from per-coloring comparison."""
    discriminating = []
    for row in report:
        sub_only = row['sub_only']
        at_only = row['at_only']
        # Discriminator criterion: at least one value is present in sub but
        # NEVER in at (or vice versa), across reasonable sample sizes.
        if (sub_only and row['at_n'] >= 5) or (at_only and row['sub_n'] >= 5):
            discriminating.append(row)
    return discriminating


def main():
    print("=" * 72, flush=True)
    print("E23 — HKR Index Lemma / signed Content probe", flush=True)
    print("=" * 72, flush=True)

    # Conservative plan for each n
    # (n, stride_sub, max_cycles_per_ms, time_budget_per_ms, L_max)
    # We want BOTH sub-threshold and at-threshold multisets.
    plan_sub = [
        (5, 1, 30, 2.0, 15),
        (6, 2, 20, 3.0, 17),
        (7, 20, 10, 3.0, 19),
        (8, 120, 4, 4.0, 21),
    ]
    plan_at = [
        (5, 1, 30, 2.0, 15),
        (6, 2, 20, 3.0, 17),
        (7, 10, 10, 3.0, 19),
        (8, 30, 4, 4.0, 21),
    ]

    all_sub = []
    all_at = []
    t_start = time.time()

    for (n, stride, max_cycles, tb, L_max), (n2, stride2, mc2, tb2, L2) in zip(plan_sub, plan_at):
        assert n == n2
        # Sub-threshold
        mult_sub = enumerate_multisets(n, m_n(n), at_threshold=False)
        samp_sub = mult_sub[::stride]
        # At-threshold (apply at-plan stride)
        mult_at = enumerate_multisets(n, m_n(n), at_threshold=True)
        samp_at = mult_at[::stride2]

        print(f"\n=== n={n}  M_n={m_n(n)}  "
              f"sub_multisets={len(mult_sub)} sampled={len(samp_sub)}  "
              f"at_multisets={len(mult_at)} ===", flush=True)

        print(f"\n-- sub-threshold scan --", flush=True)
        sub_recs = process_multisets(n, samp_sub, L_max, tb, max_cycles, 'sub')
        all_sub.extend(sub_recs)

        print(f"\n-- at-threshold scan --", flush=True)
        at_recs = process_multisets(n, samp_at, L2, tb2, mc2, 'at')
        all_at.extend(at_recs)

    print(f"\n{'='*72}")
    print(f"Scan done. sub={len(all_sub)}  at={len(all_at)}  t={time.time()-t_start:.0f}s")
    print(f"{'='*72}")

    sub_summary = summarize(all_sub, 'sub')
    at_summary = summarize(all_at, 'at')

    print("\n--- Per-n coloring summary (sub) ---")
    for n, s in sub_summary.items():
        print(f"\nn={n} count={s['count']}")
        for col, stats in s['A'].items():
            print(f"  A[{col}] halfchanges: dist={stats['halfchanges_dist']} "
                  f"range={stats['halfchanges_min']}..{stats['halfchanges_max']}")

    print("\n--- Per-n coloring summary (at) ---")
    for n, s in at_summary.items():
        print(f"\nn={n} count={s['count']}")
        for col, stats in s['A'].items():
            print(f"  A[{col}] halfchanges: dist={stats['halfchanges_dist']}")

    # Split by n for per-n comparison
    by_n_sub = defaultdict(list)
    by_n_at = defaultdict(list)
    for r in all_sub:
        by_n_sub[r['n']].append(r)
    for r in all_at:
        by_n_at[r['n']].append(r)

    all_discriminators = {}
    for n in sorted(set(by_n_sub) | set(by_n_at)):
        print(f"\n{'='*72}\nComparing sub vs at for n={n}\n{'='*72}")
        subs = by_n_sub.get(n, [])
        ats = by_n_at.get(n, [])
        if not subs or not ats:
            print(f"  skipping n={n}: sub={len(subs)} at={len(ats)}")
            continue
        rep = compare_sub_at(subs, ats)
        disc = verdict_from_report(rep)
        all_discriminators[n] = disc
        print(f"  report entries: {len(rep)}  discriminating: {len(disc)}")
        for row in disc[:15]:
            print(f"    [{row['construction']}][{row['coloring']}][{row['stat']}]  "
                  f"sub_only={row['sub_only'][:5]}  at_only={row['at_only'][:5]}  "
                  f"sub_n={row['sub_n']}  at_n={row['at_n']}")

    # --- VERDICT ---
    print(f"\n{'='*72}")
    print("VERDICT")
    print(f"{'='*72}")
    total_disc = sum(len(d) for d in all_discriminators.values())
    if total_disc == 0:
        verdict = 'RED'
        print("RED — No coloring in A/B/C separates sub vs at-threshold cycles.")
        print("Content distributions overlap entirely. The Index Lemma")
        print("framework does not discriminate our good-cycle data.")
    elif total_disc < 3:
        verdict = 'YELLOW'
        print(f"YELLOW — {total_disc} potentially discriminating colorings")
        print("but signal is thin. Further probe iteration needed.")
    else:
        verdict = 'GREEN'
        print(f"GREEN — {total_disc} discriminating (coloring, stat) pairs found.")
        print("Promote to Lean target.")
    print(f"{'='*72}")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_json = os.path.join(out_dir, 'e23_index_lemma_2026-04-20.json')
    with open(out_json, 'w') as f:
        json.dump({
            'plan_sub': plan_sub,
            'plan_at': plan_at,
            'sub_summary': sub_summary,
            'at_summary': at_summary,
            'discriminators': {str(k): v for k, v in all_discriminators.items()},
            'verdict': verdict,
            'n_sub': len(all_sub),
            'n_at': len(all_at),
        }, f, default=str)
    print(f"\nWrote {out_json}")


if __name__ == "__main__":
    main()
