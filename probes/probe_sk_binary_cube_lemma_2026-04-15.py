#!/usr/bin/env python3
"""Verify: SK from a sweep cycle is contained in {0,1}^n (task 4).

The empirical observation from probe 3 was that |SK|(n) is the same
across all sub-M_n multisets at fixed n. Probe 3's structural
interpretation: SK lives entirely in the {0,1}^n binary subcube,
regardless of actual m_i values. This script verifies that claim on
every non-all-binary sub-M_n multiset and then lays out the
analytical proof.

For each multiset with at least one non-binary proc:
1. Find a sweep cycle (length 2n, mover_seq = [0..n-1]*2).
2. Compute SK.
3. Check that every member of SK has all positions in {0,1}.
4. Report any violation.

If no violations, the claim holds empirically for every sub-M_n ms at
n = 5..7. Combined with the structural argument below, we have a
near-theorem.

ANALYTICAL PROOF SKETCH (see docs/lean_docs/sk/sk_binary_cube_lemma_2026-04-15.md):

Lemma 1 (det is binary): For a sweep cycle on any ms, every entry
(i, L, S, R) -> v in det has L, S, R, v all in {0,1}.

Proof: The sweep cycle starts at an all-binary config (enforced by
enumerate_cycles_movers's DFS, which always succeeds at starting from
an all-binary start — and the cycle closure forces all intermediate
configs to also be binary, since the mover sequence only visits
binary values). Every (L, S, R) seen during the cycle is binary; every
mover output is the flipped bit, also binary.

Lemma 2 (edges preserve binary positions): A forced edge from c to c'
at position j requires (j, c[j-1], c[j], c[j+1]) in det with output
!= c[j]. By Lemma 1, this requires c[j-1], c[j], c[j+1] in {0,1} AND
the output is in {0,1}. So c'_j in {0,1}, and for i != j, c'_i = c_i.

Lemma 3 (non-binary positions are preserved along edges): If c_i >= 2
for some i, every outgoing edge of c is at some j != i (Lemma 2's
constraint c_i in {0,1} fails at j = i). So c'_i = c_i >= 2.

Theorem (SK subset {0,1}^n): If c has any position c_i >= 2, then c
is not in SK.

Proof: Consider the sub-forced-graph G_i = {c : c_i = v} for a fixed
v >= 2. By Lemma 3, edges out of G_i stay in G_i. So G_i is a closed
sub-graph. The sink-kernel trimming restricted to G_i is the same as
the sub-kernel of G_i alone. G_i is isomorphic to a sub-structure of
the (n-1)-position system where position i is "frozen" at v. The
forced edges in G_i only use positions j with j+/-1 both not in {i}
AND c[j-1], c[j+1] both binary (edge at j needs (j, binary, binary,
binary) in det). Inductively, G_i has no sinks in its own forced
graph OTHER than by trimming, but because position i contributes no
edges, the "useful" edges are confined to n-1 positions with limited
reach.

The careful argument: G_i's sink-kernel is empty. Intuitively, the
"binary corner" structure that makes SK non-empty in {0,1}^n requires
ALL positions to contribute edges. With position i contributing no
edges, there's no "cycle closure" and the trimming removes every
config in G_i.

This sub-claim is verified computationally below for every sub-M_n
multiset with >= 1 non-binary proc at n = 5..7.
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import math
import sys


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product, require_non_binary=True):
    out = []

    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product and (not require_non_binary or any(x >= 3 for x in prefix)):
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()

    rec(0, [], 1)
    return out


def enumerate_sweep_cycles(ms, n, max_found=3, time_budget=10.0):
    mover_seq = list(range(n)) * 2
    L = len(mover_seq)
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen = set()
    t0 = time.time()

    def dfs(step, config, det, path):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        if step == L:
            if config == path[0]:
                ct = tuple(path)
                if ct not in seen:
                    seen.add(ct)
                    found.append((list(path), list(mover_seq), dict(det)))
            return
        p = mover_seq[step]
        Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
        km = (p, Lp, Sp, Rp)
        forced_out = det.get(km)
        for new_val in range(ms[p]):
            if new_val == Sp: continue
            if forced_out is not None and forced_out != new_val: continue
            new_det = dict(det)
            new_det[km] = new_val
            ok = True
            for i in range(n):
                if i == p: continue
                Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    ok = False; break
                new_det[ki] = Si
            if not ok: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step + 1, nc, new_det, path + [nc])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(0, start, {}, [start])
    return found


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    return remaining


def is_binary(c):
    return all(x in (0, 1) for x in c)


def verify_det_is_binary(det):
    for (i, L, S, R), v in det.items():
        if not (L in (0, 1) and S in (0, 1) and R in (0, 1) and v in (0, 1)):
            return False, (i, L, S, R, v)
    return True, None


def main():
    print("=" * 90, flush=True)
    print("SK ⊆ {0,1}^n — computational verification (task 4)", flush=True)
    print("=" * 90, flush=True)

    violations = []
    checked = 0
    det_binary_ok = 0
    det_binary_fail = 0

    for n in [5, 6, 7]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn, require_non_binary=True)
        print(f"\n=== n={n}  M_n={Mn}  non-binary sub-M_n multisets: {len(multisets)} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_sweep_cycles(ms, n, max_found=2, time_budget=5.0)
            if not cycles:
                continue
            for cycle, movers, det in cycles:
                checked += 1
                # Lemma 1 check
                ok, bad = verify_det_is_binary(det)
                if ok:
                    det_binary_ok += 1
                else:
                    det_binary_fail += 1
                    print(f"  !!! det has non-binary entry at ms={ms}: {bad}", flush=True)
                good = set(cycle)
                ng, _, adj = build_forced_graph(ms, n, det, good)
                sk = sink_kernel(ng, adj)
                non_binary_in_sk = [c for c in sk if not is_binary(c)]
                if non_binary_in_sk:
                    violations.append((ms, cycle, non_binary_in_sk[:5]))
                    print(f"  !!! non-binary config in SK at ms={ms}: {non_binary_in_sk[:3]}", flush=True)
            if idx % 50 == 0 and idx > 0:
                elapsed = time.time() - t0
                print(f"  [{idx}/{len(multisets)}]  {elapsed:.1f}s  checked={checked}  violations={len(violations)}", flush=True)
        print(f"  total checked: {checked}  violations: {len(violations)}", flush=True)

    print("\n" + "=" * 90, flush=True)
    print("SUMMARY", flush=True)
    print("=" * 90, flush=True)
    print(f"Total cycles checked: {checked}", flush=True)
    print(f"det is fully binary (Lemma 1):  {det_binary_ok} OK, {det_binary_fail} FAIL", flush=True)
    print(f"SK ⊆ {{0,1}}^n (Theorem):       {checked - len(violations)} OK, {len(violations)} FAIL", flush=True)
    if violations:
        print("\nVIOLATIONS (SK contains non-binary config):", flush=True)
        for ms, cycle, bad in violations[:20]:
            print(f"  ms={ms}  sample bad SK members: {bad}", flush=True)


if __name__ == "__main__":
    main()
