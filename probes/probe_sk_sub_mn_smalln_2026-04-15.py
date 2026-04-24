#!/usr/bin/env python3
"""SK at all sub-M_n multisets, n=5..8.

For each n in {5..8}, enumerate every state vector (m_0, ..., m_{n-1})
with m_i ≥ 2 and product strictly less than M_n = 32·3^(n-4). For each,
search for sweep AND bounce candidate cycles, run SK, and check whether
|SK| > 0 in every case.

Tests hypothesis 2: SK at the sharp M_n threshold may give the small-n
LB, even though SK at the loose 4·3^(n-2) threshold does not (because
the M_n witnesses live in the gap and use non-sweep cycles).

Outcome A: every sub-M_n (n, ms) has every tested cycle with |SK| > 0
  → hypothesis 2 partial-confirmed; SK at threshold M_n gives small-n LB
  for the cycle types tested

Outcome B: some sub-M_n (n, ms) has SOME tested cycle with |SK| = 0
  → hypothesis 2 dead for that case; need a different mechanism

Outcome C: some sub-M_n (n, ms) finds NO candidate cycles
  → cycle enumeration was too restrictive; inconclusive

This probe tests SWEEP and BOUNCE cycle types only. Other cycle types
(wiggle, mixed) would need a separate run. Not enough on its own to
prove anything, but enough to falsify hypothesis 2 if it falsifies it.
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import math


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3**(n-4)
    return 4 * 3**(n-2)


def enumerate_multisets(n, max_product):
    """Generate every (m_0, ..., m_{n-1}) with m_i ≥ 2 and product < max_product."""
    # Bound each m_i: since others are ≥ 2, m_i < max_product / 2^(n-1)
    max_each = max_product  # loose
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        # remaining positions all ≥ 2 → max for current is max_product / (prod * 2^(n-i-1))
        for m in range(2, max_each + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


def enumerate_cycles_movers(ms, n, mover_seq, max_found=3, time_budget=20.0):
    """DFS for closed cycles with a fixed mover sequence."""
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
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
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
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    ok = False; break
                new_det[ki] = Si
            if not ok: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

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
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True
                    break
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
        rounds += 1
    return remaining, rounds


def analyze(ms, n):
    """Return (any_empty_sk, num_cycles, min_sk, max_sk) across sweep+bounce."""
    sweep_seq = list(range(n)) * 2
    bounce_seq = list(range(n)) + list(range(n-2, 0, -1))
    cycles = []
    cycles += enumerate_cycles_movers(ms, n, sweep_seq, max_found=3, time_budget=10.0)
    cycles += enumerate_cycles_movers(ms, n, bounce_seq, max_found=3, time_budget=10.0)
    if not cycles:
        return None
    sk_sizes = []
    for cycle, movers, det in cycles:
        good_set = set(cycle)
        ng, _, adj = build_forced_graph(ms, n, det, good_set)
        sk, _ = sink_kernel(ng, adj)
        sk_sizes.append(len(sk))
    return (min(sk_sizes) == 0, len(cycles), min(sk_sizes), max(sk_sizes))


def main():
    print("=" * 90)
    print("SK at all sub-M_n multisets, n=5..8")
    print("=" * 90)
    print()
    print("For each n in 5..8, enumerate all (m_0..m_{n-1}) with m_i >= 2 and")
    print("product < M_n. Test sweep + bounce candidate cycles. Report cases where")
    print("ANY candidate cycle has |SK| = 0 (which would indicate a possibly-valid")
    print("system at sub-M_n product — refuting hypothesis 2 for that ms).")
    print()

    for n in [5, 6, 7, 8]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        print(f"\n=== n={n}  M_n={Mn}  multisets to check: {len(multisets)} ===")
        empty_sk_cases = []
        no_cycle_cases = []
        nontrivial_cases = []
        for ms in multisets:
            product = math.prod(ms)
            result = analyze(ms, n)
            if result is None:
                no_cycle_cases.append((ms, product))
                continue
            any_empty, ncyc, min_sk, max_sk = result
            nontrivial_cases.append((ms, product, ncyc, min_sk, max_sk))
            if any_empty:
                empty_sk_cases.append((ms, product, ncyc, min_sk, max_sk))

        print(f"  multisets with cycles found: {len(nontrivial_cases)}")
        print(f"  multisets with NO cycle found: {len(no_cycle_cases)}")
        if no_cycle_cases:
            print(f"    (no-cycle ms — these are inconclusive, sweep+bounce found nothing):")
            for ms, p in no_cycle_cases[:10]:
                print(f"      ms={ms} product={p}")
            if len(no_cycle_cases) > 10:
                print(f"      ... and {len(no_cycle_cases)-10} more")
        print(f"  multisets where SK was EMPTY for some candidate cycle: {len(empty_sk_cases)}")
        if empty_sk_cases:
            print(f"    !!! HYPOTHESIS 2 FALSIFIED for these ms !!!")
            for ms, p, nc, mn_sk, mx_sk in empty_sk_cases[:20]:
                print(f"      ms={ms} product={p}/{Mn} cycles={nc} SK range=[{mn_sk}, {mx_sk}]")
            if len(empty_sk_cases) > 20:
                print(f"      ... and {len(empty_sk_cases)-20} more")

        print()
        print(f"  summary table (first 10 nontrivial):")
        print(f"  {'ms':<25} {'product':<10} {'#cycles':<10} {'SK range'}")
        for ms, p, nc, mn_sk, mx_sk in nontrivial_cases[:10]:
            sk_range = f"[{mn_sk}, {mx_sk}]" if mn_sk != mx_sk else f"{mn_sk}"
            print(f"  {str(ms):<25} {p:<10} {nc:<10} {sk_range}")

    print()
    print("=" * 90)
    print("INTERPRETATION")
    print("=" * 90)
    print("""
- If empty_sk_cases is empty for all n in 5..8: hypothesis 2 partial-
  confirmed for sweep+bounce cycles. SK at the M_n threshold may suffice
  for the small-n LB, modulo non-sweep/non-bounce candidates.
- If empty_sk_cases is non-empty: those ms have SK = 0 candidate cycles
  at sub-M_n product, which means SK does NOT detect their invalidity.
  Hypothesis 2 is dead for those cases.
- If many no_cycle_cases: the cycle enumeration is too restrictive;
  many sub-M_n ms have no sweep/bounce candidate at all, so we can't
  conclude anything about them from this probe.
""")


if __name__ == "__main__":
    main()
