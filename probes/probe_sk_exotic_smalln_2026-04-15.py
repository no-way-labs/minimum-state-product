#!/usr/bin/env python3
"""Exotic cycle coverage at sub-M_n — probe 2 for hypothesis 2.

The previous probe (probe_sk_sub_mn_smalln_2026-04-15.py) tested only
sweep and bounce cycle families. This probe tests whether any
NON-sweep, NON-bounce cycle at sub-M_n product has |SK| = 0 (which
would falsify hypothesis 2 and kill the SK-at-sharp-threshold story).

Strategy. The M_n witnesses themselves (extracted from
LeanMn/SmallN/Defs.lean in probe_sk_small_n_witness_2026-04-15.py) use
exotic mover sequences with internal oscillations and backtracks:

  n=5 witness mover seq: [0,1,2,3,2,3,4, 0,1,2,3,4, 3,4,3,2,3,4]
  n=6 witness mover seq: [0,1,2,3,2,3,2,3,4,3,3,4,5, ...] (35 total)

These don't match sweep ([0,1,..,n-1]·2) or bounce ([0,..,n-1,n-2,..,1]).
At SUPER-M_n product they give SK = 0 (as confirmed by probe 1). The
question is whether any SUB-M_n multiset admits a similar exotic cycle
that ALSO has SK = 0.

Two kinds of templates tested:

  1. Witness templates. The exact mover sequences from M_5..M_8 witnesses.
  2. Wiggle templates. [0,1,..,n-1, n-2, n-3, ..., 1] of length 2n-2 and
     variants.
  3. Free DFS up to depth 2n (brute-force exotic search on small n).

For each sub-M_n multiset, each template is run as a fixed mover
sequence (like the existing probe) and SK is computed for each closed
cycle found. Any |SK| = 0 at sub-M_n is a falsification.

Free-DFS enumeration is used only for n = 5 (otherwise explodes). For
n ≥ 6 we rely on the template approach.

Outcome A: zero falsifications anywhere → hypothesis 2 strengthens
  across exotic cycle families as well.

Outcome B: some sub-M_n cycle has SK = 0 → hypothesis 2 is false,
  report the (ms, cycle, mover_seq) so it can be inspected.
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import math


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product):
    out = []

    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
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


def enumerate_cycles_movers(ms, n, mover_seq, max_found=3, time_budget=10.0):
    L = len(mover_seq)
    if any(p >= n for p in mover_seq):
        return []
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


def enumerate_free_cycles(ms, n, max_length, time_budget=30.0, max_found=20):
    """Brute-force enumerate closed cycles of length ≤ max_length with ANY mover.

    Expensive: only use for small n. Returns list of (cycle, movers, det).
    """
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            # normalize cycle (rotate so min tuple is first)
            norm = min(tuple(path[i:] + path[:i]) for i in range(len(path)))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path), list(movers), dict(det)))
            return
        if len(path) >= max_length:
            return
        for p in range(n):
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
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
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


# Exotic templates, indexed by n. Witness templates are the exact M_n
# witness mover sequences extracted from Defs.lean.
WITNESS_TEMPLATES = {
    5: [0, 1, 2, 3, 2, 3, 4, 0, 1, 2, 3, 4, 3, 4, 3, 2, 3, 4],
    6: [0, 1, 2, 3, 2, 3, 2, 3, 4, 3, 3, 4, 5, 0, 1, 2, 3, 2, 3, 2, 3, 4, 3, 4, 5, 4, 3, 2, 3, 2, 3, 4, 3, 4, 5],
    7: [0, 0, 1, 2, 3, 4, 3, 4, 5, 4, 5, 4, 3, 4, 5, 5, 4, 5, 6, 5, 4, 3, 4, 5, 6, 0, 6, 5, 5, 4, 5, 4, 3, 4, 5, 5, 4, 5, 6, 5, 6, 0, 1, 2, 3, 4, 5, 4, 5, 6, 0, 6],
    8: [0, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3, 2, 3, 4, 3, 2, 1, 2, 3, 4, 5, 4, 3, 3, 2, 3, 2, 1, 2, 3, 3, 2, 3, 4, 3, 4, 5, 6, 7, 6, 7, 0, 1, 2, 3, 2, 3, 4, 5, 6, 7, 6, 7],
}


def wiggle_template(n):
    return list(range(n)) + list(range(n - 2, 0, -1))  # same as bounce — skip


def get_templates(n):
    """Return list of (name, mover_seq) exotic templates for this n."""
    templates = []
    if n in WITNESS_TEMPLATES:
        templates.append((f"witness_n{n}", WITNESS_TEMPLATES[n]))
    # Double-wiggle: go up then part-way back then up again
    templates.append(("double_wiggle", list(range(n)) + list(range(n - 2, 0, -1)) + list(range(n))))
    # Half-sweep twice
    half = n // 2
    templates.append(("half_sweep_twice", list(range(n)) + list(range(half, n)) + list(range(half))))
    # Wiggle: single sweep + reverse (= bounce but doubled to distinguish)
    templates.append(("wiggle_triple", list(range(n)) + list(range(n - 2, 0, -1)) + list(range(n)) + list(range(n - 2, 0, -1))))
    return templates


def analyze_ms(ms, n, use_free_dfs=False, free_depth=None):
    """Run exotic templates on ms and return (cycles_tested, min_sk, violations)."""
    violations = []
    total_cycles = 0
    min_sk_seen = None
    for tname, tseq in get_templates(n):
        # fairness filter on template
        if set(tseq) != set(range(n)):
            continue
        cycles = enumerate_cycles_movers(ms, n, tseq, max_found=2, time_budget=3.0)
        for cycle, movers, det in cycles:
            total_cycles += 1
            good = set(cycle)
            ng, _, adj = build_forced_graph(ms, n, det, good)
            sk = sink_kernel(ng, adj)
            if min_sk_seen is None or len(sk) < min_sk_seen:
                min_sk_seen = len(sk)
            if len(sk) == 0:
                violations.append((tname, cycle, movers, 0))
    if use_free_dfs:
        L_max = free_depth if free_depth is not None else 2 * n + 2
        cycles = enumerate_free_cycles(ms, n, max_length=L_max, time_budget=10.0, max_found=50)
        for cycle, movers, det in cycles:
            # fairness filter: every processor must fire
            if set(movers) != set(range(n)):
                continue
            total_cycles += 1
            sweep_seq = list(range(n)) * (len(movers) // n + 1)
            bounce_seq = (list(range(n)) + list(range(n - 2, 0, -1))) * 2
            if movers == sweep_seq[:len(movers)] or movers == bounce_seq[:len(movers)]:
                continue
            good = set(cycle)
            ng, _, adj = build_forced_graph(ms, n, det, good)
            sk = sink_kernel(ng, adj)
            if min_sk_seen is None or len(sk) < min_sk_seen:
                min_sk_seen = len(sk)
            if len(sk) == 0:
                violations.append(("free_dfs", cycle, movers, 0))
    return total_cycles, min_sk_seen, violations


def main():
    import sys
    print("=" * 90, flush=True)
    print("Exotic cycles at sub-M_n — probe 2 (hypothesis 2 falsification check)", flush=True)
    print("=" * 90, flush=True)

    for n in (5, 6, 7, 8):
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        # For tractability: at larger n use a sampled subset
        if n == 7:
            multisets = multisets[:: max(1, len(multisets) // 100)]
        if n == 8:
            multisets = multisets[:: max(1, len(multisets) // 50)]
        print(f"\n=== n={n}  M_n={Mn}  testing {len(multisets)} sub-M_n multisets ===", flush=True)
        total_violations = []
        total_no_cycle = 0
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            use_free = (n <= 6)
            total_cycles, min_sk, viols = analyze_ms(ms, n, use_free_dfs=use_free)
            if total_cycles == 0:
                total_no_cycle += 1
            if viols:
                total_violations.append((ms, viols))
                print(f"  !!! falsification at ms={ms}: {len(viols)} |SK|=0 exotic cycles", flush=True)
                for tname, cycle, movers, sk_size in viols[:2]:
                    print(f"      template={tname}  cycle_len={len(cycle)}  movers={movers}", flush=True)
            if idx % 25 == 0:
                elapsed = time.time() - t0
                print(f"  [{idx}/{len(multisets)}]  {elapsed:.1f}s  violations so far: {len(total_violations)}  no-cycle: {total_no_cycle}", flush=True)

        print(f"  total violations: {len(total_violations)} / {len(multisets)}  no-cycle: {total_no_cycle}", flush=True)

    print("\n" + "=" * 90)
    print("INTERPRETATION")
    print("=" * 90)
    print("""
If total_violations is empty across all n: hypothesis 2 strengthens to
include witness-template and wiggle/double-wiggle cycle families. It
still does not cover ARBITRARY cycles, but the exotic templates most
closely aligned with the actual M_n witnesses have been ruled out.

If any violation exists: hypothesis 2 is FALSE for that (ms, template).
Inspect the reported cycle and mover sequence — the system may be a
genuine valid sub-M_n system (would contradict M_n sharp), or it may
be a trapped "closed det cycle" that is not a valid good cycle for
uniqueness/fairness reasons.
""")


if __name__ == "__main__":
    main()
