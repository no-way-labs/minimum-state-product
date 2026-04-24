#!/usr/bin/env python3
"""
Profile the explicit-bad TP-preserving 239 -> 245 family.

This script isolates the local obstruction family behind the non-special
bridge fact:

  boundary-changing CΦ cannot realize 239 -> 245

What it checks for n in a given range:
  - all TP-preserving bad 239 -> 245 candidates come from local triple (1,0,2)
  - fc always drops by 1
  - PhiFull always drops by 1 on the bad TP-preserving cases
  - the realized bad family is classified by the first non-1 symbol in the
    free interior prefix:
      first non-1 = 0  -> PhiFull = fc
      first non-1 = 2  -> PhiFull = fc + 1

This is not yet a Lean proof, but it freezes a concrete all-n-looking
candidate for the future non-special lemma.
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict
from itertools import product

import cphi_bridge_exact_scan as scan
from cup2_theorem import build_system


def explicit_phi_data(n: int):
    ms, fs = build_system(n)
    good = scan.explicit_good_cycle_configs(n)
    bad = [c for c in product(*(range(m) for m in ms)) if c not in good]
    bad_set = set(bad)

    def tp(c):
        return (scan.exp2_count(c, n), scan.int_21(c, n), scan.exp2_weight(c, n))

    fc_cache = {c: scan.fc(c, n) for c in bad}
    tp_cache = {c: tp(c) for c in bad}
    tp_fwd = defaultdict(list)
    for c in bad:
        for i in range(n):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out == S:
                continue
            d = list(c)
            d[i] = out
            d = tuple(d)
            if d in bad_set and tp_cache.get(d) == tp_cache[c]:
                tp_fwd[c].append((d, scan.fc(d, n) - fc_cache[c]))

    g = {c: 0 for c in bad}
    for _ in range(2 * n + 10):
        changed = False
        for c in bad:
            best = g[c]
            for d, dfc in tp_fwd[c]:
                cand = dfc + g[d]
                if cand > best:
                    best = cand
            if best != g[c]:
                g[c] = best
                changed = True
        if not changed:
            break

    phi = {c: fc_cache[c] + g[c] for c in bad}
    return bad, bad_set, tp_cache, fc_cache, phi, fs


def profile_n(n: int):
    bad, bad_set, tp_cache, fc_cache, phi, fs = explicit_phi_data(n)
    family = []

    for c in bad:
        if scan.encode6(scan.boundary6(c, n)) != 239:
            continue
        i = n - 3
        L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
        out = fs[i](L, S, R)
        if out != 1:
            continue
        d = list(c)
        d[i] = out
        d = tuple(d)
        if scan.encode6(scan.boundary6(d, n)) != 245:
            continue

        family.append({
            "src": c,
            "dst": d,
            "dst_bad": d in bad_set,
            "tp_pres": tp_cache.get(d) == tp_cache[c] if d in bad_set else False,
            "fc_drop": scan.fc(d, n) - fc_cache[c],
            "phi_src": phi.get(c),
            "phi_dst": phi.get(d),
            "delta_src": phi.get(c) - fc_cache[c],
            "delta_dst": (phi.get(d) - scan.fc(d, n)) if d in bad_set else None,
            "local_triple": (L, S, R),
            "prefix": c[3:n-3],
        })

    bad_tp_family = [x for x in family if x["dst_bad"] and x["tp_pres"]]

    print(f"\n=== n={n} ===")
    print(f"239->245 candidates total: {len(family)}")
    print(f"239->245 bad TP-preserving: {len(bad_tp_family)}")
    print(f"status counts: {Counter((x['dst_bad'], x['tp_pres']) for x in family)}")
    print(f"local triples: {Counter(x['local_triple'] for x in family)}")
    print(f"fc drops: {Counter(x['fc_drop'] for x in family)}")
    print(f"(delta_src, delta_dst, phi_dst-phi_src): "
          f"{Counter((x['delta_src'], x['delta_dst'], x['phi_dst'] - x['phi_src']) for x in bad_tp_family)}")

    ok = True
    for x in bad_tp_family:
        first = next((v for v in x["prefix"] if v != 1), None)
        if not ((first == 0 and x["delta_src"] == 0) or (first == 2 and x["delta_src"] == 1)):
            ok = False
            print("counterexample to first-non1 rule:")
            print(x)
            break
    print(f"first non-1 rule holds: {ok}")


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9, 10, 11, 12]
    for n in ns:
        profile_n(n)


if __name__ == "__main__":
    main()
