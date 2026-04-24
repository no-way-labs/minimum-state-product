#!/usr/bin/env python3
"""Shadow + Entry-Conflict two-mechanism probe.

For each benchmark multiset, enumerate candidate full-coverage good cycles
and test each one against two kill mechanisms:

  SHADOW : determined bad graph contains a closed walk reachable from a
           non-good start via forced moves (find_shadow).
  EC     : some processor sees the same (L,S,R) context at both a mover
           step and a non-mover step in the cycle's own word (has_any_ec).

Desired separator: every tail cycle is killed by at least one mechanism,
and at least one witness cycle survives both. A weaker but still useful
separator: tails uniformly show the mechanism that matches their type
(sweep → shadow, non-sweep → EC), while witnesses have a cycle of some
type for which neither mechanism fires.

Functions are inlined from:
  enumerate_cycles / build_forced_graph : cic_lifting_proof2.py
  classify_cycle_type                    : cic_cycle_types.py
  find_shadow                            : binscc_mixed_escape_mnu.py
  find_ec_at_proc / has_any_ec           : ra16_shift_pattern.py
  shadow_perm                            : hk_last_shadow_pattern_check.py
"""

from itertools import product as iproduct
from collections import defaultdict
import time


BENCHMARKS = [
    ("n5_tail",    5, (2, 2, 2, 3, 3),       "tail"),
    ("n6_tail",    6, (2, 2, 2, 3, 3, 3),    "tail"),
    ("n5_witness", 5, (2, 2, 2, 3, 4),       "witness"),
    ("n6_witness", 6, (2, 2, 2, 4, 3, 3),    "witness"),
    ("n7_witness", 7, (3, 2, 2, 2, 3, 4, 3), "witness"),
]


# ----------------------------------------------------------------------
# enumerate_cycles — copied from cic_lifting_proof2.py to avoid side
# effects on import.
# ----------------------------------------------------------------------
def enumerate_cycles(ms, n, max_cycles=200, max_time=60.0, max_path_len=None):
    if max_path_len is None:
        max_path_len = 10 * n
    t0 = time.time()
    P = 1
    for m in ms:
        P *= m
    if P > 500:
        return []
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    for start_idx in range(min(len(all_configs), P)):
        if time.time() - t0 > max_time:
            break
        start = all_configs[start_idx]
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 500000:
            if time.time() - t0 > max_time:
                break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for new_val in range(ms[p]):
                    if new_val == config[p]:
                        continue
                    if movers:
                        last = movers[-1]
                        diff = min(abs(p - last), n - abs(p - last))
                        if diff > 1:
                            continue
                    new_det = dict(det)
                    consistent = True
                    L = config[(p - 1) % n]
                    S = config[p]
                    R = config[(p + 1) % n]
                    key_m = (p, L, S, R)
                    if key_m in new_det:
                        if new_det[key_m] != new_val:
                            consistent = False
                    else:
                        new_det[key_m] = new_val
                    if consistent:
                        for i in range(n):
                            if i == p:
                                continue
                            Li = config[(i - 1) % n]
                            Si = config[i]
                            Ri = config[(i + 1) % n]
                            key_i = (i, Li, Si, Ri)
                            if key_i in new_det:
                                if new_det[key_i] != Si:
                                    consistent = False
                                    break
                            else:
                                new_det[key_i] = Si
                    if not consistent:
                        continue
                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)
                    if new_config == start and len(path) >= n:
                        me_ok = True
                        for idx in range(len(path)):
                            c = path[idx]
                            priv = []
                            for i in range(n):
                                Li = c[(i - 1) % n]
                                Si = c[i]
                                Ri = c[(i + 1) % n]
                                ki = (i, Li, Si, Ri)
                                if ki in new_det and new_det[ki] != Si:
                                    priv.append(i)
                            if len(priv) != 1:
                                me_ok = False
                                break
                        if me_ok:
                            cycle_tup = tuple(path)
                            if cycle_tup not in [tuple(c) for c, _, _ in cycles]:
                                cycles.append((path, movers + [p], new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue
                    if new_config not in set(path) and len(path) < max_path_len:
                        stack.append((new_config, path + [new_config],
                                      new_det, movers + [p]))
    return cycles


# ----------------------------------------------------------------------
# classify_cycle_type — from cic_cycle_types.py
# ----------------------------------------------------------------------
def classify_cycle_type(movers, n):
    if not movers or -1 in movers:
        return "unknown"
    sweep = list(range(n))
    L = len(movers)
    if L % n == 0 and movers == sweep * (L // n):
        return "sweep"
    rev_sweep = list(range(n - 1, -1, -1))
    if L % n == 0 and movers == rev_sweep * (L // n):
        return "rev_sweep"
    bounce = list(range(n)) + list(range(n - 2, 0, -1))
    for r in range(1, 10):
        prefix = (bounce * r)[:L]
        if len(prefix) == L and movers == prefix:
            return "bounce"
    rev_bounce = list(range(n - 1, -1, -1)) + list(range(1, n - 1))
    for r in range(1, 10):
        prefix = (rev_bounce * r)[:L]
        if len(prefix) == L and movers == prefix:
            return "rev_bounce"
    has_self = any(movers[i] == movers[(i + 1) % L] for i in range(L))
    dirs = []
    for i in range(L):
        d = (movers[(i + 1) % L] - movers[i]) % n
        if d <= n // 2:
            dirs.append(d)
        else:
            dirs.append(d - n)
    dir_changes = sum(1 for i in range(len(dirs))
                      if dirs[i] != dirs[(i + 1) % len(dirs)])
    if has_self:
        return f"walk_selfloop_L{L}_dc{dir_changes}"
    return f"walk_L{L}_dc{dir_changes}"


def is_sweep_type(ctype):
    return ctype in ("sweep", "rev_sweep")


# ----------------------------------------------------------------------
# find_shadow — from binscc_mixed_escape_mnu.py
# ----------------------------------------------------------------------
def find_shadow(cycle, det, ms, n):
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    for start in non_good:
        config = start
        visited = {}
        path = []
        for step in range(500):
            if config in good_set:
                break
            if config in visited:
                cycle_start = visited[config]
                return path[cycle_start:]
            visited[config] = len(path)
            path.append(config)
            forced = []
            for j in range(n):
                Lj = config[(j - 1) % n]
                Sj = config[j]
                Rj = config[(j + 1) % n]
                key = (j, Lj, Sj, Rj)
                if key in det and det[key] != Sj:
                    forced.append((j, det[key]))
            if not forced:
                break
            moved = False
            for proc, new_val in forced:
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config not in good_set:
                    config = new_config
                    moved = True
                    break
            if not moved:
                break
    return None


# ----------------------------------------------------------------------
# Entry conflict — from ra16_shift_pattern.py
# ----------------------------------------------------------------------
def find_ec_at_proc(word, configs, n, j):
    L = len(word)
    mt = set()
    nmt = set()
    for t in range(L):
        c = configs[t]
        triple = (c[(j - 1) % n], c[j], c[(j + 1) % n])
        if word[t] == j:
            mt.add(triple)
        else:
            nmt.add(triple)
    return mt & nmt


def ec_conflicts(word, configs, ms, n):
    """Return list of (proc, set_of_conflicting_triples) for procs with EC."""
    out = []
    for j in range(n):
        hits = find_ec_at_proc(word, configs, n, j)
        if hits:
            out.append((j, hits))
    return out


# ----------------------------------------------------------------------
# Probe driver
# ----------------------------------------------------------------------
def run_benchmark(label, n, ms, role):
    print(f"\n===== {label}  n={n}  ms={ms}  role={role} =====")
    t0 = time.time()
    cycles = enumerate_cycles(ms, n, max_cycles=40, max_time=60.0)
    elapsed = time.time() - t0
    print(f"enumerate_cycles: {len(cycles)} cycles in {elapsed:.1f}s")
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    print(f"full-coverage cycles: {len(full)}")
    if not full:
        return {"label": label, "role": role, "rows": []}

    rows = []
    for idx, (cycle, movers, det) in enumerate(full):
        ctype = classify_cycle_type(movers, n)
        shadow = find_shadow(cycle, det, ms, n)
        ec = ec_conflicts(movers, cycle, ms, n)
        row = {
            "idx": idx,
            "L": len(cycle),
            "type": ctype,
            "is_sweep": is_sweep_type(ctype),
            "has_shadow": shadow is not None,
            "shadow_len": len(shadow) if shadow is not None else None,
            "has_ec": bool(ec),
            "ec_procs": [p for p, _ in ec],
            "killed_by_shadow": shadow is not None,
            "killed_by_ec": bool(ec),
            "killed": (shadow is not None) or bool(ec),
        }
        rows.append(row)

    # Classification breakdown.
    type_counter = defaultdict(int)
    for r in rows:
        type_counter[r["type"]] += 1
    print(f"  cycle types: {dict(type_counter)}")

    n_sweep = sum(1 for r in rows if r["is_sweep"])
    n_nonsweep = len(rows) - n_sweep
    print(f"  sweep: {n_sweep}  non-sweep: {n_nonsweep}")

    n_shadow = sum(1 for r in rows if r["has_shadow"])
    n_ec = sum(1 for r in rows if r["has_ec"])
    n_killed = sum(1 for r in rows if r["killed"])
    n_survive = len(rows) - n_killed
    print(f"  has_shadow: {n_shadow}/{len(rows)}")
    print(f"  has_ec    : {n_ec}/{len(rows)}")
    print(f"  killed (shadow OR ec): {n_killed}/{len(rows)}")
    print(f"  SURVIVORS (neither): {n_survive}/{len(rows)}")

    # Sub-breakdown: sweeps killed by shadow? non-sweeps killed by EC?
    sweep_rows = [r for r in rows if r["is_sweep"]]
    nonsweep_rows = [r for r in rows if not r["is_sweep"]]
    sw_shadow = sum(1 for r in sweep_rows if r["has_shadow"])
    ns_ec = sum(1 for r in nonsweep_rows if r["has_ec"])
    ns_shadow = sum(1 for r in nonsweep_rows if r["has_shadow"])
    sw_ec = sum(1 for r in sweep_rows if r["has_ec"])
    print(f"  sweep  ∩ shadow : {sw_shadow}/{len(sweep_rows)}")
    print(f"  sweep  ∩ ec     : {sw_ec}/{len(sweep_rows)}")
    print(f"  nonsweep ∩ shadow: {ns_shadow}/{len(nonsweep_rows)}")
    print(f"  nonsweep ∩ ec    : {ns_ec}/{len(nonsweep_rows)}")

    # Print the survivors in detail if any.
    survivors = [r for r in rows if not r["killed"]]
    if survivors:
        print(f"  SURVIVOR DETAILS:")
        for r in survivors:
            print(f"    idx={r['idx']} L={r['L']} type={r['type']} "
                  f"shadow={r['has_shadow']} ec_procs={r['ec_procs']}")

    return {"label": label, "role": role, "rows": rows}


def main():
    results = []
    for (label, n, ms, role) in BENCHMARKS:
        results.append(run_benchmark(label, n, ms, role))

    print("\n\n========== CROSS-BENCHMARK SUMMARY ==========")
    print(f"{'label':<14}{'role':<10}{'cycs':<6}{'sweeps':<8}"
          f"{'shadow':<9}{'ec':<6}{'killed':<9}{'survive':<9}")
    for res in results:
        rows = res["rows"]
        if not rows:
            print(f"{res['label']:<14}{res['role']:<10}0")
            continue
        n_sw = sum(1 for r in rows if r["is_sweep"])
        n_sh = sum(1 for r in rows if r["has_shadow"])
        n_ec = sum(1 for r in rows if r["has_ec"])
        n_kill = sum(1 for r in rows if r["killed"])
        n_surv = len(rows) - n_kill
        print(f"{res['label']:<14}{res['role']:<10}{len(rows):<6}"
              f"{n_sw:<8}{n_sh:<9}{n_ec:<6}{n_kill:<9}{n_surv:<9}")

    print("\nTwo-mechanism separator test:")
    print("  Want: every TAIL cycle killed by shadow OR ec,")
    print("        and at least one WITNESS cycle survives both.")
    for res in results:
        rows = res["rows"]
        if not rows:
            continue
        survivors = sum(1 for r in rows if not r["killed"])
        status = "OK" if (
            (res["role"] == "tail" and survivors == 0) or
            (res["role"] == "witness" and survivors > 0)
        ) else "FAIL"
        print(f"  {res['label']:<14} {res['role']:<10} survivors={survivors}  {status}")


if __name__ == "__main__":
    main()
