#!/usr/bin/env python3
"""What's the universal 2-value rule per q?

At n=7, 672/672 q-records have exactly 2 anchor v-values, all ∈ V_q,
all fire-input and fire-output. 96.7% are {min(V_q), max(V_q)}, 22
exceptions. Focus on exceptions to find the true universal rule.

Candidate rules for the 2 anchor values at q:
  R1. {min(V_q), max(V_q)} — BROKEN (3.3% exceptions)
  R2. Plateau values: {v ∈ V_q : q holds v for a run ≥ something}
  R3. Ring-firing extremes: from the firing value-sequence at q
      (c_{i_0}[q] → c_{i_1}[q] → ...), anchors are the 2 "turning points"
  R4. Values v such that EXISTS step i: q fires AND c_i[q] = v AND c_{i+1}[q] = v'
      with some pairing constraint
  R5. For |V_q| = 2: {0, 1} trivially. For |V_q| ≥ 3: some derived pair.
  R6. The 2 values v such that c[q] = v occurs at a "boundary" step
      (where some neighbor processor is at an extreme of its V)

Dump all 22 exceptions at n=7 + all 150 |V_q|≥3 records for detailed pattern.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
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


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
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
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
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
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def compute_peel(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in range(ms[q]):
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
    adj = defaultdict(list)
    for c in N1:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in N1:
                    adj[c].append(nc)
    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove: break
        cur -= to_remove
    return cur


def q_firing_data(cycle, movers, q, n):
    """For position q, return list of (step_i, c_i[q], c_{i+1}[q]) at firing steps."""
    L = len(movers)
    fires = []
    for i in range(L):
        if movers[i] == q:
            fires.append((i, cycle[i][q], cycle[(i + 1) % L][q]))
    return fires


def q_run_lengths(cycle, q, n):
    """Compute run lengths at q: for each value v ∈ V_q, average run length."""
    L = len(cycle)
    runs_by_val = defaultdict(list)
    i = 0
    while i < L:
        v = cycle[i][q]
        j = i
        while j < L and cycle[j][q] == v:
            j += 1
        runs_by_val[v].append(j - i)
        i = j
    # Handle wrap: if cycle[0][q] == cycle[L-1][q], merge last run with first
    return runs_by_val


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    peel = compute_peel(ms, n, cycle, movers, det)
    if not peel: return None

    # Anchors per (q, v)
    qv_icount = defaultdict(int)
    for c_s in peel:
        for i, c in enumerate(cycle):
            diffs = [k for k in range(n) if c[k] != c_s[k]]
            if len(diffs) == 1:
                q = diffs[0]; v = c_s[q]
                qv_icount[(q, v)] += 1

    per_q = {}
    for q in range(n):
        v_anchors = sorted(v for (qp, v) in qv_icount if qp == q)
        if len(v_anchors) != 2: continue
        Vq = sorted(V[q])
        if len(Vq) < 3: continue  # Focus on nontrivial case
        fires = q_firing_data(cycle, movers, q, n)
        fire_ins = [f[1] for f in fires]
        fire_outs = [f[2] for f in fires]
        runs = q_run_lengths(cycle, q, n)
        per_q[q] = {
            'V_q': Vq,
            'anchors': v_anchors,
            'fires': fires,
            'fire_ins_seq': fire_ins,
            'fire_outs_seq': fire_outs,
            'runs': {v: sorted(runs[v]) for v in Vq},
            'total_runs': {v: sum(runs[v]) for v in Vq},
            'num_runs': {v: len(runs[v]) for v in Vq},
            'is_minmax': set(v_anchors) == {Vq[0], Vq[-1]},
        }
    return per_q


def main():
    print("=" * 72, flush=True)
    print("Finding universal 2-value rule at q (|V_q|≥3)", flush=True)
    print("=" * 72, flush=True)
    q_records = []
    exceptions = []
    tb = 4.0; max_cycles = 8; L_max = 17
    n = 7
    Mn = m_n_sharp(n)
    multisets = enumerate_multisets(n, Mn)
    sampled = multisets[::40]
    print(f"n=7  {len(sampled)} multisets", flush=True)
    t0 = time.time()
    for idx, ms in enumerate(sampled):
        cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n + 2: continue
            per_q = analyze(ms, n, cycle, movers, det)
            if per_q is None: continue
            for q, data in per_q.items():
                q_records.append((ms, cycle, movers, q, data))
                if not data['is_minmax']:
                    exceptions.append((ms, cycle, movers, q, data))
        if (idx + 1) % max(1, len(sampled) // 5) == 0 or idx == len(sampled) - 1:
            print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  q_recs={len(q_records)}", flush=True)

    print(f"\n{'='*72}\n|V_q|≥3 q-records: {len(q_records)}\n{'='*72}")
    mm_cnt = sum(1 for r in q_records if r[4]['is_minmax'])
    print(f"is {{min, max}}(V_q): {mm_cnt}/{len(q_records)}")
    print(f"exceptions: {len(exceptions)}")

    print(f"\n{'='*72}\nALL EXCEPTIONS (first 30)\n{'='*72}")
    for (ms, cycle, movers, q, d) in exceptions[:30]:
        L = len(movers)
        print(f"\nms={ms} L={L} q={q}")
        print(f"  V_q={d['V_q']}, anchors={d['anchors']}  (is_minmax={d['is_minmax']})")
        print(f"  fires: {d['fires']}")
        print(f"  total-time at each v: {d['total_runs']}")
        print(f"  #runs at each v: {d['num_runs']}")
        print(f"  run lengths: {d['runs']}")
        # Test hypotheses
        # R2: plateau values (longest total time)
        totals = d['total_runs']
        sorted_by_total = sorted(totals.items(), key=lambda kv: -kv[1])
        top2_total = {kv[0] for kv in sorted_by_total[:2]}
        print(f"  top-2 by total-time: {top2_total}  match anchors: {set(d['anchors']) == top2_total}")
        # R_fire: top-2 most frequent fire-input value
        fi_c = Counter(d['fire_ins_seq'])
        top2_fi = {kv[0] for kv in fi_c.most_common(2)}
        print(f"  top-2 fire-in freq: {top2_fi}  match anchors: {set(d['anchors']) == top2_fi}")

    # For ALL records (incl. min-max), check hypotheses aggregate
    print(f"\n{'='*72}\nHypothesis tests on ALL |V_q|≥3 records\n{'='*72}")
    r_matches = defaultdict(int)
    for (ms, cycle, movers, q, d) in q_records:
        anchor_set = set(d['anchors'])
        Vq = d['V_q']
        # R1: {min, max}
        if anchor_set == {Vq[0], Vq[-1]}:
            r_matches['R1_minmax'] += 1
        # R2: top-2 by total time
        totals = d['total_runs']
        sorted_by_total = sorted(totals.items(), key=lambda kv: -kv[1])
        top2 = {kv[0] for kv in sorted_by_total[:2]}
        if anchor_set == top2:
            r_matches['R2_top2_total'] += 1
        # R3: fewest-time (opposite)
        sorted_by_total_r = sorted(totals.items(), key=lambda kv: kv[1])
        bot2 = {kv[0] for kv in sorted_by_total_r[:2]}
        if anchor_set == bot2:
            r_matches['R3_bot2_total'] += 1
        # R4: exactly those v with #runs >= median
        runs_per_v = sorted(d['num_runs'].items(), key=lambda kv: -kv[1])
        top2_runs = {kv[0] for kv in runs_per_v[:2]}
        if anchor_set == top2_runs:
            r_matches['R4_top2_runs'] += 1
        # R5: fire-input most frequent
        fi_c = Counter(d['fire_ins_seq'])
        top2_fi = {kv[0] for kv in fi_c.most_common(2)}
        if anchor_set == top2_fi:
            r_matches['R5_top2_fire_in'] += 1
        # R6: v with max single run
        max_run = {v: max(d['runs'][v]) if d['runs'][v] else 0 for v in Vq}
        sr = sorted(max_run.items(), key=lambda kv: -kv[1])
        top2_mr = {kv[0] for kv in sr[:2]}
        if anchor_set == top2_mr:
            r_matches['R6_top2_maxrun'] += 1
    print(f"Total records: {len(q_records)}")
    for k, v in r_matches.items():
        print(f"  {k}: {v}/{len(q_records)} ({100*v/len(q_records):.1f}%)")


if __name__ == "__main__":
    main()
