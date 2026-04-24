#!/usr/bin/env python3
"""Which 2 v values at each q produce peel anchors?

At n=7, per q we see EXACTLY 2 v-values in V_q giving anchors.
Hypotheses to test:
  H_A: v ∈ {min(V_q), max(V_q)}
  H_B: v ∈ {first-fire-value, last-fire-value of q in cycle}
  H_C: v is NOT a transition-input value (i.e., v ∉ {c_i[q] : q fires at step i})
  H_D: v IS a transition-input value
  H_E: the 2 values are the two "plateau" values — values held for > 1 step
  H_F: Complement of firing-target values: v ∉ {c_{i+1}[q] : q fires at step i}

Also: do the 2 anchor v's per q differ from c_i[q] consistently?

For each record, produce a summary for each q.
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


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    peel = compute_peel(ms, n, cycle, movers, det)
    if not peel: return None

    # fire-input, fire-output values per q
    fire_inputs = defaultdict(list)   # q -> list of c_i[q] when q fires at step i
    fire_outputs = defaultdict(list)  # q -> list of c_{i+1}[q] when q fires at step i
    for i in range(L):
        q = movers[i]
        fire_inputs[q].append(cycle[i][q])
        fire_outputs[q].append(cycle[(i + 1) % L][q])

    # peel anchors
    qv_icount = defaultdict(int)
    for c_s in peel:
        for i, c in enumerate(cycle):
            diffs = [k for k in range(n) if c[k] != c_s[k]]
            if len(diffs) == 1:
                q = diffs[0]; v = c_s[q]
                qv_icount[(q, v)] += 1

    # Per-q: the anchor v set and tests
    per_q_tests = {}
    for q in range(n):
        v_anchors = set(v for (qp, v) in qv_icount if qp == q)
        if len(v_anchors) != 2: continue
        fi = set(fire_inputs[q])    # values q has when firing
        fo = set(fire_outputs[q])   # values q transitions to
        Vq = V[q]
        # Classify each v_a
        classes = {}
        for v_a in v_anchors:
            classes[v_a] = {
                'in_V': v_a in Vq,
                'in_fire_input': v_a in fi,
                'in_fire_output': v_a in fo,
                'is_min_Vq': v_a == min(Vq),
                'is_max_Vq': v_a == max(Vq),
            }
        per_q_tests[q] = {
            'v_anchors': sorted(v_anchors),
            'V_q': sorted(Vq),
            'fire_inputs': sorted(fi),
            'fire_outputs': sorted(fo),
            'classes': classes,
            # Summary flags
            'anchors_eq_min_max': v_anchors == {min(Vq), max(Vq)},
            'anchors_both_fire_input': all(v in fi for v in v_anchors),
            'anchors_none_fire_input': all(v not in fi for v in v_anchors),
            'anchors_both_fire_output': all(v in fo for v in v_anchors),
            'anchors_both_Vq': v_anchors <= Vq,
            # Test: v ∉ fire_output ⇔ v is "input-only" for q
            'anchors_input_only': all(v in fi and v not in fo for v in v_anchors),
            # Test: v ∈ fire_output, not fire_input
            'anchors_output_only': all(v in fo and v not in fi for v in v_anchors),
        }
    return per_q_tests


def main():
    print("=" * 72, flush=True)
    print("Which 2 v values anchor at each q?", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (7, 40, 8, 4.0, 17),
    ]
    all_q_records = []
    one_example = None
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        rec_count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2: continue
                per_q = analyze(ms, n, cycle, movers, det)
                if per_q is None: continue
                rec_count += 1
                if one_example is None:
                    one_example = (ms, cycle, movers, per_q)
                for q, tests in per_q.items():
                    all_q_records.append((n, q, tests))
            if (idx + 1) % max(1, len(sampled) // 6) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={rec_count}", flush=True)

    print(f"\n{'='*72}\nPer-q tests (n=7)\n{'='*72}")
    total = len(all_q_records)
    print(f"Total q-records: {total}")
    flags = ['anchors_eq_min_max', 'anchors_both_fire_input', 'anchors_none_fire_input',
             'anchors_both_fire_output', 'anchors_both_Vq', 'anchors_input_only', 'anchors_output_only']
    for f in flags:
        cnt = sum(1 for (_, _, t) in all_q_records if t.get(f))
        print(f"  {f}: {cnt}/{total} ({100*cnt/total:.1f}%)")

    # m_q=2 breakdown: with m_q=2 and |V_q|=2, the 2 anchor values are forced to be V_q; test anchors_eq_Vq
    m2_cnt = sum(1 for (_, _, t) in all_q_records if len(t['V_q']) == 2)
    print(f"\n  |V_q|=2 records: {m2_cnt}")
    m2_anch_Vq = sum(1 for (_, _, t) in all_q_records if len(t['V_q']) == 2 and set(t['v_anchors']) == set(t['V_q']))
    print(f"    anchors = V_q: {m2_anch_Vq}/{m2_cnt}")

    print(f"\n{'='*72}\nOne example\n{'='*72}")
    if one_example is not None:
        ms, cycle, movers, per_q = one_example
        print(f"ms={ms}, L={len(movers)}")
        print(f"cycle[0..4]: {cycle[:5]}...")
        print(f"movers: {movers}")
        for q in sorted(per_q.keys()):
            t = per_q[q]
            print(f"  q={q}: V_q={t['V_q']}, anchors={t['v_anchors']}, fire_in={t['fire_inputs']}, fire_out={t['fire_outputs']}")


if __name__ == "__main__":
    main()
