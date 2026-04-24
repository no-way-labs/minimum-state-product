#!/usr/bin/env python3
"""E17 — Local characterization of the unique non-trivial SCC on T_N1.

Board context (primer §7.8, sk_campaign_state_2026-04-19.md)
    E16 established: every record has exactly ONE non-trivial SCC `BIG`
    of size ≥ 18 in the forced-NG subgraph on T_N1. The peel fixpoint
    equals BIG in every record.

    R4 (peel-direct Lean) is stuck on proving peel ≠ ∅ without walk
    construction (E14/E15, 26% residue). If we can identify BIG by a
    LOCAL, cycle-structure-independent property P(c) — computable from
    cycle data + config c alone — we get a Lean-portable target:

        "prove { c ∈ T_N1 : P(c) } is nonempty and forced-closed."

    ~200 lines in Lean. Bypasses walk construction.

    This probe enumerates candidate local features and tests whether any
    single feature (or small conjunction) characterizes BIG-membership
    uniformly across all records.

Features probed (LOCAL — 1-hop or structural at config c alone)
    out_deg                 — # forced-NG successors of c in T_N1
    in_deg                  — # predecessors of c in T_N1 via forced-NG
    num_anchors             — # cycle-Hamming-1 anchors (k, q, v) of c
    anchor_qv_at_extremes   — every anchor's v ∈ {min(V_q), max(V_q)}?
    anchor_qv_at_dom_pair   — every anchor's v in top-2 residence values
                              of V_q (dom_pair from tube findings memo)
    is_sink                 — out_deg == 0
    has_sink_successor      — ≥ 1 successor is a sink
    all_successors_are_sinks — every successor is a sink

Characterization tests (per record)
    For each feature P:
      rate_P_in_BIG          = |{c : P(c) ∧ c ∈ BIG}| / |{c : P(c)}|
      rate_notP_not_in_BIG   = |{c : ¬P(c) ∧ c ∉ BIG}| / |{c : ¬P(c)}|
      accuracy               = (TP + TN) / |T_N1|     (assuming P ≡ BIG)
    A feature PERFECTLY characterizes BIG iff accuracy = 1.0.

    Also try pairwise conjunctions (P1 ∧ P2) and negation pairs.

Verdict
    GREEN  — single feature (or small fixed conjunction) matches BIG
             100% uniformly across all records and all n.
    YELLOW — best achieves ≥ 95% but not 100%.
    RED    — no local feature > 90%. SCC is globally defined;
             R4 is dead.

Infrastructure reused from probe_sk_scc_structure_2026-04-20.py:
    m_n, enumerate_multisets, enumerate_all_cycles, tarjan_scc.
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, combinations


# ----- thresholds --------------------------------------------------------

def m_n(n: int) -> int:
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


# ----- multiset enumeration ----------------------------------------------

def enumerate_multisets(n: int, max_product: int):
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


# ----- cycle enumeration -------------------------------------------------

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


# ----- Tarjan SCC (iterative) --------------------------------------------

def tarjan_scc(nodes, adj):
    index_of = {}
    lowlink = {}
    on_stack = {}
    stack = []
    sccs = []
    idx_counter = [0]
    node_set = set(nodes)

    def strongconnect(v_start):
        work = [(v_start, iter(adj.get(v_start, ())))]
        index_of[v_start] = idx_counter[0]
        lowlink[v_start] = idx_counter[0]
        idx_counter[0] += 1
        stack.append(v_start)
        on_stack[v_start] = True

        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in node_set:
                    continue
                if w not in index_of:
                    index_of[w] = idx_counter[0]
                    lowlink[w] = idx_counter[0]
                    idx_counter[0] += 1
                    stack.append(w)
                    on_stack[w] = True
                    work.append((w, iter(adj.get(w, ()))))
                    advanced = True
                    break
                elif on_stack.get(w, False):
                    if index_of[w] < lowlink[v]:
                        lowlink[v] = index_of[w]
            if advanced:
                continue
            work.pop()
            if lowlink[v] == index_of[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    comp.append(w)
                    if w == v:
                        break
                sccs.append(comp)
            if work:
                parent = work[-1][0]
                if lowlink[v] < lowlink[parent]:
                    lowlink[parent] = lowlink[v]

    for v in nodes:
        if v not in index_of:
            strongconnect(v)
    return sccs


# ----- analyze record: compute BIG, features, accuracy -------------------

# Features we test. Listed here to keep summary columns stable.
FEATURE_NAMES = [
    'out_deg_ge_1',
    'out_deg_ge_2',
    'in_deg_ge_1',
    'in_deg_ge_2',
    'num_anchors_ge_2',
    'num_anchors_ge_3',
    'anchor_qv_at_extremes',
    'anchor_qv_at_dom_pair',
    'is_not_sink',
    'has_nonsink_successor',
    'has_nonsink_predecessor',
]


def analyze_record(ms, n, cycle, movers, det):
    L = len(movers)
    V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n):
            V[q].add(c[q])
    V_list = [sorted(s) for s in V]
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Residence time per value per position (from cycle only)
    residence = [Counter() for _ in range(n)]
    for c in cycle:
        for q in range(n):
            residence[q][c[q]] += 1

    # dom_pair[q] = top-2 values by residence time at position q
    dom_pair = []
    for q in range(n):
        items = sorted(residence[q].items(), key=lambda kv: (-kv[1], kv[0]))
        dom_pair.append({v for v, _ in items[:2]})

    V_extremes = [{min(s), max(s)} for s in V_list]

    # Tube T = N_1(C) ∩ VC-NG
    # Also compute anchors for each c ∈ T: anchors[c] = list of (k, q, v)
    anchors_of = defaultdict(list)
    T = set()
    for k, c in enumerate(cycle):
        for q in range(n):
            for v in V_list[q]:
                if v == c[q]:
                    continue
                nc = list(c)
                nc[q] = v
                nc = tuple(nc)
                if nc not in cycle_set:
                    T.add(nc)
                    anchors_of[nc].append((k, q, v))

    # Forced-NG successor edges inside T
    adj_out = defaultdict(list)
    adj_in = defaultdict(list)
    seen_edges = set()
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c)
                nc[p] = val
                nc = tuple(nc)
                if nc in T and (c, nc) not in seen_edges:
                    seen_edges.add((c, nc))
                    adj_out[c].append(nc)
                    adj_in[nc].append(c)

    # SCCs
    nodes = list(T)
    sccs = tarjan_scc(nodes, adj_out)
    # Identify BIG: the unique non-trivial SCC (size ≥ 2)
    nontrivial = [s for s in sccs if len(s) >= 2]
    if len(nontrivial) == 0:
        return None  # degenerate: skip (E16 said this shouldn't happen)
    # E16 claim: unique non-trivial SCC. If more than one, we still pick
    # the largest as BIG but flag the record.
    nontrivial.sort(key=len, reverse=True)
    BIG_members = set(nontrivial[0])
    BIG_num = len(nontrivial)

    # Sinks in the whole tube T (for "has_sink_successor" etc.)
    sinks = {c for c in T if len(adj_out[c]) == 0}

    # --- Per-node local features ----------------------------------------
    in_BIG = {}
    features = {}

    for c in T:
        out_deg = len(adj_out[c])
        in_deg = len(adj_in[c])
        anchors = anchors_of[c]
        num_anchors = len(anchors)
        anchor_qv_at_extremes = (
            num_anchors >= 1 and
            all(v in V_extremes[q] for (_, q, v) in anchors))
        anchor_qv_at_dom_pair = (
            num_anchors >= 1 and
            all(v in dom_pair[q] for (_, q, v) in anchors))
        is_not_sink = out_deg > 0
        has_nonsink_successor = any(s not in sinks for s in adj_out[c])
        has_nonsink_predecessor = any(s not in sinks for s in adj_in[c])

        feats = {
            'out_deg_ge_1': out_deg >= 1,
            'out_deg_ge_2': out_deg >= 2,
            'in_deg_ge_1': in_deg >= 1,
            'in_deg_ge_2': in_deg >= 2,
            'num_anchors_ge_2': num_anchors >= 2,
            'num_anchors_ge_3': num_anchors >= 3,
            'anchor_qv_at_extremes': anchor_qv_at_extremes,
            'anchor_qv_at_dom_pair': anchor_qv_at_dom_pair,
            'is_not_sink': is_not_sink,
            'has_nonsink_successor': has_nonsink_successor,
            'has_nonsink_predecessor': has_nonsink_predecessor,
        }
        features[c] = feats
        in_BIG[c] = c in BIG_members

    # --- Per-feature accuracy ------------------------------------------
    feature_stats = {}
    for fname in FEATURE_NAMES:
        TP = sum(1 for c in T if features[c][fname] and in_BIG[c])
        FP = sum(1 for c in T if features[c][fname] and not in_BIG[c])
        FN = sum(1 for c in T if not features[c][fname] and in_BIG[c])
        TN = sum(1 for c in T if not features[c][fname] and not in_BIG[c])
        total = len(T)
        accuracy = (TP + TN) / total if total else 0
        # "P -> BIG" rate: of those with P, fraction in BIG
        p_pos = TP + FP
        p_to_big = TP / p_pos if p_pos else None
        # "¬P -> ¬BIG" rate: of those without P, fraction not in BIG
        p_neg = TN + FN
        notp_to_notbig = TN / p_neg if p_neg else None
        feature_stats[fname] = {
            'TP': TP, 'FP': FP, 'FN': FN, 'TN': TN,
            'accuracy': accuracy,
            'p_to_big': p_to_big,
            'notp_to_notbig': notp_to_notbig,
            'perfect': (FP == 0 and FN == 0),
        }

    # --- Pairwise conjunctions (P1 ∧ P2) and (P1 ∧ ¬P2) ---------------
    # Keep it manageable: all unordered pairs of FEATURE_NAMES, both
    # AND and (A ∧ ¬B). Stored compactly as name strings.
    pair_stats = {}
    for a, b in combinations(FEATURE_NAMES, 2):
        for variant, pred in (
            ('AND', lambda fa, fb: fa and fb),
            ('A_AND_NOT_B', lambda fa, fb: fa and not fb),
            ('NOT_A_AND_B', lambda fa, fb: (not fa) and fb),
            ('OR', lambda fa, fb: fa or fb),
        ):
            TP = FP = FN = TN = 0
            for c in T:
                p = pred(features[c][a], features[c][b])
                big = in_BIG[c]
                if p and big:
                    TP += 1
                elif p and not big:
                    FP += 1
                elif (not p) and big:
                    FN += 1
                else:
                    TN += 1
            total = len(T)
            acc = (TP + TN) / total if total else 0
            pair_stats[(a, b, variant)] = {
                'TP': TP, 'FP': FP, 'FN': FN, 'TN': TN,
                'accuracy': acc,
                'perfect': (FP == 0 and FN == 0),
            }

    # pick best single & best pair
    best_single = max(feature_stats.items(),
                      key=lambda kv: kv[1]['accuracy'])
    best_pair = max(pair_stats.items(), key=lambda kv: kv[1]['accuracy'])

    return {
        'n': n,
        'ms': list(ms),
        'L': L,
        'T': len(T),
        'BIG_size': len(BIG_members),
        'BIG_num_nontrivial_sccs': BIG_num,
        'num_sinks': len(sinks),
        'feature_stats': {
            k: {'accuracy': v['accuracy'], 'perfect': v['perfect'],
                'FP': v['FP'], 'FN': v['FN'],
                'p_to_big': v['p_to_big'],
                'notp_to_notbig': v['notp_to_notbig']}
            for k, v in feature_stats.items()
        },
        'best_single_feature': {
            'name': best_single[0],
            'accuracy': best_single[1]['accuracy'],
            'perfect': best_single[1]['perfect'],
            'FP': best_single[1]['FP'],
            'FN': best_single[1]['FN'],
        },
        'best_pair_feature': {
            'spec': f"{best_pair[0][0]} {best_pair[0][2]} {best_pair[0][1]}",
            'accuracy': best_pair[1]['accuracy'],
            'perfect': best_pair[1]['perfect'],
            'FP': best_pair[1]['FP'],
            'FN': best_pair[1]['FN'],
        },
        # keep full pair stats too (compact) for aggregation
        '_pair_stats': {
            f"{a}|{v}|{b}": {
                'accuracy': s['accuracy'],
                'perfect': s['perfect'],
                'FP': s['FP'], 'FN': s['FN'],
            }
            for (a, b, v), s in pair_stats.items()
        },
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("E17 probe: local characterization of non-trivial SCC on T_N1",
          flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1, 40, 2.0, 15),
        (6, 4, 20, 3.0, 17),
        (7, 40, 10, 3.0, 19),
        (8, 200, 5, 4.0, 21),
    ]
    records = []
    skipped = 0
    t_global = time.time()

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  M_n={Mn}  multisets={len(multisets)}  "
              f"sampled={len(sampled)} ===", flush=True)
        t0 = time.time()
        rec_before = len(records)
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                if len(movers) < 2 * n:
                    continue
                r = analyze_record(ms, n, cycle, movers, det)
                if r is None:
                    skipped += 1
                    continue
                records.append(r)
            if (idx + 1) % max(1, len(sampled) // 10) == 0 \
                    or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  t={time.time()-t0:.0f}s  "
                      f"records(+{len(records)-rec_before})  "
                      f"skipped={skipped}", flush=True)

    total = len(records)
    print(f"\n{'='*72}\nSummary ({total} records, "
          f"{time.time()-t_global:.0f}s, {skipped} skipped)\n{'='*72}")

    # --- per-feature aggregate: min accuracy across records, #perfect ----
    feat_min_acc = {f: 1.0 for f in FEATURE_NAMES}
    feat_num_perfect = {f: 0 for f in FEATURE_NAMES}
    feat_sum_acc = {f: 0.0 for f in FEATURE_NAMES}
    feat_records = {f: 0 for f in FEATURE_NAMES}

    for r in records:
        for f in FEATURE_NAMES:
            s = r['feature_stats'][f]
            acc = s['accuracy']
            if acc < feat_min_acc[f]:
                feat_min_acc[f] = acc
            if s['perfect']:
                feat_num_perfect[f] += 1
            feat_sum_acc[f] += acc
            feat_records[f] += 1

    print("\n  Per-feature (across all records, all n):")
    print(f"  {'feature':<28} {'min_acc':>8} {'mean_acc':>9} {'perfect':>12}")
    feat_rows = []
    for f in FEATURE_NAMES:
        n_rec = feat_records[f]
        mean_acc = feat_sum_acc[f] / n_rec if n_rec else 0
        print(f"  {f:<28} {feat_min_acc[f]:>8.3f} {mean_acc:>9.3f} "
              f"{feat_num_perfect[f]:>7}/{n_rec}")
        feat_rows.append({
            'feature': f,
            'min_acc': feat_min_acc[f],
            'mean_acc': mean_acc,
            'num_perfect': feat_num_perfect[f],
            'num_records': n_rec,
        })

    best_single_feat_by_min = max(feat_rows, key=lambda r: r['min_acc'])
    best_single_feat_by_mean = max(feat_rows, key=lambda r: r['mean_acc'])
    best_single_feat_by_perfect = max(feat_rows, key=lambda r: r['num_perfect'])

    print()
    print(f"  Best SINGLE feature by MIN acc:  "
          f"{best_single_feat_by_min['feature']} "
          f"(min={best_single_feat_by_min['min_acc']:.3f}, "
          f"mean={best_single_feat_by_min['mean_acc']:.3f}, "
          f"perfect={best_single_feat_by_min['num_perfect']}/"
          f"{best_single_feat_by_min['num_records']})")
    print(f"  Best SINGLE feature by MEAN acc: "
          f"{best_single_feat_by_mean['feature']} "
          f"(min={best_single_feat_by_mean['min_acc']:.3f}, "
          f"mean={best_single_feat_by_mean['mean_acc']:.3f})")
    print(f"  Best SINGLE feature by #PERFECT: "
          f"{best_single_feat_by_perfect['feature']} "
          f"(perfect={best_single_feat_by_perfect['num_perfect']}/"
          f"{best_single_feat_by_perfect['num_records']})")

    # --- per-pair aggregate ---------------------------------------------
    pair_min_acc = defaultdict(lambda: 1.0)
    pair_num_perfect = defaultdict(int)
    pair_sum_acc = defaultdict(float)
    pair_records = defaultdict(int)
    for r in records:
        for key, s in r['_pair_stats'].items():
            acc = s['accuracy']
            if acc < pair_min_acc[key]:
                pair_min_acc[key] = acc
            if s['perfect']:
                pair_num_perfect[key] += 1
            pair_sum_acc[key] += acc
            pair_records[key] += 1

    pair_rows = []
    for key in pair_records:
        n_rec = pair_records[key]
        mean_acc = pair_sum_acc[key] / n_rec if n_rec else 0
        pair_rows.append({
            'spec': key,
            'min_acc': pair_min_acc[key],
            'mean_acc': mean_acc,
            'num_perfect': pair_num_perfect[key],
            'num_records': n_rec,
        })

    best_pair_by_min = max(pair_rows, key=lambda r: r['min_acc'])
    best_pair_by_mean = max(pair_rows, key=lambda r: r['mean_acc'])
    best_pair_by_perfect = max(pair_rows, key=lambda r: r['num_perfect'])

    print()
    print(f"  Best PAIR by MIN acc:   {best_pair_by_min['spec']} "
          f"(min={best_pair_by_min['min_acc']:.3f}, "
          f"mean={best_pair_by_min['mean_acc']:.3f}, "
          f"perfect={best_pair_by_min['num_perfect']}/"
          f"{best_pair_by_min['num_records']})")
    print(f"  Best PAIR by MEAN acc:  {best_pair_by_mean['spec']} "
          f"(min={best_pair_by_mean['min_acc']:.3f}, "
          f"mean={best_pair_by_mean['mean_acc']:.3f})")
    print(f"  Best PAIR by #PERFECT:  {best_pair_by_perfect['spec']} "
          f"(perfect={best_pair_by_perfect['num_perfect']}/"
          f"{best_pair_by_perfect['num_records']})")

    # --- per-n breakdown for best single + best pair ---------------------
    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    print("\n  Per-n breakdown (best single = {}):".format(
        best_single_feat_by_min['feature']))
    for n in sorted(by_n):
        recs = by_n[n]
        accs = [r['feature_stats'][best_single_feat_by_min['feature']]['accuracy']
                for r in recs]
        perfects = sum(1 for r in recs
                       if r['feature_stats'][best_single_feat_by_min['feature']]['perfect'])
        print(f"    n={n}: records={len(recs)}  "
              f"acc min={min(accs):.3f} max={max(accs):.3f} "
              f"mean={sum(accs)/len(accs):.3f}  perfect={perfects}/{len(recs)}")

    print("\n  Per-n breakdown (best pair = {}):".format(
        best_pair_by_min['spec']))
    for n in sorted(by_n):
        recs = by_n[n]
        accs = [r['_pair_stats'][best_pair_by_min['spec']]['accuracy']
                for r in recs]
        perfects = sum(1 for r in recs
                       if r['_pair_stats'][best_pair_by_min['spec']]['perfect'])
        print(f"    n={n}: records={len(recs)}  "
              f"acc min={min(accs):.3f} max={max(accs):.3f} "
              f"mean={sum(accs)/len(accs):.3f}  perfect={perfects}/{len(recs)}")

    # --- verdict ---------------------------------------------------------
    print(f"\n{'='*72}")
    print("VERDICT")
    print(f"{'='*72}")

    best_min = max(best_single_feat_by_min['min_acc'],
                   best_pair_by_min['min_acc'])
    single_perfect_everywhere = (
        best_single_feat_by_min['num_perfect'] == total
        and best_single_feat_by_min['min_acc'] >= 0.9999)
    pair_perfect_everywhere = (
        best_pair_by_min['num_perfect'] == total
        and best_pair_by_min['min_acc'] >= 0.9999)

    if single_perfect_everywhere:
        verdict = "GREEN"
        msg = (f"Single feature `{best_single_feat_by_min['feature']}` "
               f"PERFECTLY characterizes BIG in all {total} records. "
               f"R4 is ALIVE: this feature is the Lean-portable target.")
    elif pair_perfect_everywhere:
        verdict = "GREEN"
        msg = (f"Feature conjunction `{best_pair_by_min['spec']}` "
               f"PERFECTLY characterizes BIG in all {total} records. "
               f"R4 is ALIVE via this conjunction.")
    elif best_min >= 0.95:
        verdict = "YELLOW"
        if best_single_feat_by_min['min_acc'] >= best_pair_by_min['min_acc']:
            msg = (f"Best single `{best_single_feat_by_min['feature']}` "
                   f"has min_acc={best_single_feat_by_min['min_acc']:.3f} "
                   f"(≥0.95 but not perfect). Residue to investigate.")
        else:
            msg = (f"Best pair `{best_pair_by_min['spec']}` has "
                   f"min_acc={best_pair_by_min['min_acc']:.3f} "
                   f"(≥0.95 but not perfect). Residue to investigate.")
    elif best_min >= 0.90:
        verdict = "YELLOW"
        msg = (f"Best local characterization achieves only "
               f"min_acc={best_min:.3f}. Borderline — R4 unclear.")
    else:
        verdict = "RED"
        msg = (f"No local feature exceeds min_acc={best_min:.3f} across all "
               f"records. BIG is globally defined; no local characterization "
               f"exists. R4 (peel-direct Lean route) is DEAD.")

    print(f"\n  FINAL VERDICT: {verdict}")
    print(f"  {msg}")
    print(f"{'='*72}")

    # --- dump JSON -------------------------------------------------------
    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(
        out_dir, 'e17_scc_local_char_2026-04-20.json')
    # Drop heavy _pair_stats dict from per-record; keep top summaries.
    lean_records = []
    for r in records:
        r2 = {k: v for k, v in r.items() if k != '_pair_stats'}
        lean_records.append(r2)
    with open(out_path, 'w') as f:
        json.dump({
            'records': lean_records,
            'plan': plan,
            'total_records': total,
            'skipped': skipped,
            'feature_rows': feat_rows,
            'best_single_by_min': best_single_feat_by_min,
            'best_single_by_mean': best_single_feat_by_mean,
            'best_single_by_perfect': best_single_feat_by_perfect,
            'best_pair_by_min': best_pair_by_min,
            'best_pair_by_mean': best_pair_by_mean,
            'best_pair_by_perfect': best_pair_by_perfect,
            'verdict': verdict,
            'verdict_msg': msg,
        }, f)
    print(f"\nWrote {out_path} ({total} records).", flush=True)


if __name__ == "__main__":
    main()
