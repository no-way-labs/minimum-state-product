#!/usr/bin/env python3
"""
CONVERGENCE PROOF 80: Layer 1 mechanism analysis
=================================================
Goal: Understand WHY Δint_j(2,0) ≤ 0 on zero-int(2,1) excursion edges.

For each excursion edge (u → v) with Δint(2,1)=0:
1. Identify the anomalous entry and position
2. Track how (2,0) pairs change step-by-step through the chain
3. Identify the MECHANISM: why does the chain compensate for any
   int_j(2,0) increase from the anomalous step?
4. Classify by entry type and interior pattern.

Also: check if Δint_j(2,0) ≤ 0 holds on ALL excursion edges (not just
zero-int(2,1) ones). If so, Layer 1 follows from Layer 0.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

def delta_fc_val(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def classify_entry(pos, L, S, R, out, n):
    if pos == 0 and (L, S, R, out) == (0, 0, 0, 1):
        return 'E1'
    elif pos == 0 and (L, S, R, out) == (1, 1, 2, 0):
        return 'E2'
    elif 2 <= pos <= n - 3 and (L, S, R, out) == (2, 1, 1, 0):
        return f'E3@{pos}'
    elif pos == n - 2 and (L, S, R, out) == (1, 1, 1, 2):
        return 'E4'
    elif pos == n - 1 and (L, S, R, out) == (2, 0, 0, 1):
        return 'E5'
    else:
        return f'?@{pos}({L},{S},{R})→{out}'


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build transition info
        anom_edges = []
        dfc_le0_adj = defaultdict(list)
        for c in bad_list:
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        dfc = delta_fc_val(L, S, R, out)
                        if dfc <= 0:
                            dfc_le0_adj[c].append(succ)
                        if out != L and out != R:
                            anom_edges.append((c, succ, i, dfc))

        anom_sources = set(c for c, _, _, _ in anom_edges)
        anom_target_map = defaultdict(list)
        anom_step_info = {}
        for c, succ, i, dfc in anom_edges:
            anom_target_map[succ].append(c)
            anom_step_info[(c, succ)] = (i, c[(i-1)%n], c[i], c[(i+1)%n], succ[i])

        # Build excursion edges with invariant info
        exc_with_inv = []
        seen = set()
        for b in set(s for _, s, _, _ in anom_edges):
            visited = {b}; queue = [b]; head = 0
            while head < len(queue):
                node = queue[head]; head += 1
                if node in anom_sources:
                    for src in anom_target_map.get(b, []):
                        if (src, node) not in seen:
                            seen.add((src, node))
                            info = anom_step_info.get((src, b))
                            d21 = int_21(node, n) - int_21(src, n)
                            dj20 = int_j_20(node, n) - int_j_20(src, n)
                            d20 = int_20(node, n) - int_20(src, n)
                            exc_with_inv.append((src, node, info, d21, dj20, d20))
                for nxt in dfc_le0_adj.get(node, []):
                    if nxt not in visited:
                        visited.add(nxt); queue.append(nxt)

        print(f"\n{'='*70}", flush=True)
        print(f"n={n}: {len(exc_with_inv)} excursion edges ({time.time()-t0:.1f}s)", flush=True)

        # === 1. Check: is Δint_j(2,0) ≤ 0 on ALL excursion edges? ===
        all_edges_dj20 = Counter()
        for _, _, _, d21, dj20, d20 in exc_with_inv:
            all_edges_dj20[dj20 <= 0] += 1

        all_neg = sum(1 for _, _, _, _, dj20, _ in exc_with_inv if dj20 <= 0)
        all_pos = sum(1 for _, _, _, _, dj20, _ in exc_with_inv if dj20 > 0)
        print(f"  Δint_j(2,0) ≤ 0 on ALL exc edges? neg/zero={all_neg}, positive={all_pos}",
              flush=True)

        # === 2. Check: is Δint_j(2,0) ≤ 0 on ALL edges (not just zero-21)? ===
        # If true, Layer 1 follows from Layer 0 directly!
        if all_pos > 0:
            # When positive, what's the d21?
            pos_d21 = Counter()
            for _, _, _, d21, dj20, _ in exc_with_inv:
                if dj20 > 0:
                    pos_d21[d21] += 1
            print(f"  Positive Δint_j(2,0) by Δint(2,1): {dict(pos_d21)}", flush=True)

        # === 3. On zero-int(2,1) edges: Δint_j(2,0) analysis ===
        zero21 = [(u, v, info, dj20, d20) for u, v, info, d21, dj20, d20 in exc_with_inv
                   if d21 == 0]
        z21_neg = sum(1 for _, _, _, dj20, _ in zero21 if dj20 < 0)
        z21_zero = sum(1 for _, _, _, dj20, _ in zero21 if dj20 == 0)
        z21_pos = sum(1 for _, _, _, dj20, _ in zero21 if dj20 > 0)
        print(f"  Zero-int(2,1) edges: {len(zero21)}, "
              f"Δint_j(2,0): neg={z21_neg}, zero={z21_zero}, pos={z21_pos}", flush=True)

        if z21_pos > 0:
            print(f"  WARNING: Layer 1 VIOLATION at n={n}!", flush=True)

        # === 4. Entry type analysis on zero-21 edges ===
        entry_dj20 = defaultdict(list)
        for u, v, info, dj20, d20 in zero21:
            if info:
                pos, L, S, R, out = info
                etype = classify_entry(pos, L, S, R, out, n)
            else:
                etype = '?'
            entry_dj20[etype].append(dj20)

        print(f"\n  Entry types on zero-int(2,1) edges:", flush=True)
        for etype in sorted(entry_dj20.keys()):
            vals = entry_dj20[etype]
            neg = sum(1 for v in vals if v < 0)
            zer = sum(1 for v in vals if v == 0)
            pos = sum(1 for v in vals if v > 0)
            mn = min(vals) if vals else 0
            mx = max(vals) if vals else 0
            print(f"    {etype:15s}: {len(vals)} edges, Δintj20 ∈ [{mn},{mx}], "
                  f"neg={neg} zero={zer} pos={pos}", flush=True)

        # === 5. Also check Δint(2,0) on zero-21 edges ===
        z21_d20_neg = sum(1 for _, _, _, _, d20 in zero21 if d20 < 0)
        z21_d20_zero = sum(1 for _, _, _, _, d20 in zero21 if d20 == 0)
        z21_d20_pos = sum(1 for _, _, _, _, d20 in zero21 if d20 > 0)
        print(f"\n  Δint(2,0) on zero-21 edges: neg={z21_d20_neg}, "
              f"zero={z21_d20_zero}, pos={z21_d20_pos}", flush=True)

        # === 6. Joint (Δint(2,1), Δint_j(2,0)) on ALL excursion edges ===
        joint = Counter()
        for _, _, _, d21, dj20, _ in exc_with_inv:
            joint[(d21, dj20 <= 0)] += 1

        print(f"\n  Joint (Δint(2,1), Δint_j(2,0)≤0?):", flush=True)
        for (d21, neg), cnt in sorted(joint.items()):
            sgn = "≤0" if neg else ">0"
            print(f"    Δint21={d21:+d}, Δintj20{sgn}: {cnt}", flush=True)

        # === 7. Detailed: Δint_j(2,0) distribution by Δint(2,1) ===
        by_d21 = defaultdict(list)
        for _, _, _, d21, dj20, _ in exc_with_inv:
            by_d21[d21].append(dj20)

        print(f"\n  Δint_j(2,0) distribution by Δint(2,1):", flush=True)
        for d21 in sorted(by_d21.keys()):
            vals = by_d21[d21]
            if vals:
                mn, mx = min(vals), max(vals)
                neg = sum(1 for v in vals if v < 0)
                zer = sum(1 for v in vals if v == 0)
                pos = sum(1 for v in vals if v > 0)
                mean = sum(vals) / len(vals)
                print(f"    Δint21={d21:+d}: {len(vals)} edges, Δintj20 ∈ [{mn},{mx}], "
                      f"mean={mean:.1f}, neg={neg} zero={zer} pos={pos}", flush=True)

        # === 8. What about Δ(int_j(2,0) + int_j(2,1))? ===
        # Since int_j(2,1) = Σ j for (2,1) pairs, and int(2,1) = count of (2,1) pairs
        # If a (2,1) pair at position j becomes (2,0): int_j(2,1) decreases by j,
        # int_j(2,0) increases by j. So int_j(2,0) + int_j(2,1) is preserved!
        # Wait, only if the transformation is (2,1)→(2,0) at the same position.
        # Let me check.
        from collections import namedtuple

        def int_j_combined(c, n):
            """int_j(2,0) + int_j(2,1) = sum of j where c[j]=2 for interior j."""
            return sum(j for j in range(2, n - 2) if c[j] == 2 and c[j+1] in (0, 1))

        def int_j_all2(c, n):
            """sum of j where c[j]=2 for interior j, regardless of c[j+1]."""
            return sum(j for j in range(2, n - 2) if c[j] == 2)

        combined_test = []
        all2_test = []
        for u, v, info, d21, dj20, d20 in exc_with_inv:
            dc = int_j_combined(v, n) - int_j_combined(u, n)
            da = int_j_all2(v, n) - int_j_all2(u, n)
            combined_test.append(dc)
            all2_test.append(da)

        comb_neg = sum(1 for v in combined_test if v < 0)
        comb_zero = sum(1 for v in combined_test if v == 0)
        comb_pos = sum(1 for v in combined_test if v > 0)
        a2_neg = sum(1 for v in all2_test if v < 0)
        a2_zero = sum(1 for v in all2_test if v == 0)
        a2_pos = sum(1 for v in all2_test if v > 0)
        print(f"\n  Δ(intj20+intj21) on ALL exc edges: neg={comb_neg} zero={comb_zero} "
              f"pos={comb_pos}", flush=True)
        print(f"  Δ(Σj where c[j]=2) on ALL exc edges: neg={a2_neg} zero={a2_zero} "
              f"pos={a2_pos}", flush=True)

        # === 9. Is Σ(j * c[j]) monotone on excursion edges? ===
        def weighted_sum(c, n):
            return sum(j * c[j] for j in range(n))

        ws_neg = sum(1 for u, v, *_ in exc_with_inv if weighted_sum(v,n) < weighted_sum(u,n))
        ws_zero = sum(1 for u, v, *_ in exc_with_inv if weighted_sum(v,n) == weighted_sum(u,n))
        ws_pos = sum(1 for u, v, *_ in exc_with_inv if weighted_sum(v,n) > weighted_sum(u,n))
        print(f"  Δ(Σj*c[j]) on ALL exc edges: neg={ws_neg} zero={ws_zero} pos={ws_pos}",
              flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
