#!/usr/bin/env python3
"""
CONVERGENCE PROOF 104: Find secondary potential on constant-Φ_full edges
=========================================================================
Constant-Φ_full edges have Δfc + Δg_full = 0. We need a secondary quantity
that strictly decreases on ALL constant-Φ_full edges → proves DAG.

Interior Δfc=0 entries move "disagreement particles":
  (1,0,0)→1: moves disagreement RIGHT  (+1 to position-weighted sum)
  (0,2,2)→0: moves disagreement RIGHT  (+1)
  (1,1,2)→2: moves disagreement LEFT   (-1)

Test candidates:
1. W(c) = Σ j·[c[j]≠c[j+1]] — position-weighted disagreement
2. Weighted fc: Σ w_j·[c[j]≠c[j+1]] for various weights w
3. Interior pair encodings
4. Count of specific patterns
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)
def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)
def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [7, 8, 9, 10, 11]:
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        if len(bad_list) > 900000:
            print(f"\nn={n}: skipping ({len(bad_list)} bad)")
            continue

        # Build TP edges + g_full
        tp_fwd = defaultdict(list)
        tp_nodes = set()
        fc_cache = {}
        tp_edge_list = []
        for c in bad_list:
            fc_cache[c] = fc(c, n)
            tp_nodes.add(c)
        for c in bad_list:
            e2c = exp2_count(c, n)
            i21c = int_21(c, n)
            ewc = exp2_weight(c, n)
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        if succ not in fc_cache:
                            fc_cache[succ] = fc(succ, n)
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            dfc = fc_cache[succ] - fc_cache[c]
                            tp_fwd[c].append((succ, dfc))
                            tp_edge_list.append((c, succ, i, dfc))
                            tp_nodes.add(succ)

        g = {c: 0 for c in tp_nodes}
        for _ in range(2 * n + 5):
            changed = False
            for c in tp_nodes:
                for s, dfc in tp_fwd.get(c, []):
                    new_g = dfc + g[s]
                    if new_g > g[c]:
                        g[c] = new_g
                        changed = True
            if not changed:
                break

        phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

        # Extract constant-Φ_full edges
        const_edges = [(c, s, pos, dfc) for c, s, pos, dfc in tp_edge_list
                       if phi[s] == phi[c]]

        print(f"\n{'='*70}")
        print(f"n={n}: {len(const_edges)} constant-Φ_full edges")

        # ============================================================
        # Test candidate secondary potentials
        # ============================================================

        def disagree_positions(c):
            """Set of edge positions where c[j] ≠ c[j+1]."""
            return frozenset(j for j in range(n) if c[j] != c[(j+1)%n])

        # Candidate 1: W = Σ j * [c[j] ≠ c[j+1]] — position-weighted disagreement
        def W1(c):
            return sum(j for j in range(n) if c[j] != c[(j+1)%n])

        # Candidate 2: W = Σ (n-1-j) * [c[j] ≠ c[j+1]] — reversed weights
        def W2(c):
            return sum((n-1-j) for j in range(n) if c[j] != c[(j+1)%n])

        # Candidate 3: W = Σ j² * [c[j] ≠ c[j+1]]
        def W3(c):
            return sum(j*j for j in range(n) if c[j] != c[(j+1)%n])

        # Candidate 4: Σ j * c[j] — position-weighted config sum
        def W4(c):
            return sum(j * c[j] for j in range(n))

        # Candidate 5: Σ (n-1-j) * c[j] — reversed
        def W5(c):
            return sum((n-1-j) * c[j] for j in range(n))

        # Candidate 6: Interior value sum Σ c[j] for j=2..n-3
        def W6(c):
            return sum(c[j] for j in range(2, n-2))

        # Candidate 7: Count of 1s in interior
        def W7(c):
            return sum(1 for j in range(2, n-2) if c[j] == 1)

        # Candidate 8: Count of 2s in interior
        def W8(c):
            return sum(1 for j in range(2, n-2) if c[j] == 2)

        # Candidate 9: (n-j) * disagreement — emphasize left
        def W9(c):
            return sum((n-j) for j in range(n) if c[j] != c[(j+1)%n])

        # Candidate 10: center distance * disagreement
        def W10(c):
            mid = (n-1) / 2.0
            return sum(abs(j - mid) for j in range(n) if c[j] != c[(j+1)%n])

        # Candidate 11: Σ j * (c[j] == 0) — count 0s weighted by position
        def W11(c):
            return sum(j for j in range(n) if c[j] == 0)

        # Candidate 12: Σ (c[j] * c[(j+1)%n]) — adjacent product sum
        def W12(c):
            return sum(c[j] * c[(j+1)%n] for j in range(n))

        # Candidate 13: number of "10" patterns in interior
        def W13(c):
            return sum(1 for j in range(2, n-2) if c[j] == 1 and c[(j+1)%n] == 0)

        # Candidate 14: number of "12" patterns
        def W14(c):
            return sum(1 for j in range(n-1) if c[j] == 1 and c[j+1] == 2)

        candidates = [
            ("W_pos", W1), ("W_rpos", W2), ("W_pos2", W3),
            ("jc", W4), ("jc_rev", W5), ("int_sum", W6),
            ("int_1s", W7), ("int_2s", W8), ("W_nj", W9), ("W_ctr", W10),
            ("j_0s", W11), ("adj_prod", W12), ("int_10", W13), ("pat_12", W14),
        ]

        print(f"\n  Candidate potentials on constant-Φ edges:")
        for name, fn in candidates:
            inc = 0; dec = 0; eq = 0
            for c, s, pos, dfc in const_edges:
                d = fn(s) - fn(c)
                if d > 0: inc += 1
                elif d < 0: dec += 1
                else: eq += 1
            # Report the direction with fewer edges (= violations if we pick the other)
            viols = min(inc, dec)
            direction = "↓" if dec > inc else "↑" if inc > dec else "="
            total = len(const_edges)
            print(f"    {name:12s}: ↑{inc} ↓{dec} ={eq} | "
                  f"best: {direction} with {viols}/{total} viols ({100*viols/total:.1f}%)")

        # ============================================================
        # Try COMBINATIONS: Φ_full * K + W for various W
        # ============================================================
        print(f"\n  Lexicographic (Φ_full, W) on ALL TP edges:")
        for name, fn in candidates:
            viols = 0
            for c, s, pos, dfc in tp_edge_list:
                dphi = phi[s] - phi[c]
                if dphi > 0:
                    viols += 1
                elif dphi == 0:
                    d = fn(s) - fn(c)
                    if d >= 0:  # need strict decrease
                        viols += 1
            total = len(tp_edge_list)
            if viols < total * 0.05:  # only show promising ones
                print(f"    (Φ, -{name:12s}): {viols}/{total} viols ({100*viols/total:.2f}%)")

        # ============================================================
        # Analyze ΔW by entry type on constant edges
        # ============================================================
        print(f"\n  ΔW_pos by entry type on constant edges:")
        dw_by_entry = defaultdict(list)
        for c, s, pos, dfc in const_edges:
            L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
            if pos == 0: ptype = "bot"
            elif pos == 1: ptype = "low"
            elif pos == 2: ptype = "P2"
            elif pos == n-2: ptype = "high"
            elif pos == n-1: ptype = "top"
            else: ptype = "mid"
            key = (ptype, L, S, R, out, dfc)
            dw = W1(s) - W1(c)
            dw_by_entry[key].append(dw)

        for key, dws in sorted(dw_by_entry.items(), key=lambda x: -len(x[1])):
            ptype, L, S, R, out, dfc = key
            dw_set = sorted(set(dws))
            cnt = Counter(dws)
            print(f"    {ptype:4s} ({L},{S},{R})→{out} Δfc={dfc:+d}: ΔW ∈ {dw_set[:8]}"
                  f"{'...' if len(dw_set)>8 else ''} ({len(dws)} edges)")

        # ============================================================
        # Key test: for mid-position Δfc=0 edges, is ΔW always the same?
        # ============================================================
        print(f"\n  Mid-position Δfc=0 entry ΔW analysis:")
        for c, s, pos, dfc in const_edges:
            if 3 <= pos <= n-3 and dfc == 0:
                L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]; out = s[pos]
                # Check: does the disagreement actually hop?
                # Before: disagree at (pos-1,pos) iff L≠S, at (pos,pos+1) iff S≠R
                # After: disagree at (pos-1,pos) iff L≠out, at (pos,pos+1) iff out≠R
                before_left = (L != S)
                before_right = (S != R)
                after_left = (L != out)
                after_right = (out != R)
                break
        # Just confirm the hop directions
        for entry_type in [(1,0,0,1), (0,2,2,0), (1,1,2,2)]:
            L, S, R, out = entry_type
            bl = (L != S); br = (S != R)
            al = (L != out); ar = (out != R)
            change_l = al - bl  # +1 = new disagree, -1 = resolved
            change_r = ar - br
            print(f"    ({L},{S},{R})→{out}: left {bl}→{al} ({change_l:+d}), right {br}→{ar} ({change_r:+d})")

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
