#!/usr/bin/env python3
"""Analyze boundary coupling and P₀ oscillation for convergence proof.

CLB's key insight: T_Top(2,0,0)→1 requires c[0]=0, so the top boundary
can only fire its anomalous entry when the bottom is in state 0.

This script checks:
1. Which anomalous entries produce bad→bad vs bad→good transitions
2. The right-boundary mini-oscillation (T_Top anomalous + T_Top copy_R)
3. P₀ oscillation constraints
4. Whether bounding P₀ oscillation suffices to close the proof
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_high, T_top
from cup2_convergence_proof import T_mid_alt, build_system, classify, delta_fc, psi
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict


def main():
    print("BOUNDARY COUPLING ANALYSIS")
    print("=" * 70)

    # ── Per-anomalous-entry bad→bad analysis ───────────────────────
    print("\nPER-ENTRY BAD→BAD vs BAD→GOOD COUNTS")
    print("-" * 60)

    entry_names = {
        (0, 'bot', (0,0,0), 1): "T_bot(0,0,0)→1",
        (0, 'bot', (1,1,2), 0): "T_bot(1,1,2)→0",
        (-2, 'high', (1,1,1), 2): "T_high(1,1,1)→2",
        (-1, 'top', (2,0,0), 1): "T_top(2,0,0)→1",
    }

    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        counts = defaultdict(lambda: {'bb': 0, 'bg': 0})

        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    cls = classify(Li, Si, Ri, out)
                    if cls == "anomalous":
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        # Identify which entry
                        if i == 0:
                            key = f"T_bot({Li},{Si},{Ri})→{out}"
                        elif i == n-2:
                            key = f"T_high({Li},{Si},{Ri})→{out}"
                        elif i == n-1:
                            key = f"T_top({Li},{Si},{Ri})→{out}"
                        else:
                            key = f"T_mid({Li},{Si},{Ri})→{out}"

                        if succ in bad_set:
                            counts[key]['bb'] += 1
                        else:
                            counts[key]['bg'] += 1

        print(f"\n  n={nv}:")
        for key in sorted(counts.keys()):
            bb = counts[key]['bb']
            bg = counts[key]['bg']
            total = bb + bg
            print(f"    {key:>22}: {bb:>4} bad→bad, {bg:>4} bad→good "
                  f"({100*bg/total:.0f}% to good)" if total > 0 else f"    {key}: 0 transitions")

    # ── Check: does T_Top anomalous always go to good? ─────────────
    print("\n\nCRITICAL CHECK: T_Top(2,0,0)→1 — always bad→good?")
    print("-" * 60)
    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        top_bb = 0
        top_bg = 0
        top_examples = []
        for c in bad_set:
            # Check T_top anomalous: pos n-1, input (c[n-2], c[n-1], c[0])
            if c[n-2] == 2 and c[n-1] == 0 and c[0] == 0:
                # T_top(2,0,0)=1, anomalous
                lst = list(c); lst[n-1] = 1; succ = tuple(lst)
                if succ in bad_set:
                    top_bb += 1
                    if len(top_examples) < 3:
                        top_examples.append((c, succ))
                else:
                    top_bg += 1

        status = "ALWAYS BAD→GOOD ✓" if top_bb == 0 else f"{top_bb} bad→bad"
        print(f"  n={nv}: {top_bg} bad→good, {top_bb} bad→bad → {status}")
        for c, succ in top_examples:
            print(f"    BAD→BAD: {c} → {succ}")

    # ── Right-boundary mini-oscillation ────────────────────────────
    print("\n\nRIGHT-BOUNDARY MINI-OSCILLATION CHECK")
    print("-" * 60)
    print("Check: T_Top(2,0,0)→1 then T_Top(2,1,0)→0 — does this 2-cycle exist?")

    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        two_cycles = 0
        for c in bad_set:
            if c[n-2] == 2 and c[n-1] == 0 and c[0] == 0:
                # T_top(2,0,0)→1
                lst = list(c); lst[n-1] = 1; succ = tuple(lst)
                if succ in bad_set:
                    # Reverse: T_top(2,1,0)→0
                    if succ[n-2] == 2 and succ[n-1] == 1 and succ[0] == 0:
                        lst2 = list(succ); lst2[n-1] = 0; back = tuple(lst2)
                        if back == c:
                            two_cycles += 1

        print(f"  n={nv}: {two_cycles} potential 2-cycles "
              f"→ {'ALL BLOCKED (target is good)' if two_cycles == 0 else 'SOME EXIST!'}")

    # ── Phase analysis ─────────────────────────────────────────────
    print("\n\nPHASE B ANALYSIS (c[0]=1)")
    print("-" * 60)
    print("During Phase B: which anomalous entries can fire?")

    for nv in range(5, 9):
        prod = 4 * 3 ** (nv - 2)
        if prod > 10000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Phase B configs: c[0] = 1
        phase_b = [c for c in bad_set if c[0] == 1]

        anom_in_b = defaultdict(int)
        for c in phase_b:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    cls = classify(Li, Si, Ri, out)
                    if cls == "anomalous":
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            if i == 0:
                                key = f"T_bot({Li},{Si},{Ri})→{out}"
                            elif i == n-2:
                                key = f"T_high({Li},{Si},{Ri})→{out}"
                            elif i == n-1:
                                key = f"T_top({Li},{Si},{Ri})→{out}"
                            else:
                                key = f"T_mid({Li},{Si},{Ri})→{out}"
                            anom_in_b[key] += 1

        print(f"\n  n={nv} (Phase B, c[0]=1): {len(phase_b)} configs")
        if anom_in_b:
            for key in sorted(anom_in_b.keys()):
                print(f"    {key}: {anom_in_b[key]} bad→bad edges")
        else:
            print(f"    NO anomalous bad→bad edges in Phase B!")

    # ── P₀ oscillation: what decreases? ───────────────────────────
    print("\n\nP₀ OSCILLATION: QUANTITY TRACKING")
    print("-" * 60)
    print("For each T_bot(0,0,0)→1 firing, track the eventual return")
    print("via T_bot(1,1,2)→0 and check what decreases.\n")

    for nv in [5, 6, 7]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build full adjacency
        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        # Find configs where T_bot(0,0,0)→1 fires (bad→bad)
        bot001_sources = []
        for c in bad_set:
            if c[n-1] == 0 and c[0] == 0 and c[1] == 0:
                lst = list(c); lst[0] = 1; succ = tuple(lst)
                if succ in bad_set:
                    bot001_sources.append((c, succ))

        # For each, BFS to find configs where T_bot(1,1,2)→0 fires
        if nv <= 6:
            print(f"  n={nv}: {len(bot001_sources)} T_bot(0,0,0)→1 bad→bad edges")
            for src, after_001 in bot001_sources[:3]:
                # BFS from after_001 to find T_bot(1,1,2)→0 source
                from collections import deque
                visited = set()
                queue = deque([(after_001, [after_001])])
                visited.add(after_001)
                found_return = None
                while queue and found_return is None:
                    cur, path = queue.popleft()
                    # Check if T_bot(1,1,2)→0 fires here
                    if cur[n-1] == 1 and cur[0] == 1 and cur[1] == 2:
                        # T_bot(1,1,2)→0 fires
                        lst = list(cur); lst[0] = 0; ret = tuple(lst)
                        found_return = (cur, ret, path)
                        break
                    if len(path) > 30:
                        continue
                    for s in adj[cur]:
                        if s not in visited:
                            visited.add(s)
                            queue.append((s, path + [s]))

                if found_return:
                    pre_ret, post_ret, path = found_return
                    fc_src = sum(1 for j in range(n) if src[j] != src[(j+1)%n])
                    psi_src = psi(src, n)
                    fc_ret = sum(1 for j in range(n) if post_ret[j] != post_ret[(j+1)%n])
                    psi_ret = psi(post_ret, n)
                    print(f"    {src} →(0→1)→ ...({len(path)} steps)... →(1→0)→ {post_ret}")
                    print(f"      fc: {fc_src}→{fc_ret} ({fc_ret-fc_src:+d}), "
                          f"Ψ: {psi_src}→{psi_ret} ({psi_ret-psi_src:+d}), "
                          f"sum: {sum(src)}→{sum(post_ret)} ({sum(post_ret)-sum(src):+d})")


if __name__ == "__main__":
    main()
