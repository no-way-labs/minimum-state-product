#!/usr/bin/env python3
"""Check the PAIRED excursion property for fc-induction.

For a cycle at fc level f+1:
  a →(Δfc<0)→ x →(old path, fc≤f)→ y →(anomalous)→ b at fc=f+1

The key claim: Ψ(b) < Ψ(a) for every such reachable excursion.

If this holds + Ψ decreases on Δfc=0 paths at level f+1, then no cycle exists:
  Ψ(a₁) < Ψ(bₖ) < Ψ(aₖ) < ... < Ψ(b₁) < Ψ(a₁) → contradiction.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from cup2_psi_proof import psi, delta_fc
from itertools import product as cartesian
from collections import deque, defaultdict


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def main():
    print("PAIRED EXCURSION PROPERTY CHECK")
    print("=" * 70)
    print("Claim: for every excursion a→(down)→...→(up)→b at same fc level,")
    print("       Ψ(b) < Ψ(a).")
    print()

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

        # Compute fc
        fc = {c: sum(1 for j in range(n) if c[j] != c[(j+1)%n]) for c in bad_set}
        max_fc = max(fc.values())

        # Build adjacency lists
        adj_full = {c: [] for c in bad_set}
        adj_old = defaultdict(list)  # only fc≤f edges, built per level
        exits = defaultdict(list)    # exits[f] = [(a, x)] where a at fc=f, x at fc<f
        entries = defaultdict(list)  # entries[f] = [(y, b)] where y at fc<f, b at fc=f

        for c in bad_set:
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    dfc = delta_fc(Li, Si, Ri, out)
                    cls = classify_entry(Li, Si, Ri, out)
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        adj_full[c].append(succ)
                        if dfc < 0:
                            # Exit from fc(c) to fc(succ) < fc(c)
                            exits[fc[c]].append((c, succ))
                        if cls == "anomalous":
                            # Entry to fc(succ) from fc(c) < fc(succ)
                            entries[fc[succ]].append((c, succ))

        # For each fc level f, check paired excursion property
        total_violations = 0
        total_pairs = 0

        for f in range(2, max_fc + 1):
            if not exits[f] or not entries[f]:
                continue

            # Build old part: all configs with fc < f and edges among them
            old_configs = set(c for c in bad_set if fc[c] < f)
            old_adj = {c: [] for c in old_configs}
            for c in old_configs:
                for s in adj_full[c]:
                    if s in old_configs:
                        old_adj[c].append(s)

            # For each exit (a, x): find all configs reachable from x in old part
            # For each entry (y, b): check if y is reachable from some exit's x
            # If so, check Ψ(b) < Ψ(a)

            # Collect all entry sources (y values) for this level
            entry_sources = {}  # y → list of b
            for y, b in entries[f]:
                if y not in entry_sources:
                    entry_sources[y] = []
                entry_sources[y].append(b)

            # For each exit (a, x), BFS from x in old part
            for a, x in exits[f]:
                if x not in old_configs:
                    continue
                # BFS from x
                visited = set()
                queue = deque([x])
                visited.add(x)
                while queue:
                    cur = queue.popleft()
                    for s in old_adj[cur]:
                        if s not in visited:
                            visited.add(s)
                            queue.append(s)

                # Check which entry sources are reachable from x
                for y in entry_sources:
                    if y in visited:
                        for b in entry_sources[y]:
                            total_pairs += 1
                            psi_a = psi(a, n)
                            psi_b = psi(b, n)
                            if psi_b >= psi_a:
                                total_violations += 1
                                if total_violations <= 5 and nv <= 7:
                                    print(f"  VIOLATION n={nv} fc={f}: "
                                          f"a={a} Ψ={psi_a}, "
                                          f"b={b} Ψ={psi_b}")

        status = "ALL PAIRS SATISFY Ψ(b)<Ψ(a) ✓" if total_violations == 0 \
            else f"{total_violations} VIOLATIONS"
        print(f"  n={nv}: {total_pairs} reachable excursion pairs, {status}")


if __name__ == "__main__":
    main()
