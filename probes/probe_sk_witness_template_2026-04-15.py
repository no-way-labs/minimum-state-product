#!/usr/bin/env python3
"""Phase A probe: girth-2k witness templates.

For each of the 10 canonical-skeleton edges, extract the non-good
configuration in SK(C) that witnesses the edge — i.e. a config c whose
binary projection is the edge source, with a forced step to some c'
in SK(C) whose binary projection is the edge destination.

We run this across several (n, ms) cases with k = 3 binary positions
and look for a uniform template per edge: a description of the witness
that depends only on (edge, n, binary positions) and not on the rest of
the ms structure.

Outcome A (good): for each edge there is one template that works at
every (n, ms) tested → the girth-2k lemma has a clean symbolic proof
and Lean transcription is straightforward.

Outcome B (mixed): templates vary by ms or n → either the symbolic
construction needs additional case structure, or our 3-binary
projection is not the right invariant.

This probe is **discovery only** (§0.5 rule (d)). Its output never
enters Lean. The point is to confirm or refute the assumption that
T2's witness construction can be uniform.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time

# ----- canonical skeleton (matches Skeleton.lean / targets doc §1) -----
CANON_6CYC_REV = [
    ((0,1,1),(0,0,1)), ((0,0,1),(1,0,1)), ((1,0,1),(1,0,0)),
    ((1,0,0),(1,1,0)), ((1,1,0),(0,1,0)), ((0,1,0),(0,1,1)),
]
CANON_POLE = [
    ((0,0,1),(0,0,0)), ((0,0,0),(1,0,0)),
    ((1,1,0),(1,1,1)), ((1,1,1),(0,1,1)),
]
CANON_EDGES = CANON_6CYC_REV + CANON_POLE


# ----- forced graph + SK (same as prior probes, lifted unchanged) -----
def enumerate_sweep_cycles(ms, n, max_found=1, time_budget=60.0):
    mover_seq = list(range(n)) * 2
    L = len(mover_seq)
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
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
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
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    ok = False; break
                new_det[ki] = Si
            if not ok: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(0, start, {}, [start])
    return found


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True
                    break
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
        rounds += 1
    return remaining, rounds


# ----- witness extraction -----
def find_witnesses_for_edge(sk, adj, bpos3, edge):
    """All (c, c', mover) triples where:
       - c ∈ SK
       - projection of c onto bpos3 is edge[0]
       - some forced edge c → c' has c' ∈ SK
       - projection of c' onto bpos3 is edge[1]
       - the mover that produced c → c' is one of the binary positions
         (otherwise the projection edge is degenerate / not a binary flip)
    """
    src, dst = edge
    out = []
    for c in sk:
        if tuple(c[i] for i in bpos3) != src:
            continue
        for cprime, p in adj.get(c, []):
            if cprime not in sk: continue
            if tuple(cprime[i] for i in bpos3) != dst: continue
            if p not in bpos3: continue  # only count binary flips
            out.append((c, cprime, p))
    return out


def witness_template(witnesses, ms, n, bpos3):
    """Reduce a set of witnesses to a 'template': for each non-binary
    position, the set of values that any witness uses at that position.
    A 1-element set means 'forced value'; a multi-element set means
    'flexible'. Empty set means no witness."""
    if not witnesses:
        return None
    nbpos = [i for i in range(n) if i not in bpos3]
    template = {i: set() for i in nbpos}
    for c, _, _ in witnesses:
        for i in nbpos:
            template[i].add(c[i])
    return template


def template_signature(template):
    """A canonical signature of the template, useful for cross-case
    comparison. We encode each non-binary position as the sorted tuple
    of values the template allows."""
    if template is None:
        return None
    return tuple(sorted(template.items()))


def template_str(template, n, bpos3):
    """Pretty-print a template as a row, showing values per position."""
    parts = []
    for i in range(n):
        if i in bpos3:
            parts.append("B")
        else:
            vals = template.get(i, set())
            if not vals:
                parts.append("?")
            elif len(vals) == 1:
                parts.append(str(next(iter(vals))))
            else:
                parts.append("[" + "".join(str(v) for v in sorted(vals)) + "]")
    return " ".join(parts)


# ----- main sweep -----
def main():
    cases = [
        # (ms, n, label)
        ((2,2,2,3,3),               5, "n5 3CB"),
        ((2,2,2,3,3,3),             6, "n6 3CB"),
        ((2,2,2,3,3,3,3),           7, "n7 3CB"),
        ((2,2,2,3,3,3,3,3),         8, "n8 3CB"),
        ((2,2,2,3,3,3,3,3,3),       9, "n9 3CB"),
        # alternative binary placements
        ((2,3,2,3,2,3,3),           7, "n7 spread (0,2,4)"),
        ((2,3,3,2,3,2,3),           7, "n7 spread (0,3,5)"),
        ((2,3,3,2,3,3,2),           7, "n7 spread (0,3,6)"),
    ]

    # Per-edge accumulator: case_label → template signature
    per_edge_signatures = {edge: {} for edge in CANON_EDGES}
    per_edge_witness_count = {edge: {} for edge in CANON_EDGES}

    for ms, n, label in cases:
        print(f"\n===== {label}  ms={ms}  n={n}  product={1 if not ms else __import__('math').prod(ms)} =====")
        cycles = enumerate_sweep_cycles(ms, n, max_found=1, time_budget=60.0)
        if not cycles:
            print("  no sweep cycle found — skipping")
            continue
        cycle, movers, det = cycles[0]
        good_set = set(cycle)
        ng, _, adj = build_forced_graph(ms, n, det, good_set)
        sk, rounds = sink_kernel(ng, adj)
        bpos_all = [i for i, m in enumerate(ms) if m == 2]
        if len(bpos_all) < 3:
            print(f"  only {len(bpos_all)} binary positions — skipping (need ≥3)")
            continue
        bpos3 = bpos_all[:3]
        print(f"  |SK|={len(sk)}  rounds={rounds}  binary={bpos_all} → using {bpos3}")

        for edge in CANON_EDGES:
            witnesses = find_witnesses_for_edge(sk, adj, bpos3, edge)
            template = witness_template(witnesses, ms, n, bpos3)
            sig = template_signature(template)
            per_edge_signatures[edge][label] = sig
            per_edge_witness_count[edge][label] = len(witnesses)
            tag = "REV" if edge in CANON_6CYC_REV else "POLE"
            print(f"  [{tag}] {edge[0]} → {edge[1]}: {len(witnesses):3d} witnesses  "
                  f"template: {template_str(template, n, bpos3) if template else 'NONE'}")

    # ----- cross-case template comparison -----
    print("\n" + "=" * 70)
    print("CROSS-CASE TEMPLATE COMPARISON")
    print("=" * 70)
    print()
    print("For each edge: do witnesses across cases share a uniform")
    print("non-binary value pattern? (We can't directly compare templates")
    print("across different n, but we can compare *structure*.)")
    print()
    for edge in CANON_EDGES:
        tag = "REV" if edge in CANON_6CYC_REV else "POLE"
        print(f"[{tag}] edge {edge[0]} → {edge[1]}:")
        cases_with = [(lbl, cnt) for lbl, cnt in per_edge_witness_count[edge].items() if cnt > 0]
        cases_without = [lbl for lbl, cnt in per_edge_witness_count[edge].items() if cnt == 0]
        print(f"    has witnesses in {len(cases_with)}/{len(per_edge_witness_count[edge])} cases")
        if cases_without:
            print(f"    MISSING in: {cases_without}")
        # Compare templates for cases with the SAME (n, k, bpos3 layout)
        # by ms equivalence class
        for lbl, sig in per_edge_signatures[edge].items():
            if sig is None:
                continue
            # Format the signature compactly
            forced = [(i, next(iter(v))) for i, v in sig if len(v) == 1]
            flex = [(i, sorted(v)) for i, v in sig if len(v) > 1]
            print(f"    [{lbl}] forced: {forced}  flex: {flex}")
        print()


if __name__ == "__main__":
    main()
