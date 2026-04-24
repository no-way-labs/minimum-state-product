"""Scan: for each sample, test a family of structural hypotheses about
the bad cycle. Enumerate ALL bad cycles (or many) in each sample and check
if any satisfies a clean hypothesis.

Hypotheses to test:
H1: bad_cfg[k] = gc_cfg[k+d] with proc 0 toggled (for some d)
H2: bad_cfg[k] = gc_cfg[k+d] with all binary toggled
H3: bad_cfg[k] = gc_cfg[k+d] with odd/even k halves having different masks
H4: bad_cfg[k] = gc_cfg[sigma(k)] for some permutation sigma (on indices)
H5: there exist two "pivot" indices p1, p2 in gc such that
    bad = gc[p1:p2] reversed + gc[p2:p1] reversed (with flips)
H6: Sorting the bad_configs by some invariant reveals a bijection with gc
H7: bad_configs is a union of two length-12 "halves" each being a half of gc.
"""
import sys
sys.setrecursionlimit(50000)
import json
from itertools import product as iproduct

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [p for p in range(N) if MS[p] == 2]
TER_PROCS = [p for p in range(N) if MS[p] > 2]

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N


def build_gc_configs(w):
    cfg = [0]*N
    gc_configs = [tuple(cfg)]
    for m in w:
        cfg[m] = (cfg[m] + 1) % MS[m]
        gc_configs.append(tuple(cfg))
    return gc_configs[:-1]


def build_mover_triples(w, gc_configs):
    mover_triples = {}
    for k, p in enumerate(w):
        cfg = gc_configs[k]
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        mover_triples[(p, L, S, R)] = (S + 1) % MS[p]
    return mover_triples


def build_edges(mover_triples, gc_set):
    all_configs = list(iproduct(*[range(m) for m in MS]))
    edges = {}
    for c in all_configs:
        if c in gc_set: continue
        lst = []
        for p in range(N):
            L, S, R = c[left(p)], c[p], c[right(p)]
            key = (p, L, S, R)
            if key in mover_triples:
                Snew = mover_triples[key]
                if Snew != S:
                    new_c = list(c)
                    new_c[p] = Snew
                    new_c = tuple(new_c)
                    if new_c not in gc_set:
                        lst.append((new_c, p))
        edges[c] = lst
    return edges


def find_all_24_cycles(edges, max_count=200):
    """Enumerate length-24 simple cycles in edges, up to max_count per start."""
    # Too many overall; restrict to starts reached from canonical start
    cycles = []
    # Choose starting node: one whose out-degree > 0
    starts = [c for c in edges if len(edges.get(c, [])) > 0]
    # DFS from each start, limited to max_count total
    for start in starts:
        if len(cycles) >= max_count: break
        visited = {start}
        path = [(start, None)]
        def dfs(node, depth):
            if len(cycles) >= max_count: return
            for (nxt, p) in edges.get(node, []):
                if nxt == start and depth + 1 == 24:
                    cycles.append(list(path) + [(start, p)])
                    if len(cycles) >= max_count: return
                    continue
                if nxt in visited: continue
                if depth + 1 >= 24: continue
                visited.add(nxt)
                path.append((nxt, p))
                dfs(nxt, depth + 1)
                path.pop()
                visited.remove(nxt)
        dfs(start, 0)
    return cycles


def find_cycle_from_start(edges, start):
    """Find one simple length-24 cycle starting at `start`, if any."""
    visited = {start}
    path = [(start, None)]
    found = [None]
    def dfs(node, depth):
        if found[0] is not None: return
        for (nxt, p) in edges.get(node, []):
            if nxt == start and depth + 1 == 24:
                found[0] = list(path) + [(start, p)]
                return
            if nxt in visited: continue
            if depth + 1 >= 24: continue
            visited.add(nxt)
            path.append((nxt, p))
            dfs(nxt, depth + 1)
            if found[0] is not None: return
            path.pop()
            visited.remove(nxt)
    dfs(start, 0)
    return found[0]


def test_H1_shift_toggle0(gc_configs, bad_set):
    """Does there exist a delta d and cfg matching: bad = {gc[k+d] XOR (proc 0 flip) : k}?"""
    for d in range(CL):
        shifted = []
        for k in range(CL):
            c = list(gc_configs[(k+d) % CL])
            c[0] = 1 - c[0]
            shifted.append(tuple(c))
        if set(shifted) == bad_set:
            return d
    return None


def test_H2_shift_toggle_all_binary(gc_configs, bad_set):
    for d in range(CL):
        shifted = []
        for k in range(CL):
            c = list(gc_configs[(k+d) % CL])
            for p in BIN_PROCS: c[p] = 1 - c[p]
            shifted.append(tuple(c))
        if set(shifted) == bad_set:
            return d
    return None


def test_H4_permutation(gc_configs, bad_configs):
    """Does there exist a permutation sigma such that bad_cfg[k] = gc_cfg[sigma(k)] ?"""
    # Only possible if sets are equal
    return set(bad_configs) == set(gc_configs)


def test_H_flip_subset(gc_configs, bad_set):
    """Try all 8 binary masks: bad = gc XOR mask (as a set)."""
    for mask_idx in range(1, 8):
        mask = [(mask_idx >> i) & 1 for i in range(3)]
        results = []
        for k in range(CL):
            c = list(gc_configs[k])
            for (p, b) in zip(BIN_PROCS, mask):
                if b: c[p] = 1 - c[p]
            results.append(tuple(c))
        if set(results) == bad_set:
            return mask
    return None


def test_H_flip_and_shift(gc_configs, bad_set):
    """Try mask XOR and shift d."""
    for mask_idx in range(1, 8):
        mask = [(mask_idx >> i) & 1 for i in range(3)]
        for d in range(CL):
            results = []
            for k in range(CL):
                c = list(gc_configs[(k+d) % CL])
                for (p, b) in zip(BIN_PROCS, mask):
                    if b: c[p] = 1 - c[p]
                results.append(tuple(c))
            if set(results) == bad_set:
                return (mask, d)
    return None


def test_H_half_flip(gc_configs, bad_set):
    """Bad = first 12 configs of gc with some binary mask A, plus last 12 with mask B."""
    for mA_idx in range(8):
        for mB_idx in range(8):
            if mA_idx == 0 and mB_idx == 0: continue
            mA = [(mA_idx >> i) & 1 for i in range(3)]
            mB = [(mB_idx >> i) & 1 for i in range(3)]
            for dA in range(CL):
                for dB in range(CL):
                    results = []
                    for k in range(12):
                        c = list(gc_configs[(k+dA) % CL])
                        for (p, b) in zip(BIN_PROCS, mA):
                            if b: c[p] = 1 - c[p]
                        results.append(tuple(c))
                    for k in range(12):
                        c = list(gc_configs[(k+dB) % CL])
                        for (p, b) in zip(BIN_PROCS, mB):
                            if b: c[p] = 1 - c[p]
                        results.append(tuple(c))
                    if set(results) == bad_set:
                        return (mA, mB, dA, dB)
    return None


def analyze_sample_exhaustive(w, n_cycles=50):
    gc_configs = build_gc_configs(w)
    gc_set = set(gc_configs)
    mover_triples = build_mover_triples(w, gc_configs)
    edges = build_edges(mover_triples, gc_set)

    # Find many distinct cycles (by set)
    bad_sets_seen = set()
    cycles_found = []
    tried_starts = 0
    for start in edges:
        if tried_starts > 300 or len(cycles_found) >= n_cycles: break
        tried_starts += 1
        cyc = find_cycle_from_start(edges, start)
        if cyc is None: continue
        bad_configs = tuple(c for (c, _) in cyc[:-1])
        fs = frozenset(bad_configs)
        if fs in bad_sets_seen: continue
        bad_sets_seen.add(fs)
        bad_word = [p for (_, p) in cyc[1:]]
        cycles_found.append((bad_configs, bad_word))

    return gc_configs, gc_set, cycles_found


if __name__ == '__main__':
    # Load samples from pa2a_find_bad output if exists; otherwise re-enumerate
    from pa2a_find_bad import enumerate_residual
    samples = enumerate_residual(cap=20)
    print(f"Enumerated {len(samples)} residuals")
    print(f"Testing each with exhaustive bad-cycle search + hypothesis checks\n")

    hits = {'H1': 0, 'H2': 0, 'H4': 0, 'Hmask': 0, 'Hflipshift': 0, 'Hhalf': 0}
    total = 0
    for i, w in enumerate(samples):
        gc_configs, gc_set, cycles = analyze_sample_exhaustive(w, n_cycles=30)
        if not cycles:
            print(f"sample {i}: no cycles found"); continue
        total += 1
        print(f"\nSample {i}: gc_word={''.join(str(x) for x in w)}, found {len(cycles)} distinct bad cycles")
        found_any = False
        for cyc_idx, (bad_configs, bad_word) in enumerate(cycles):
            bad_set = set(bad_configs)
            r1 = test_H1_shift_toggle0(gc_configs, bad_set)
            r2 = test_H2_shift_toggle_all_binary(gc_configs, bad_set)
            r4 = test_H4_permutation(gc_configs, bad_configs)
            rmask = test_H_flip_subset(gc_configs, bad_set)
            rfs = test_H_flip_and_shift(gc_configs, bad_set)
            if r1 is not None or r2 is not None or r4 or rmask is not None or rfs is not None:
                print(f"  cycle {cyc_idx}: H1={r1} H2={r2} H4={r4} Hmask={rmask} Hflipshift={rfs}")
                if r1 is not None: hits['H1'] += 1
                if r2 is not None: hits['H2'] += 1
                if r4: hits['H4'] += 1
                if rmask is not None: hits['Hmask'] += 1
                if rfs is not None: hits['Hflipshift'] += 1
                found_any = True
                break
        if not found_any:
            # Check if any bad_config overlaps with gc_configs at all (as ternary projection)
            bad_configs, bad_word = cycles[0]
            n_bin_flipped = 0
            # How many bad configs have proc0 flipped relative to some gc config matching on ternary?
            for bc in bad_configs:
                ter_match_with_0_flipped = False
                for gc in gc_configs:
                    if all(bc[p] == gc[p] for p in TER_PROCS):
                        if bc[0] != gc[0]:
                            ter_match_with_0_flipped = True
                            break
                if ter_match_with_0_flipped:
                    n_bin_flipped += 1
            print(f"  no hypothesis matches; bad_configs with ter-match+bin0-flip: {n_bin_flipped}/{len(bad_configs)}")

    print(f"\nHit counts over {total} samples: {hits}")
