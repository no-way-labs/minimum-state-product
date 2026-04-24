"""For the found bad cycle, compare bad_configs[k] vs gc_configs[k+d] for
various shifts d. Print the difference pattern."""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples, build_edges
from pa2a_perm_analysis import find_one_bad_cycle

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24

def cfg_diff(c1, c2):
    return tuple(a - b for a, b in zip(c1, c2))

def main():
    samples = enumerate_residual(cap=5)
    for si, w in enumerate(samples):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        edges = build_edges(mover_triples, gc_set)
        cyc = find_one_bad_cycle(edges)
        if cyc is None: continue
        bad_configs = [c for (c, _) in cyc[:-1]]
        bad_word = [p for (_, p) in cyc[1:]]
        print(f"=== Sample {si}: gc_word={''.join(str(x) for x in w)} ===")
        print(f"bad_word={''.join(str(x) for x in bad_word)}")
        # Try shifts
        for d in range(CL):
            diffs = []
            max_h = 0
            for k in range(CL):
                diff = cfg_diff(bad_configs[k], gc_configs[(k+d) % CL])
                h = sum(1 for x in diff if x != 0)
                max_h = max(max_h, h)
                diffs.append(h)
            avg = sum(diffs)/CL
            if avg < 2.5:
                print(f"  shift d={d}: avg diff = {avg:.2f}, max = {max_h}, per-step diff: {diffs}")
        print()


if __name__ == '__main__':
    main()
