"""At shift d=2, most bad_cfgs are gc_cfgs[k+2] with proc 0 flipped.
The "transition" positions have diff=3. What is the exact pattern of those
transition configs?

Hypothesis: the transition patches are also gc_cfgs[k+δ'] with different
shifts for a few steps. Maybe 4 distinct shift regions?"""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples, build_edges
from pa2a_perm_analysis import find_one_bad_cycle

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


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

        # For each bad_config, find ALL shifts d such that bad_cfg[k] ~ gc_cfg[k+d] with proc0-only flip
        bad_matches = []
        for k in range(CL):
            bc = bad_configs[k]
            matches = []
            for d in range(CL):
                gc = gc_configs[(k+d) % CL]
                diff = [i for i in range(N) if bc[i] != gc[i]]
                if len(diff) == 0:
                    matches.append((d, 'exact', []))
                elif len(diff) == 1 and diff[0] == 0:
                    matches.append((d, 'flip0', []))
                elif len(diff) <= 2:
                    matches.append((d, 'small', diff))
            bad_matches.append((k, bc, matches))
            # Print
            best = min(matches, key=lambda m: 0 if m[1]=='flip0' else (1 if m[1]=='exact' else 2)) if matches else None
            print(f"  bad[{k:2d}]={bc} mover={bad_word[k] if k < len(bad_word) else '?'}")
            if matches:
                shown = matches[:5]
                print(f"      matches: {shown}")
        print()


if __name__ == '__main__':
    main()
