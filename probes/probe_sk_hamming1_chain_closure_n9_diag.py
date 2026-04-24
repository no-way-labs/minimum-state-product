#!/usr/bin/env python3
"""Diagnostic for n=9 dead-end cases in Probe C.

The main probe reported 4 n=9 cycles where the canonical witness chain
terminates in 'dead_end' (no forced successor found). This is critical:
dead-end means the witness has NO forced neighbor, so it would NOT be in
SK. We need to check whether the dead-end config is c* itself, or some
later node in the chain.
"""
import importlib.util, os, sys, json
from collections import Counter, defaultdict
sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_A = os.path.join(_HERE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py")
_C = os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py")
spa = importlib.util.spec_from_file_location("probe_a", _A)
pa = importlib.util.module_from_spec(spa); spa.loader.exec_module(pa)
spc = importlib.util.spec_from_file_location("probe_c", _C)
pc = importlib.util.module_from_spec(spc); spc.loader.exec_module(pc)


def main():
    ms = (2,2,2,2,3,3,3,3,3)
    n = 9
    cycles = pa.enumerate_cycles_multistart(ms, n, L_min=2*n+2, L_max=22,
                                              time_budget=60.0, max_cycles=4)
    print(f"n=9  ms={ms}  cycles found: {len(cycles)}")
    for idx, (cycle, movers, det) in enumerate(cycles):
        L = len(movers)
        N1, adj, peel_set, provenance, V, move_entries, cycle_set = \
            pa.build_N1_and_peel(ms, n, cycle, det)
        if not peel_set:
            print(f"  cycle {idx}: no peel")
            continue
        c_star = sorted(peel_set)[0]
        print(f"\n  cycle {idx}: L={L} cycle_size={len(cycle_set)} "
              f"N1_size={len(N1)} peel_size={len(peel_set)}")
        print(f"    c_star = {c_star}")
        chain = pc.trace_chain(c_star, det, n, cycle_set, max_steps=2000)
        print(f"    chain length = {chain['path_length']}")
        print(f"    termination  = {chain['termination']}")
        print(f"    max hamming  = {chain['max_hamming']}")
        print(f"    hamming traj = {chain['hamming_trajectory']}")
        # Trace path explicitly to find the dead-end node and inspect it
        path = [c_star]
        visited = {c_star: 0}
        hammings = [pc.hamming(c_star, cycle_set)]
        for step in range(200):
            c = path[-1]
            succs = pc.forced_successors(c, det, n, cycle_set)
            ng = [(p, nc) for (kind, p, nc) in succs if kind == 'ng']
            on_cycle = [(p, nc) for (kind, p, nc) in succs if kind == 'cycle']
            if not ng and not on_cycle:
                print(f"    DEAD-END @step {step}, config = {c}")
                print(f"      forced_successors returned empty.")
                # enumerate all defined det entries at this config
                defined_positions = []
                for p in range(n):
                    ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    if ctx in det:
                        val = det[ctx]
                        defined_positions.append((p, ctx, val, val == c[p]))
                print(f"      det entries at this config: {defined_positions}")
                # Is the config in VC_NG?
                print(f"      in cycle_set? {c in cycle_set}")
                # Is the config in N_1?
                print(f"      in N1? {c in N1}")
                # Is the config in peel?
                print(f"      in peel? {c in peel_set}")
                # compute HAMMING from c_star:
                hs = sum(1 for i in range(n) if c[i] != c_star[i])
                print(f"      hamming from c_star = {hs}")
                break
            if not ng and on_cycle:
                print(f"    REACH CYCLE @step {step}")
                break
            ng.sort(key=lambda x: x[1])
            nc = ng[0][1]
            if nc in visited:
                print(f"    LOOP @step {step}")
                break
            visited[nc] = len(path); path.append(nc); hammings.append(pc.hamming(nc, cycle_set))
        # Critical check: does c_star itself have any forced neighbor at all?
        # including cycle-bound ones (since SK needs VC_NG neighbor, cycle-bound
        # doesn't count for SK membership)
        succs_cstar = pc.forced_successors(c_star, det, n, cycle_set)
        ng_cs = [x for x in succs_cstar if x[0] == 'ng']
        cyc_cs = [x for x in succs_cstar if x[0] == 'cycle']
        print(f"    c_star forced successors: {len(ng_cs)} NG, {len(cyc_cs)} cycle-bound")
        # SK membership needs ≥1 forced neighbor in SK ⊆ VC_NG.
        # If c_star has ≥1 NG forced successor, good. Otherwise c_star ∉ SK.
        if not ng_cs:
            print(f"    CRITICAL: c_star has NO NG forced successor — c_star ∉ SK by def.")


if __name__ == "__main__":
    main()
