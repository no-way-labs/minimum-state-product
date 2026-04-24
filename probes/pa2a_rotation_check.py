"""Sanity check: does the formula work under cyclic rotation of gc word?
(i.e., starting the gc at a different config in the same cycle)"""
import sys
sys.setrecursionlimit(50000)
from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_final_verify import verify_sample, TABLE

samples = enumerate_residual(cap=5)
for si, w in enumerate(samples):
    print(f"sample {si}: gc_word={''.join(str(x) for x in w)}")
    # Rotate the word cyclically
    for rot in [1, 3, 5, 10, 12, 15, 20]:
        w_rot = tuple(list(w[rot:]) + list(w[:rot]))
        # Note: w_rot starting from (0,...,0) generates a different cycle
        # (since config is built from the start config). The cycle is the
        # SAME cycle as gc, but "starting" at a different place. However,
        # our verify_sample builds gc_configs from w_rot starting at (0,...,0),
        # which is NOT the same config as gc's original cycle. So this
        # test is just checking that the formula applies to DIFFERENT residuals.
        try:
            good, msg = verify_sample(w_rot)
            print(f"  rot={rot}: {good}, {msg}")
        except AssertionError as e:
            print(f"  rot={rot}: assertion failed: {e}")
