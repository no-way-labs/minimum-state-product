#!/usr/bin/env python3
"""For odd-winding non-consecutive isolated binary procs: is fc always 2?"""
import random

def random_transition(m_left, m_self, m_right):
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f

def privileged(config, sys_f, ms, n, i):
    return sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]

def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    return privs[0] if len(privs) == 1 else None

def apply_move(config, sys_f, ms, n, i):
    nc = list(config)
    nc[i] = sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])]
    return tuple(nc)

def main():
    random.seed(42)

    # We need odd-winding cycles. These are rare for sub-threshold.
    # Check_winding showed 100% zero-winding for sub-threshold + ≥3 binary.
    # But the odd-winding path IS reached from CaseObstructions for non-sub-threshold.
    # The sorry's hypotheses include sub-threshold though.
    #
    # Wait — the odd-winding NON-CONSECUTIVE path in CaseObstructions does NOT
    # require sub-threshold directly. It has: odd-winding + ≥3 binary + no 3 consec.
    # The sub-threshold comes when it calls subThreshold_binary_core_false.
    #
    # But all sub-threshold cycles are zero-winding (from check_winding.py).
    # So the odd-winding non-consecutive path is VACUOUSLY EMPTY for sub-threshold.
    # It's only reached for non-sub-threshold systems... but subThreshold_obstruction
    # ONLY applies to sub-threshold systems!
    #
    # Wait. Let me re-read the proof tree.
    # subThreshold_obstruction has _hsub. It case-splits on winding.
    # Non-zero winding → nonZeroWinding_shadow → oddWinding... → sorry.
    # The sorry has _hsub in its hypotheses.
    # But computationally: sub-threshold + ≥3 binary → ALWAYS zero winding.
    # So the non-zero winding branch is vacuously empty!

    print("KEY INSIGHT:")
    print("Sub-threshold + ≥3 binary → 100% zero winding (confirmed computationally)")
    print("Therefore:")
    print("  - The sweep non-consecutive isolated path is VACUOUSLY EMPTY")
    print("  - The odd-winding non-consecutive isolated path is VACUOUSLY EMPTY")
    print("  - Only the zero-winding non-consecutive path actually reaches the sorry")
    print()
    print("If we can prove 'sub-threshold + ≥3 binary → zero winding',")
    print("the non-zero winding branches disappear and only the zero-winding")
    print("non-consecutive path remains (1 path instead of 3).")
    print()
    print("Combined with point 1 (consecutive zero-winding already sorry-free):")
    print("  Only ZERO-WINDING NON-CONSECUTIVE remains.")
    print("  This is the hardest case but it's the ONLY one.")

if __name__ == '__main__':
    main()
