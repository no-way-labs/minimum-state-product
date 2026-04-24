#!/usr/bin/env python3
"""Extract and compare ternary processor rules from CLB construction at multiple n.

Focus on finding a universal closed-form rule for the ternary middles.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_clb_general import build_system_general


def print_full_table(fs, p, ms, n, label):
    m_L = ms[(p - 1) % n]
    m_S = ms[p]
    m_R = ms[(p + 1) % n]
    priv_entries = []
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                out = fs[p](L, S, R)
                if out != S:
                    priv_entries.append((L, S, R, out))
    print(f"  {label}: {len(priv_entries)} privileged, table:")
    for L in range(m_L):
        row = []
        for S in range(m_S):
            for R in range(m_R):
                out = fs[p](L, S, R)
                mark = "*" if out != S else " "
                row.append(f"{out}{mark}")
        lbl = f"  L={L}:"
        # Group by S
        for S in range(m_S):
            entries = [f"f({L},{S},{R})={fs[p](L,S,R)}{'*' if fs[p](L,S,R)!=S else ' '}" for R in range(m_R)]
            print(f"    {' '.join(entries)}")


def compare_tables(fs_list, p_types, ms_list, n_list):
    """Compare same processor TYPE across different n values."""
    for ptype in p_types:
        print(f"\n{'='*70}")
        print(f"Processor type: {ptype}")
        print(f"{'='*70}")
        for idx, nv in enumerate(n_list):
            fs = fs_list[idx]
            ms = ms_list[idx]
            n = nv
            if ptype == "P1":
                p = 1
            elif ptype == "P_{n-2}":
                p = n - 2
            elif ptype == "interior":
                p = n // 2
            else:
                continue

            m_L = ms[(p - 1) % n]
            m_S = ms[p]
            m_R = ms[(p + 1) % n]
            print(f"\n  n={nv}, P{p} (m_L={m_L}, m_S={m_S}, m_R={m_R}):")
            for S in range(m_S):
                for L in range(m_L):
                    entries = []
                    for R in range(m_R):
                        out = fs[p](L, S, R)
                        mark = "*" if out != S else " "
                        entries.append(f"f({L},{S},{R})={out}{mark}")
                    print(f"    {' '.join(entries)}")


def main():
    n_values = [5, 6, 7, 8]
    systems = []
    for nv in n_values:
        ms, fs, comp, cycle, movers = build_system_general(nv)
        systems.append((ms, fs, comp))

    # Print P1 tables across n
    print("P1 (ternary adjacent to binary bottom) across n values:")
    for idx, nv in enumerate(n_values):
        ms, fs, comp = systems[idx]
        n = nv
        p = 1
        m_L = ms[0]  # binary
        m_S = ms[1]  # ternary
        m_R = ms[2]  # ternary
        print(f"\n  n={nv}, P1 (m_L={m_L}, m_S={m_S}, m_R={m_R}):")
        for L in range(m_L):
            for S in range(m_S):
                entries = []
                for R in range(m_R):
                    out = fs[p](L, S, R)
                    mark = "*" if out != S else " "
                    entries.append(f"{out}{mark}")
                print(f"    L={L},S={S}: [{','.join(entries)}]")

    # Print interior middle tables (only 3x3x3)
    print("\n\nInterior middle (3x3x3) across n values:")
    for idx, nv in enumerate(n_values):
        ms, fs, comp = systems[idx]
        n = nv
        p = n // 2  # truly interior
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        if m_L != 3 or m_R != 3:
            print(f"  n={nv}: P{p} not 3x3x3, skipping")
            continue
        print(f"\n  n={nv}, P{p} (m_L={m_L}, m_S={m_S}, m_R={m_R}):")
        for L in range(m_L):
            for S in range(m_S):
                entries = []
                for R in range(m_R):
                    out = fs[p](L, S, R)
                    mark = "*" if out != S else " "
                    entries.append(f"{out}{mark}")
                print(f"    L={L},S={S}: [{','.join(entries)}]")

    # Print P_{n-2} tables
    print("\n\nP_{n-2} (ternary adjacent to binary top) across n values:")
    for idx, nv in enumerate(n_values):
        ms, fs, comp = systems[idx]
        n = nv
        p = n - 2
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[n - 1]  # binary
        print(f"\n  n={nv}, P{n-2} (m_L={m_L}, m_S={m_S}, m_R={m_R}):")
        for L in range(m_L):
            for S in range(m_S):
                entries = []
                for R in range(m_R):
                    out = fs[p](L, S, R)
                    mark = "*" if out != S else " "
                    entries.append(f"{out}{mark}")
                print(f"    L={L},S={S}: [{','.join(entries)}]")

    # Check if interior tables are identical across n
    print("\n\nAre interior (3x3x3) tables identical across n?")
    ref_table = None
    ref_n = None
    for idx, nv in enumerate(n_values):
        ms, fs, comp = systems[idx]
        n = nv
        p = n // 2
        m_L = ms[(p - 1) % n]
        m_R = ms[(p + 1) % n]
        if m_L != 3 or m_R != 3:
            continue
        table = {}
        for L in range(3):
            for S in range(3):
                for R in range(3):
                    table[(L, S, R)] = fs[p](L, S, R)
        if ref_table is None:
            ref_table = table
            ref_n = nv
        else:
            match = all(table[k] == ref_table[k] for k in table)
            print(f"  n={nv} vs n={ref_n}: {'IDENTICAL' if match else 'DIFFER'}")
            if not match:
                for k in sorted(table):
                    if table[k] != ref_table[k]:
                        print(f"    {k}: n={ref_n}→{ref_table[k]}, n={nv}→{table[k]}")

    # Similarly for P1 and P_{n-2}
    print("\nAre P1 (2x3x3) tables identical across n?")
    ref = None
    for idx, nv in enumerate(n_values):
        ms, fs, comp = systems[idx]
        table = {}
        for L in range(2):
            for S in range(3):
                for R in range(3):
                    table[(L, S, R)] = fs[1](L, S, R)
        if ref is None:
            ref = table
        else:
            match = all(table[k] == ref[k] for k in table)
            print(f"  n={nv}: {'IDENTICAL' if match else 'DIFFER'}")

    print("\nAre P_{n-2} (3x3x2) tables identical across n?")
    ref = None
    for idx, nv in enumerate(n_values):
        ms, fs, comp = systems[idx]
        n = nv
        p = n - 2
        table = {}
        for L in range(3):
            for S in range(3):
                for R in range(2):
                    table[(L, S, R)] = fs[p](L, S, R)
        if ref is None:
            ref = table
        else:
            match = all(table[k] == ref[k] for k in table)
            print(f"  n={nv}: {'IDENTICAL' if match else 'DIFFER'}")


if __name__ == "__main__":
    main()
