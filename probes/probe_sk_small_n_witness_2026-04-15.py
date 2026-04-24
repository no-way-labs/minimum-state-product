#!/usr/bin/env python3
"""Run SK on the M_5..M_8 witness cycles — hypothesis 3 probe.

Parses `lean/LeanMn/SmallN/Defs.lean` for the explicit witness systems
(ms, TransFn, good cycle) for n = 5..8 and runs the sink-kernel
computation on each witness's ACTUAL good cycle (not sweep/bounce
candidates).

Research questions (from sk_small_n_discovery_2026-04-15.md §Hypothesis 3):

  Q1. What does each M_n witness's good cycle look like?
      - cycle length
      - mover sequence
      - per-position value distribution (does the quaternary visit
        all 4 states, or is one hidden?)

  Q2. Does SK detect the witness cycle as valid? |SK| must be 0 on
      the witness's actual good cycle. If |SK| > 0, SK is inconsistent
      with validity and the whole approach is in trouble.

  Q3. How does the witness cycle compare to the CLB wavefront
      (n ≥ 9: ms = (2, 3^(n-2), 2), L_0=n, L_1(j)=2(n-2-j),
      L_2(j)=2(j+1), cycle length 3n-2)?
"""
from __future__ import annotations
import re
from pathlib import Path
from itertools import product as iproduct
from collections import defaultdict, Counter


DEFS_LEAN = Path(__file__).resolve().parent.parent / "lean" / "LeanMn" / "SmallN" / "Defs.lean"


# ---------- parser ----------


def parse_state_counts(src: str, wn: str) -> tuple[int, ...]:
    """Parse `def wnM (i : Fin k) : Nat := match i.val with | j => v | _ => v`."""
    pat = rf"def {wn}M \(i : Fin (\d+)\) : Nat :=\s*match i\.val with(.*?)(?=\n\n|\ndef )"
    m = re.search(pat, src, re.DOTALL)
    if not m:
        raise ValueError(f"{wn}M not found")
    n = int(m.group(1))
    body = m.group(2)
    ms = [None] * n
    default = None
    for line in body.strip().split("\n"):
        line = line.strip()
        mline = re.match(r"\|\s*(\d+)\s*=>\s*(\d+)", line)
        if mline:
            ms[int(mline.group(1))] = int(mline.group(2))
            continue
        mdef = re.match(r"\|\s*_\s*=>\s*(\d+)", line)
        if mdef:
            default = int(mdef.group(1))
    for i in range(n):
        if ms[i] is None:
            assert default is not None
            ms[i] = default
    return tuple(ms)


def parse_trans_table(src: str, wn: str, i: int) -> dict[tuple[int, int, int], int]:
    """Parse `private def wnPi (L S R : Nat) : Nat := match L, S, R with | a,b,c => v | _,_,_ => 0`."""
    pat = rf"private def {wn}P{i} \(L S R : Nat\) : Nat :=\s*match L, S, R with(.*?)(?=\nprivate def|\ndef {wn}OutVal|\ndef {wn}Cfg)"
    m = re.search(pat, src, re.DOTALL)
    if not m:
        raise ValueError(f"{wn}P{i} not found")
    body = m.group(1)
    table = {}
    default = 0
    for line in body.strip().split("\n"):
        line = line.strip()
        mline = re.match(r"\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*(\d+)", line)
        if mline:
            L, S, R, V = map(int, mline.groups())
            table[(L, S, R)] = V
            continue
        mdef = re.match(r"\|\s*_,\s*_,\s*_\s*=>\s*(\d+)", line)
        if mdef:
            default = int(mdef.group(1))
    return table, default


def parse_cfg_bases(src: str, wn: str, n: int) -> list[int]:
    """Parse wnCfgOfCode divisors to recover per-position base used in the encoding.

    The file writes `⟨(k / B_i) % m_i, _⟩` for each position i, where B_0=1 and
    B_i = product of m_0..m_{i-1}. We extract the bases so we can decode codes
    without reimplementing the encoding.
    """
    pat = rf"def {wn}CfgOfCode \(k : Nat\) : Config {wn}Spec :=\s*{wn}Cfg(.*?)(?=\ndef |\nend|\Z)"
    m = re.search(pat, src, re.DOTALL)
    if not m:
        raise ValueError(f"{wn}CfgOfCode not found")
    body = m.group(1)
    bases = []
    for match in re.finditer(r"⟨\(k / (\d+)\) % (\d+), by omega⟩", body):
        bases.append(int(match.group(1)))
    assert len(bases) == n, f"expected {n} bases, got {len(bases)}"
    return bases


def parse_cycle_codes(src: str, wn: str) -> list[int]:
    pat = rf"def {wn}GoodCycleCodes : List Nat := \[([^\]]+)\]"
    m = re.search(pat, src)
    if not m:
        raise ValueError(f"{wn}GoodCycleCodes not found")
    return [int(x.strip()) for x in m.group(1).split(",")]


def decode(code: int, bases: list[int], ms: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((code // bases[i]) % ms[i] for i in range(len(ms)))


def make_trans(tables: list[tuple[dict, int]], n: int):
    def f(i, L, S, R):
        tbl, default = tables[i]
        return tbl.get((L, S, R), default)
    return f


# ---------- SK analysis ----------


def cycle_mover_sequence(cycle: list[tuple[int, ...]], n: int) -> list[int]:
    out = []
    L = len(cycle)
    for k in range(L):
        a = cycle[k]
        b = cycle[(k + 1) % L]
        diffs = [i for i in range(n) if a[i] != b[i]]
        if len(diffs) != 1:
            raise ValueError(f"cycle step {k} has {len(diffs)} diffs: {a} -> {b}")
        out.append(diffs[0])
    return out


def build_det_from_cycle(cycle: list[tuple[int, ...]], n: int) -> dict:
    """Build the observed-transition dictionary used by SK.

    At each cycle step, the mover's (p, L, S, R) -> S' is committed, and
    every non-mover's (i, L, S, R) -> S is committed (no change).
    """
    det = {}
    L = len(cycle)
    for k in range(L):
        c = cycle[k]
        c_next = cycle[(k + 1) % L]
        p = next(i for i in range(n) if c[i] != c_next[i])
        for i in range(n):
            Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
            key = (i, Li, Si, Ri)
            val = c_next[i] if i == p else Si
            if key in det and det[key] != val:
                raise ValueError(f"det conflict at step {k}, key {key}: {det[key]} vs {val}")
            det[key] = val
    return det


def build_forced_graph(ms: tuple[int, ...], n: int, det: dict, good_set: set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]
                nc = tuple(nc)
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


# ---------- verifier (sanity check) ----------


def verify_cycle_as_good(cycle: list, n: int, ms: tuple, trans) -> dict:
    """Check closure, uniqueness, fairness, and convergence (bad DAG via sink-kernel)."""
    cycle_set = set(cycle)
    L = len(cycle)

    def priv(c):
        out = []
        for i in range(n):
            Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
            if trans(i, Li, Si, Ri) != Si:
                out.append(i)
        return out

    unique = all(len(priv(c)) == 1 for c in cycle)

    closure_ok = True
    movers = []
    for k in range(L):
        c = cycle[k]
        p = priv(c)[0]
        movers.append(p)
        Li = c[(p - 1) % n]; Si = c[p]; Ri = c[(p + 1) % n]
        c_next = list(c); c_next[p] = trans(p, Li, Si, Ri); c_next = tuple(c_next)
        if c_next != cycle[(k + 1) % L]:
            closure_ok = False
            break

    fair = set(movers) == set(range(n))
    return {"unique": unique, "closure": closure_ok, "fair": fair, "movers": movers}


# ---------- per-witness report ----------


def analyze_witness(src: str, n: int):
    wn = f"w{n}"
    ms = parse_state_counts(src, wn)
    tables = [parse_trans_table(src, wn, i) for i in range(n)]
    bases = parse_cfg_bases(src, wn, n)
    codes = parse_cycle_codes(src, wn)
    cycle = [decode(c, bases, ms) for c in codes]
    trans = make_trans(tables, n)

    print(f"\n{'=' * 90}")
    print(f"n={n}  ms={ms}  product={_prod(ms)}  cycle length={len(cycle)}")
    print(f"{'=' * 90}")

    verify = verify_cycle_as_good(cycle, n, ms, trans)
    print(f"  verify: unique_priv={verify['unique']}  closure={verify['closure']}  fair={verify['fair']}")
    if not (verify['unique'] and verify['closure'] and verify['fair']):
        print("  !!! verify FAILED — parser or witness bug !!!")
        return

    movers = verify['movers']
    print(f"  mover sequence ({len(movers)}): {movers}")

    fire_counts = Counter(movers)
    print(f"  firings per processor:")
    for i in range(n):
        print(f"    P{i} (m={ms[i]}): {fire_counts[i]}x  ratio = {fire_counts[i] / ms[i]:.2f}x m_i")

    print(f"  per-position value distribution:")
    for i in range(n):
        vals = Counter(c[i] for c in cycle)
        dist = {v: vals[v] for v in range(ms[i])}
        print(f"    P{i} (m={ms[i]}): {dist}")

    det = build_det_from_cycle(cycle, n)
    good_set = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det, good_set)
    sk, rounds = sink_kernel(ng, adj)
    print(f"  forced graph on non-good: {len(ng)} nodes, {sum(len(v) for v in adj.values())} edges")
    print(f"  sink-kernel: |SK| = {len(sk)}  (rounds={rounds})")
    if len(sk) == 0:
        print("  ✓ SK = 0 — consistent with validity")
    else:
        print(f"  ✗ SK > 0 — INCONSISTENT with validity, SK definition or witness parse is wrong")
        sample = list(sk)[:5]
        print(f"    sample SK members: {sample}")

    return {"n": n, "ms": ms, "cycle_len": len(cycle), "fire_counts": dict(fire_counts), "sk_size": len(sk)}


def _prod(xs):
    p = 1
    for x in xs:
        p *= x
    return p


# ---------- CLB comparison ----------


def clb_wavefront_report(n: int):
    """Print the CLB n-generic cycle structure for comparison.

    CLB: ms = (2, 3, 3, ..., 3, 2), cycle length 3n-2, good configs n^2-2n+8,
    per-position distribution L_0=n, L_1(j)=2(n-2-j), L_2(j)=2(j+1).
    """
    cycle_len = 3 * n - 2
    good_count = n * n - 2 * n + 8
    print(f"\n  CLB reference for n={n}:")
    print(f"    ms = (2, 3^({n-2}), 2)  product = {2 * 3**(n-2) * 2}")
    print(f"    cycle length = {cycle_len}, good configs = {good_count}")
    print(f"    ternary L_v distribution (j = position index from P_1):")
    for j in range(n - 2):
        L0 = n
        L1 = 2 * (n - 2 - j)
        L2 = 2 * (j + 1)
        total = L0 + L1 + L2
        print(f"      P{j+1}: L0={L0} L1={L1} L2={L2} (total={total})")


def main():
    print("=" * 90)
    print("SK on M_n witness cycles — hypothesis 3 (small-n quaternary structure)")
    print("=" * 90)

    src = DEFS_LEAN.read_text()

    results = []
    for n in (5, 6, 7, 8):
        r = analyze_witness(src, n)
        if r:
            results.append(r)

    print("\n" + "=" * 90)
    print("SUMMARY TABLE")
    print("=" * 90)
    print(f"{'n':<4} {'ms':<32} {'cycle_len':<10} {'|SK|':<8}")
    for r in results:
        print(f"{r['n']:<4} {str(r['ms']):<32} {r['cycle_len']:<10} {r['sk_size']:<8}")

    print("\n" + "=" * 90)
    print("CLB wavefront structure for comparison (n ≥ 9)")
    print("=" * 90)
    for n in (5, 6, 7, 8, 9):
        clb_wavefront_report(n)


if __name__ == "__main__":
    main()
