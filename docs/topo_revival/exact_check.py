#!/usr/bin/env python3
"""Exact incidence-balance post-check for the circulation detector.

The circulation LP of \\S4 is rational-valued by construction: the
oriented incidence matrix $B$ of the lifted graph $(V_{\\mathrm{lift}},
E_{\\mathrm{lift}})$ has entries in $\\{-1, 0, +1\\}$, and the
normalisation $1^\\top \\Phi = 1$ is rational, so every vertex of the
feasible polytope is a rational point.

The reported implementation solves the LP with a floating-point simplex
(\\texttt{scipy.optimize.linprog}, HiGHS).  This tool reads the reported
float $\\Phi$, rationalises it with \\texttt{fractions.Fraction}, and
verifies *exactly* that

    $B^\\top \\Phi = 0$,    $\\sum_e \\Phi_e = 1$,    $\\Phi_e \\ge 0$
    for every edge $e$.

A reported feasibility verdict is accepted only if all three hold
exactly on the rationalised $\\Phi$.  A failure signals either that
the reported solution is a degenerate/ill-conditioned vertex, or that
the float-simplex verdict is not trustworthy for that record.
Zero-flow edges are allowed and common.

Usage:
    python3 exact_check.py feasibility_certificates.json
    python3 exact_check.py --self-test

Certificate JSON schema (one bundle, many records):

  {
    "n_records": int,
    "records": [
      {
        "name":     str,              # identifier, e.g. "w5" or "sub_n7_k3"
        "n":        int,              # ring size
        "ms":       [int, ...],       # multiset / state vector
        "L":        int,              # cycle length
        "nV_lift":  int,              # |V_lift|  (optional; inferred from edges)
        "nE_lift":  int,              # |E_lift|  (optional; inferred)
        "V_lift":   [[k,q,a], ...],   # vertex triples  (not used by verifier)
        "E_lift":   [[s,t], ...],     # directed edges (source, target) indices
        "Phi":      [...]             # edge flow; float, or [num, den] pair
      },
      ...
    ]
  }

Companion tool: farkas_verify.py in the same directory handles the
complementary (infeasible) case, re-checking the Farkas topo-order
certificate.

Exit code = number of records that fail exact verification.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from typing import List, Sequence, Tuple


# A denominator ceiling large enough to recover any LP-simplex drift from
# truly rational coordinates (the LP's rational denominators grow at
# most polynomially in |V_lift|, so 10^12 is comfortably safe).
DENOM_CEILING = 10 ** 12


def rationalise(phi: Sequence) -> List[Fraction]:
    """Convert raw Phi entries to exact Fractions.

    Accepts a list whose entries are either floats, integers, Fractions,
    or [num, den] pairs (preferred for bit-exact round-trip).  Floats are
    snapped to the nearest rational with denominator <= DENOM_CEILING.
    """
    out: List[Fraction] = []
    for v in phi:
        if isinstance(v, Fraction):
            out.append(v)
        elif isinstance(v, (list, tuple)) and len(v) == 2:
            num, den = v
            out.append(Fraction(int(num), int(den)))
        elif isinstance(v, int):
            out.append(Fraction(v, 1))
        else:
            out.append(Fraction(float(v)).limit_denominator(DENOM_CEILING))
    return out


def verify(num_vertices: int,
           edges: Sequence[Tuple[int, int]],
           phi: Sequence[Fraction]) -> dict:
    """Exact check of B^T Phi = 0, sum Phi = 1, Phi >= 0.

    B is the oriented incidence matrix of (V, E):  B[v,e] = -1 if v is
    edge e's source, +1 if v is edge e's target, 0 otherwise.  Then
    (B^T Phi)[v] = (inflow at v) - (outflow at v).
    """
    if len(phi) != len(edges):
        return {"pass": False,
                "reason": f"|Phi|={len(phi)} != |E|={len(edges)}"}

    negatives = [(i, phi[i]) for i, x in enumerate(phi) if x < 0]
    if negatives:
        return {"pass": False,
                "reason": f"negative flow on {len(negatives)} edges",
                "sample": [(i, str(x)) for (i, x) in negatives[:3]]}

    total = sum(phi, Fraction(0))
    if total != 1:
        return {"pass": False, "reason": f"sum Phi = {total} != 1"}

    balance = [Fraction(0)] * num_vertices
    for (s, t), phi_e in zip(edges, phi):
        balance[s] -= phi_e
        balance[t] += phi_e
    imbalanced = [(v, balance[v]) for v, b in enumerate(balance) if b != 0]
    if imbalanced:
        return {"pass": False,
                "reason": f"incidence-imbalance at {len(imbalanced)} vertices",
                "sample": [(v, str(b)) for (v, b) in imbalanced[:3]]}

    return {"pass": True}


def check_record(rec: dict) -> dict:
    edges = [(int(s), int(t)) for (s, t) in rec["E_lift"]]
    if "nV_lift" in rec:
        nV = int(rec["nV_lift"])
    else:
        nV = max((max(s, t) for (s, t) in edges), default=-1) + 1
    phi = rationalise(rec["Phi"])
    result = verify(nV, edges, phi)
    result["name"] = rec.get("name", "?")
    result["n"] = rec.get("n")
    result["L"] = rec.get("L")
    result["nV"] = nV
    result["nE"] = len(edges)
    return result


def _self_test() -> int:
    """Trivial 3-vertex triangle circulation, Phi = (1/3, 1/3, 1/3)."""
    rec = {
        "name": "self-test-triangle",
        "n": 0, "ms": [], "L": 3,
        "nV_lift": 3, "nE_lift": 3,
        "V_lift": [[0, 0, 0], [0, 1, 0], [0, 2, 0]],
        "E_lift": [[0, 1], [1, 2], [2, 0]],
        "Phi": [1 / 3, 1 / 3, 1 / 3],
    }
    r = check_record(rec)
    status = "PASS" if r["pass"] else "FAIL"
    print(f"  [{status}] {r['name']}: |V|={r['nV']} |E|={r['nE']}")
    if not r["pass"]:
        print(f"         reason: {r['reason']}")

    # And a deliberate negative-imbalance case (source-only edge) to
    # exercise the failure path.
    bad = {
        "name": "self-test-imbalanced",
        "n": 0, "ms": [], "L": 2,
        "nV_lift": 2, "nE_lift": 1,
        "V_lift": [[0, 0, 0], [0, 1, 0]],
        "E_lift": [[0, 1]],
        "Phi": [1.0],
    }
    r2 = check_record(bad)
    expected_fail = not r2["pass"]
    status2 = "PASS" if not r2["pass"] else "FAIL"  # failure is the expected outcome
    print(f"  [{status2}] {r2['name']} (expected to fail incidence balance)")
    if r2["pass"]:
        print("         unexpected: a source-only single edge passed verify")

    return 0 if (r["pass"] and expected_fail) else 1


def main(argv: List[str]) -> int:
    if len(argv) >= 2 and argv[1] == "--self-test":
        return _self_test()
    if len(argv) < 2:
        sys.stderr.write(
            "Usage: python3 exact_check.py <feasibility_certificates.json>\n"
            "       python3 exact_check.py --self-test\n")
        return 2

    with open(argv[1]) as f:
        bundle = json.load(f)
    records = bundle.get("records", [])

    n_pass = 0
    n_fail = 0
    for rec in records:
        r = check_record(rec)
        if r["pass"]:
            print(f"  [PASS] {r['name']} n={r['n']} L={r['L']} "
                  f"|V|={r['nV']} |E|={r['nE']}: exact rational Phi "
                  f"satisfies B^T Phi = 0, sum Phi = 1, Phi >= 0.")
            n_pass += 1
        else:
            print(f"  [FAIL] {r['name']} n={r['n']}: {r['reason']}")
            for item in r.get("sample", []):
                print(f"           {item}")
            n_fail += 1

    print()
    print(f"  {n_pass} pass, {n_fail} fail, {len(records)} total")
    return n_fail


if __name__ == "__main__":
    sys.exit(main(sys.argv))
