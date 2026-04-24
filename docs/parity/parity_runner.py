#!/usr/bin/env python3
"""Strengthening #3 — Python / Lean parity runner.

For each stored small-n witness with both a Python and a Lean encoding,
this runner:

  (a) loads the Python (ms, rules) from docs/verify_witnesses.py,
  (b) parses the Lean (ms, rules) from lean/LeanMn/SmallN/Defs.lean,
  (c) asserts the two encodings agree rule-entry by rule-entry,
  (d) independently runs Python `verify_system` on each side
      (returning `valid=True` for all witnesses),
  (e) optionally runs `lake build LeanMn.SmallN.Defs` to verify the
      Lean theorems still compile (gated by --lake),
  (f) runs negative controls: for each witness, flip a single move-entry
      in a copy of the rule table, assert `verify_system` returns
      `valid=False`,
  (g) exits nonzero on any disagreement.

Scope. Covers the n ∈ {4, 5, 6, 7, 8} witnesses that have both Python
and Lean encodings with valid Lean validity proofs (`wN_valid`). The
n = 4 optimal witness (ms=(2,2,2,3), product 24) has only a Lean
encoding; see --include-w4opt to synthesize a Python encoding from the
Lean match arms and parity-check them within the Lean-derived copy.
n = 9, 10 CUP-2 / CLB parity is documented as a pending follow-up.

Output:
  - JSON report at --output (default: parity_report.json).
  - Stdout: per-witness PASS/FAIL rows and summary.

Exit code: 0 if every witness passes all checks; nonzero = number of
failures (counts disagreements, verify_system mismatches, and control
failures).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import OrderedDict
from itertools import product as iproduct

HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "claude"))
DOCS_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "docs"))
LEAN_ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", "lean"))
LEAN_SMALLN_DEFS = os.path.join(LEAN_ROOT, "LeanMn", "SmallN", "Defs.lean")

sys.path.insert(0, CLAUDE_DIR)
sys.path.insert(0, DOCS_DIR)

from verifier import verify_system  # type: ignore
import verify_witnesses as vw  # type: ignore


# ----------------------------------------------------------------------
# Lean parser — extract (ms, rules) from SmallN/Defs.lean
# ----------------------------------------------------------------------

def _read_defs() -> str:
    with open(LEAN_SMALLN_DEFS, "r") as f:
        return f.read()


def _parse_match_nat_body(body: str) -> dict:
    """Parse match arms of form `| l, s, r => v` (optionally `| _, _, _ => v`)
    into a dict keyed by integer triples, plus a `'default'` key. Expects
    `match L, S, R with` body only — caller strips the preamble."""
    result = {}
    default = None
    for line in body.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        m = re.match(
            r"\|\s*([0-9]+|_)\s*,\s*([0-9]+|_)\s*,\s*([0-9]+|_)\s*=>\s*([0-9]+)",
            line,
        )
        if not m:
            continue
        l, s, r, v = m.groups()
        if l == "_" and s == "_" and r == "_":
            default = int(v)
            continue
        if "_" in (l, s, r):
            continue
        result[(int(l), int(s), int(r))] = int(v)
    return {"explicit": result, "default": default}


def _parse_wn_m(text: str, wN_prefix: str, n: int) -> list:
    """Parse `def {wN_prefix}M (i : Fin n) : Nat := match i.val with | k => m_k`."""
    pat = re.compile(
        rf"def {re.escape(wN_prefix)}M \(i : Fin \d+\) : Nat :=\s*match i\.val with\s*(.*?)\n\n",
        re.DOTALL,
    )
    m = pat.search(text)
    if not m:
        raise RuntimeError(f"{wN_prefix}M not found")
    body = m.group(1)
    result = [None] * n
    default = None
    for line in body.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        mm = re.match(r"\|\s*([0-9]+|_)\s*=>\s*([0-9]+)", line)
        if not mm:
            continue
        k, v = mm.groups()
        if k == "_":
            default = int(v)
        else:
            result[int(k)] = int(v)
    for i in range(n):
        if result[i] is None:
            if default is None:
                raise RuntimeError(f"{wN_prefix}M has no value for i={i}")
            result[i] = default
    return result


def _parse_wn_pk(text: str, wN_prefix: str, k: int) -> dict:
    """Parse `private def {wN_prefix}P{k} (L S R : Nat) : Nat := match L, S, R with ...`.

    Returns the dict plus a default.
    """
    pat = re.compile(
        rf"private def {re.escape(wN_prefix)}P{k} \(L S R : Nat\) : Nat :=\s*match L, S, R with\s*(.*?)(?=\n\nprivate def |\n\ndef |\n\n/-! |\ntheorem |\n\Z)",
        re.DOTALL,
    )
    m = pat.search(text)
    if not m:
        raise RuntimeError(f"{wN_prefix}P{k} not found")
    return _parse_match_nat_body(m.group(1))


def extract_lean_witness(wN_prefix: str, n: int) -> tuple:
    """Extract (ms, rules) from Lean definitions in SmallN/Defs.lean.

    `rules` is a list of n dicts; each dict maps (L, S, R) → out for every
    reachable triple under the ms state counts (unspecified triples are
    filled with the Lean `match` default, i.e. 0).
    """
    text = _read_defs()
    ms = _parse_wn_m(text, wN_prefix, n)
    rules = []
    for i in range(n):
        raw = _parse_wn_pk(text, wN_prefix, i)
        explicit, default = raw["explicit"], raw["default"]
        d = {}
        L_max = ms[(i - 1) % n]
        S_max = ms[i]
        R_max = ms[(i + 1) % n]
        for L in range(L_max):
            for S in range(S_max):
                for R in range(R_max):
                    key = (L, S, R)
                    if key in explicit:
                        d[key] = explicit[key]
                    elif default is not None:
                        d[key] = default
                    else:
                        raise RuntimeError(
                            f"{wN_prefix}P{i}: no value for {key} and no default"
                        )
        rules.append(d)
    return tuple(ms), tuple(rules)


# ----------------------------------------------------------------------
# Verification + negative control
# ----------------------------------------------------------------------

def _make_fs(rules):
    def mkf(rule_dict):
        def f(L, S, R):
            return rule_dict[(L, S, R)]
        return f
    return [mkf(r) for r in rules]


def run_verify(ms, rules) -> dict:
    fs = _make_fs(rules)
    v = verify_system(list(ms), fs, verbose=False)
    return {"valid": bool(v["valid"]),
            "details": {k: v[k] for k in v if k != "valid"}}


def negative_control(ms, rules):
    """Flip a single move-entry and verify the mutated system fails."""
    # Find a privileged (move) entry: rule[i][(L,S,R)] != S
    mutated = [dict(r) for r in rules]
    target = None
    for i, rd in enumerate(mutated):
        for key, out in rd.items():
            L, S, R = key
            if out != S:
                # Flip to something != original
                flipped = S
                mutated[i][key] = flipped
                target = (i, key, out, flipped)
                break
        if target is not None:
            break
    if target is None:
        return {"applied": False, "reason": "no move entry found"}
    v = run_verify(ms, mutated)
    return {"applied": True, "target": target, "mutated_valid": v["valid"],
            "expect": False}


def rule_table_hash(ms, rules) -> str:
    h = hashlib.sha256()
    h.update(json.dumps(list(ms)).encode())
    for rd in rules:
        for key in sorted(rd.keys()):
            h.update(f"{key}={rd[key]};".encode())
        h.update(b"||")
    return h.hexdigest()[:16]


# ----------------------------------------------------------------------
# Runner
# ----------------------------------------------------------------------

WITNESSES = [
    {"name": "w4",    "n": 4, "lean_prefix": "w4",    "py_fn": "witness_n4",
     "note": "ms=(2,2,2,4), product 32; NOT the exact M_4 — w4opt is exact."},
    {"name": "w4opt", "n": 4, "lean_prefix": "w4opt", "py_fn": "witness_n4opt",
     "note": "ms=(2,2,2,3), product 24 = M_4 (sharp). Python encoding is "
             "`witness_n4opt` (added under strengthening #3)."},
    {"name": "w5",    "n": 5, "lean_prefix": "w5",    "py_fn": "witness_n5",
     "note": "M_5=96 sharp"},
    {"name": "w6",    "n": 6, "lean_prefix": "w6",    "py_fn": "witness_n6",
     "note": "M_6=288 sharp"},
    {"name": "w7",    "n": 7, "lean_prefix": "w7",    "py_fn": "witness_n7",
     "note": "M_7=864 sharp"},
    {"name": "w8",    "n": 8, "lean_prefix": "w8",    "py_fn": "witness_n8",
     "note": "M_8=2592 sharp"},
]


def compare_rules(py_rules, lean_rules, ms) -> dict:
    """Element-wise comparison of rule tables. Assumes both cover every
    (L, S, R) within the ms bounds."""
    n = len(ms)
    diffs = []
    for i in range(n):
        Lm = ms[(i - 1) % n]
        Sm = ms[i]
        Rm = ms[(i + 1) % n]
        for L in range(Lm):
            for S in range(Sm):
                for R in range(Rm):
                    key = (L, S, R)
                    py_v = py_rules[i].get(key)
                    ln_v = lean_rules[i].get(key)
                    if py_v is None or ln_v is None or py_v != ln_v:
                        diffs.append({
                            "i": i, "key": list(key),
                            "py": py_v, "lean": ln_v,
                        })
    return {"n_diffs": len(diffs), "diffs": diffs[:20]}


def run_one(entry: dict) -> dict:
    name = entry["name"]
    n = entry["n"]
    result = {"name": name, "n": n, "note": entry["note"],
              "steps": OrderedDict()}

    # 1. Lean encoding
    try:
        lean_ms, lean_rules = extract_lean_witness(entry["lean_prefix"], n)
        result["steps"]["lean_parse"] = {
            "ok": True, "ms": list(lean_ms),
            "rule_table_hash": rule_table_hash(lean_ms, lean_rules),
        }
    except Exception as e:
        result["steps"]["lean_parse"] = {"ok": False, "error": str(e)}
        return result

    # 2. Python encoding (if available)
    py_ms, py_rules = None, None
    if entry["py_fn"]:
        fn = getattr(vw, entry["py_fn"], None)
        if fn is None:
            result["steps"]["py_load"] = {
                "ok": False, "error": f"{entry['py_fn']} not found"}
            return result
        sc, rules = fn()
        py_ms, py_rules = tuple(sc), tuple(rules)
        result["steps"]["py_load"] = {
            "ok": True, "ms": list(py_ms),
            "rule_table_hash": rule_table_hash(py_ms, py_rules),
        }
    else:
        result["steps"]["py_load"] = {"ok": True, "skipped": "Lean-only"}

    # 3. Parity check
    if py_ms is not None:
        if tuple(py_ms) != tuple(lean_ms):
            result["steps"]["parity"] = {
                "ok": False, "py_ms": list(py_ms), "lean_ms": list(lean_ms)}
        else:
            parity = compare_rules(py_rules, lean_rules, lean_ms)
            result["steps"]["parity"] = {
                "ok": parity["n_diffs"] == 0, **parity,
                "py_hash": rule_table_hash(py_ms, py_rules),
                "lean_hash": rule_table_hash(lean_ms, lean_rules),
            }
    else:
        result["steps"]["parity"] = {"ok": True, "skipped": "no Python encoding"}

    # 4. Python verify_system on Lean encoding
    vlean = run_verify(lean_ms, lean_rules)
    result["steps"]["verify_lean_encoding"] = {
        "ok": vlean["valid"] is True, "valid": vlean["valid"],
        "details": vlean["details"],
    }

    # 5. Python verify_system on Python encoding (if available)
    if py_ms is not None:
        vpy = run_verify(py_ms, py_rules)
        result["steps"]["verify_py_encoding"] = {
            "ok": vpy["valid"] is True, "valid": vpy["valid"],
            "details": vpy["details"],
        }

    # 6. Negative control on Lean encoding
    nc = negative_control(lean_ms, lean_rules)
    result["steps"]["negative_control"] = {
        "ok": (nc.get("applied", False) and nc["mutated_valid"] is False),
        **nc,
    }

    return result


# ----------------------------------------------------------------------
# CUP-2 universal tables parity (n-independent 5-table implementation)
# ----------------------------------------------------------------------

LEAN_TABLES_FILE = os.path.join(LEAN_ROOT, "LeanMn", "Tables.lean")


def parse_lean_toplevel_match(fn_name: str) -> dict:
    """Parse `def fn_name : Nat → Nat → Nat → Nat | a, b, c => v` from
    Tables.lean. Returns dict mapping (a, b, c) → v and a default."""
    with open(LEAN_TABLES_FILE, "r") as f:
        text = f.read()
    pat = re.compile(
        rf"def {re.escape(fn_name)} : Nat → Nat → Nat → Nat\s*(.*?)(?=\n\ndef |\n\nlemma |\n\Z)",
        re.DOTALL,
    )
    m = pat.search(text)
    if not m:
        raise RuntimeError(f"{fn_name} not found in Tables.lean")
    return _parse_match_nat_body(m.group(1))


def run_cup2_tables_parity() -> dict:
    """Compare Lean's 5 universal tables to Python's T_bot/T_low/T_mid/T_high/T_top."""
    sys.path.insert(0, CLAUDE_DIR)
    import cup2_theorem as cup2  # type: ignore

    lean_names = {
        "bot":  "TBotVal",
        "low":  "TLowVal",
        "mid":  "TMidVal",
        "high": "THighVal",
        "top":  "TTopVal",
    }
    py_tables = {
        "bot":  cup2.T_bot,
        "low":  cup2.T_low,
        "mid":  cup2.T_mid,
        "high": cup2.T_high,
        "top":  cup2.T_top,
    }
    # Domain for each table, dictated by the local ms pattern around the
    # position that uses it:
    #   bot   : i=0, ms[-1]=2, ms[0]=2, ms[1]=3 → (L<2, S<2, R<3)
    #   low   : i=1, ms[0]=2, ms[1]=3, ms[2]=3 → (L<2, S<3, R<3)
    #   mid   : interior, 3, 3, 3              → (L<3, S<3, R<3)
    #   high  : i=n-2, 3, 3, 2                 → (L<3, S<3, R<2)
    #   top   : i=n-1, 3, 2, 2                 → (L<3, S<2, R<2)
    domains = {
        "bot":  ((0, 2), (0, 2), (0, 3)),
        "low":  ((0, 2), (0, 3), (0, 3)),
        "mid":  ((0, 3), (0, 3), (0, 3)),
        "high": ((0, 3), (0, 3), (0, 2)),
        "top":  ((0, 3), (0, 2), (0, 2)),
    }
    results = {}
    total_diffs = 0
    for tag, lean_name in lean_names.items():
        try:
            lean_raw = parse_lean_toplevel_match(lean_name)
        except Exception as e:
            results[tag] = {"ok": False, "error": str(e)}
            total_diffs += 1
            continue
        explicit, default = lean_raw["explicit"], lean_raw["default"]
        py = py_tables[tag]
        Lr, Sr, Rr = domains[tag]
        diffs = []
        for L in range(*Lr):
            for S in range(*Sr):
                for R in range(*Rr):
                    key = (L, S, R)
                    py_v = py.get(key)
                    ln_v = explicit.get(key, default)
                    if py_v is None or py_v != ln_v:
                        diffs.append({"key": list(key), "py": py_v, "lean": ln_v})
        results[tag] = {
            "ok": len(diffs) == 0,
            "n_entries_python": len(py),
            "n_entries_lean_explicit": len(explicit),
            "domain": [list(Lr), list(Sr), list(Rr)],
            "n_diffs": len(diffs),
            "diffs": diffs,
        }
        total_diffs += len(diffs)
    return {
        "ok": total_diffs == 0,
        "total_diffs": total_diffs,
        "by_table": results,
    }


def run_cup2_per_n(n_range=range(4, 11)) -> dict:
    """For each n, build CUP-2 system via cup2_theorem.build_system(n), run
    verify_system; assert valid."""
    sys.path.insert(0, CLAUDE_DIR)
    import cup2_theorem as cup2  # type: ignore

    rows = []
    n_failures = 0
    for n in n_range:
        try:
            ms, fs = cup2.build_system(n)
            v = verify_system(list(ms), fs, verbose=False)
            rows.append({
                "n": n,
                "ms": list(ms),
                "product": int(__import__("math").prod(ms)),
                "valid": bool(v["valid"]),
                "cycle_length": len(v.get("cycle", [])) if v.get("valid") else None,
            })
            if not v["valid"]:
                n_failures += 1
        except Exception as e:
            rows.append({"n": n, "error": str(e)})
            n_failures += 1
    return {"ok": n_failures == 0, "rows": rows, "n_failures": n_failures}


def run_lake_build() -> dict:
    cmd = ["lake", "build", "LeanMn.SmallN.Defs"]
    try:
        p = subprocess.run(cmd, cwd=LEAN_ROOT, capture_output=True,
                           text=True, timeout=1800)
        return {
            "ok": p.returncode == 0,
            "returncode": p.returncode,
            "stdout_tail": "\n".join(p.stdout.splitlines()[-10:]),
            "stderr_tail": "\n".join(p.stderr.splitlines()[-10:]),
        }
    except Exception as e:
        return {"ok": False, "error": str(e)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=os.path.join(HERE, "parity_report.json"))
    parser.add_argument("--lake", action="store_true",
                        help="Also run `lake build LeanMn.SmallN.Defs`")
    parser.add_argument("--skip-cup2", action="store_true",
                        help="Skip CUP-2 universal-tables parity (n ∈ {4..10})")
    parser.add_argument("--cup2-n-max", type=int, default=10,
                        help="Max n for CUP-2 per-n verify (default 10, "
                             "matching Lean's current formalization range)")
    args = parser.parse_args()

    print("=" * 72)
    print("Python–Lean parity runner (strengthening task #3)")
    print("=" * 72)
    results = []
    witnesses = list(WITNESSES)
    for w in witnesses:
        print(f"\n-- {w['name']} (n={w['n']}) --")
        r = run_one(w)
        results.append(r)
        for step, info in r["steps"].items():
            tag = "PASS" if info.get("ok") else "FAIL"
            print(f"   [{tag}] {step}: "
                  f"{ {k: v for k, v in info.items() if k != 'ok'} }")

    # CUP-2 universal tables (5 tables, n-independent) + per-n verify
    cup2_tables = None
    cup2_per_n = None
    if not args.skip_cup2:
        print("\n-- CUP-2 universal-tables parity (5 tables, n-independent) --")
        cup2_tables = run_cup2_tables_parity()
        for tag, info in cup2_tables["by_table"].items():
            t = "PASS" if info.get("ok") else "FAIL"
            extra = f" diffs={info['n_diffs']}" if "n_diffs" in info else ""
            print(f"   [{t}] T_{tag}: "
                  f"{info.get('n_entries_python')}/{info.get('n_entries_lean_explicit')} entries{extra}")
        print(f"\n-- CUP-2 per-n verify (n ∈ {{4..{args.cup2_n_max}}}) --")
        cup2_per_n = run_cup2_per_n(range(4, args.cup2_n_max + 1))
        for row in cup2_per_n["rows"]:
            t = "PASS" if row.get("valid") else "FAIL"
            info = f"ms={row.get('ms')} prod={row.get('product')} L={row.get('cycle_length')}"
            if "error" in row:
                info = f"error={row['error']}"
            print(f"   [{t}] n={row['n']}: {info}")

    if args.lake:
        print("\n-- lake build --")
        lake = run_lake_build()
        print(f"   [{'PASS' if lake['ok'] else 'FAIL'}] lake build "
              f"LeanMn.SmallN.Defs: rc={lake.get('returncode')}")
    else:
        lake = {"ok": True, "skipped": "pass --lake to enable"}

    total_failures = 0
    for r in results:
        for step, info in r["steps"].items():
            if not info.get("ok"):
                total_failures += 1
    if not lake.get("ok"):
        total_failures += 1
    if cup2_tables is not None and not cup2_tables.get("ok"):
        total_failures += cup2_tables.get("total_diffs", 1)
    if cup2_per_n is not None and not cup2_per_n.get("ok"):
        total_failures += cup2_per_n.get("n_failures", 1)

    summary = {
        "witnesses": results,
        "cup2_tables_parity": cup2_tables,
        "cup2_per_n_verify": cup2_per_n,
        "lake_build": lake,
        "total_failures": total_failures,
    }
    try:
        with open(args.output, "w") as f:
            json.dump(summary, f, indent=2, default=str)
        print(f"\nWrote {args.output}")
    except Exception as e:
        print(f"Write failed: {e}")

    print("\n" + "=" * 72)
    if total_failures == 0:
        print(f"SUCCESS — all {len(results)} witnesses pass parity + verify + "
              f"negative control{' + lake build' if args.lake else ''}.")
    else:
        print(f"FAILURE — {total_failures} step(s) failed. See {args.output}.")
    print("=" * 72)
    return total_failures


if __name__ == "__main__":
    sys.exit(main())
