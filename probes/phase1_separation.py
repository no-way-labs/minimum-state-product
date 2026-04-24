"""Phase 1c: separation test for candidate currencies on the 97-record corpus.

Reads currencies_97.csv (produced by compute_currencies.py) and asks, for each
candidate Q:

  * Per n: do valid records and sub-threshold records overlap in Q?
    Report min/max on each side and the (signed) margin.
  * Pooled: at each n, what fraction of (valid, sub) pairs are correctly
    ordered by Q? (rank-separation, AUC-style.)
  * Valid-side saturation: std/mean of Q across valid records at each n.
  * Best normalization: among Q, Q/n, Q/n^2, Q/log(prod), pick the one with
    the tightest valid-side fit.

Compares each Q against the baseline Q = product (∏mᵢ). The baseline already
strictly separates by construction (sub-threshold means product < M_n by
definition), so the interesting question is *margin* and *saturation*, not
binary separation.

Outputs:
  - phase1_separation_report.txt with per-n tables
  - phase1_separation_summary.json with the per-Q verdict
"""
from __future__ import annotations

import csv
import json
import math
import os
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__)) or "."
SK_DIR = "./lean/LeanMn/LowerBound/SK"
CSV_PATH = os.path.join(SK_DIR, "currencies_97.csv")
TXT_OUT = os.path.join(SK_DIR, "phase1_separation_report.txt")
JSON_OUT = os.path.join(SK_DIR, "phase1_separation_summary.json")

CURRENCIES = [
    "product", "log2_product",
    "L", "kappa_mov", "kappa_tot",
    "H_pos_sum", "H_pos_avg", "H_mover", "H_joint",
    "L_over_n", "L_over_n2", "kappa_mov_over_L", "kappa_mov_over_nL",
    "Hpos_over_log2prod", "Hpos_over_nlog23",
    "coverage",
]


def load_rows():
    rows = []
    with open(CSV_PATH) as f:
        for r in csv.DictReader(f):
            r["n"] = int(r["n"])
            r["valid"] = (r["valid"].lower() == "true")
            for k in CURRENCIES:
                try:
                    r[k] = float(r[k])
                except (KeyError, ValueError):
                    r[k] = None
            rows.append(r)
    return rows


def per_n_separation(rows, key):
    """For each n, report min/max of valid and sub buckets, and margin
    (positive if valid > sub strictly, negative if overlap)."""
    by_n = defaultdict(lambda: {"valid": [], "sub": []})
    for r in rows:
        bucket = "valid" if r["valid"] else "sub"
        if r[key] is None:
            continue
        by_n[r["n"]][bucket].append(r[key])
    out = []
    for n in sorted(by_n):
        v = sorted(by_n[n]["valid"])
        s = sorted(by_n[n]["sub"])
        if not v or not s:
            out.append({"n": n, "n_valid": len(v), "n_sub": len(s),
                        "v_min": min(v) if v else None, "v_max": max(v) if v else None,
                        "s_min": min(s) if s else None, "s_max": max(s) if s else None,
                        "margin": None, "direction": None})
            continue
        # try both orientations
        margin_v_above = min(v) - max(s)   # >0 means valid strictly > sub
        margin_v_below = min(s) - max(v)   # >0 means valid strictly < sub
        if margin_v_above >= margin_v_below:
            margin, direction = margin_v_above, "valid>sub"
        else:
            margin, direction = margin_v_below, "valid<sub"
        # also: pairwise concordance (rank AUC-like): fraction of (v,s) pairs
        # consistent with `direction`.
        consistent = 0
        total = 0
        for vv in v:
            for ss in s:
                total += 1
                if direction == "valid>sub":
                    if vv > ss:
                        consistent += 1
                    elif vv == ss:
                        consistent += 0.5
                else:
                    if vv < ss:
                        consistent += 1
                    elif vv == ss:
                        consistent += 0.5
        auc = consistent / total if total else None
        out.append({
            "n": n,
            "n_valid": len(v), "n_sub": len(s),
            "v_min": min(v), "v_max": max(v), "v_mean": sum(v)/len(v),
            "v_std": (sum((x-sum(v)/len(v))**2 for x in v)/len(v))**0.5,
            "s_min": min(s), "s_max": max(s), "s_mean": sum(s)/len(s),
            "margin": margin, "direction": direction,
            "auc": auc,
        })
    return out


def saturation_score(per_n_table):
    """Across valid records, normalize Q by n and ask: how flat is Q/(n^k)?
    Return the smallest-CV (coefficient of variation) over k in {0,1,2}."""
    best = None
    for k in (0, 1, 2):
        vals_per_n = []
        for row in per_n_table:
            if row.get("v_mean") is None:
                continue
            vals_per_n.append(row["v_mean"] / (row["n"] ** k))
        if not vals_per_n:
            continue
        m = sum(vals_per_n) / len(vals_per_n)
        if m == 0:
            continue
        cv = (sum((x - m) ** 2 for x in vals_per_n) / len(vals_per_n)) ** 0.5 / abs(m)
        if best is None or cv < best[1]:
            best = (k, cv, vals_per_n)
    return best


def relative_margin(row):
    """Margin normalized by the bigger of |min(v)|, |min(s)| so it is a
    relative gap. Returns None if margin <= 0 (overlap)."""
    if row.get("margin") is None or row["margin"] <= 0:
        return None
    scale = max(abs(row["v_max"]), abs(row["s_max"]), 1.0)
    return row["margin"] / scale


def write_report(rows):
    out_lines = []
    summary = {}
    out_lines.append(f"Phase 1 separation report  ({len(rows)} records)")
    out_lines.append(f"Source: {CSV_PATH}")
    out_lines.append("=" * 80)
    out_lines.append("")
    out_lines.append("Convention: 'margin' is the signed gap between min and max across the")
    out_lines.append("two buckets in the chosen direction. margin > 0 means strict separation;")
    out_lines.append("margin <= 0 means overlap (margin = -overlap_width).")
    out_lines.append("AUC = fraction of (valid, sub) pairs ordered consistently with direction.")
    out_lines.append("")
    by_n_ranges = sorted({r["n"] for r in rows})
    out_lines.append(f"n values: {by_n_ranges}")
    out_lines.append(f"valid count: {sum(1 for r in rows if r['valid'])}")
    out_lines.append(f"sub count: {sum(1 for r in rows if not r['valid'])}")
    out_lines.append("")

    for key in CURRENCIES:
        out_lines.append("-" * 80)
        out_lines.append(f"Q = {key}")
        out_lines.append("-" * 80)
        table = per_n_separation(rows, key)
        out_lines.append(
            f"  {'n':>3s} {'#v':>3s} {'#s':>3s}  "
            f"{'v_min':>10s} {'v_max':>10s} {'v_std':>8s}  "
            f"{'s_min':>10s} {'s_max':>10s}  "
            f"{'margin':>10s} {'dir':>9s} {'AUC':>5s}"
        )
        per_n_summaries = []
        for row in table:
            if row.get("margin") is None:
                out_lines.append(f"  {row['n']:>3d} {row['n_valid']:>3d} {row['n_sub']:>3d}  "
                                 f"  (insufficient data)")
                continue
            out_lines.append(
                f"  {row['n']:>3d} {row['n_valid']:>3d} {row['n_sub']:>3d}  "
                f"{row['v_min']:>10.3f} {row['v_max']:>10.3f} {row['v_std']:>8.3f}  "
                f"{row['s_min']:>10.3f} {row['s_max']:>10.3f}  "
                f"{row['margin']:>+10.3f} {row['direction']:>9s} "
                f"{row['auc']:>5.3f}"
            )
            per_n_summaries.append(row)
        # roll-up summary
        if per_n_summaries:
            n_strict = sum(1 for r in per_n_summaries if r["margin"] > 0)
            n_overlap = sum(1 for r in per_n_summaries if r["margin"] <= 0)
            mean_auc = sum(r["auc"] for r in per_n_summaries) / len(per_n_summaries)
            mean_rel_margin = (
                sum(rm for r in per_n_summaries
                    if (rm := relative_margin(r)) is not None) /
                max(1, sum(1 for r in per_n_summaries if relative_margin(r) is not None))
            )
            sat = saturation_score(per_n_summaries)
            sat_desc = (f"k={sat[0]}, CV={sat[1]:.3f}" if sat else "n/a")
            out_lines.append(
                f"  → strict-separation n's: {n_strict}/{len(per_n_summaries)}, "
                f"overlap n's: {n_overlap},  mean AUC = {mean_auc:.3f},  "
                f"mean rel-margin (when sep) = {mean_rel_margin:.3f},  "
                f"valid-saturation: {sat_desc}"
            )
            summary[key] = {
                "n_strict_separation": n_strict,
                "n_overlap": n_overlap,
                "mean_auc": round(mean_auc, 4),
                "mean_relative_margin": round(mean_rel_margin, 4),
                "valid_saturation_k": sat[0] if sat else None,
                "valid_saturation_cv": round(sat[1], 4) if sat else None,
            }
        out_lines.append("")

    # head-to-head ranking vs product baseline
    out_lines.append("=" * 80)
    out_lines.append("RANKING vs ∏mᵢ baseline")
    out_lines.append("=" * 80)
    base = summary.get("product", {})
    out_lines.append(f"baseline product: AUC={base.get('mean_auc')}, "
                     f"strict_n={base.get('n_strict_separation')}, "
                     f"sat_CV={base.get('valid_saturation_cv')}")
    out_lines.append("")
    out_lines.append(f"{'currency':<24s} {'AUC':>6s} {'strict_n':>9s} "
                     f"{'rel_margin':>11s} {'sat_CV':>8s} {'verdict_vs_prod':>20s}")
    for key in CURRENCIES:
        s = summary.get(key)
        if not s:
            continue
        verdict = []
        if base.get("mean_auc") is not None and s["mean_auc"] > base["mean_auc"]:
            verdict.append("AUC↑")
        elif base.get("mean_auc") is not None and s["mean_auc"] < base["mean_auc"]:
            verdict.append("AUC↓")
        if base.get("valid_saturation_cv") is not None and s["valid_saturation_cv"] is not None:
            if s["valid_saturation_cv"] < base["valid_saturation_cv"]:
                verdict.append("sat↑")
            else:
                verdict.append("sat↓")
        if base.get("n_strict_separation") is not None and s["n_strict_separation"] > base["n_strict_separation"]:
            verdict.append("sep↑")
        elif base.get("n_strict_separation") is not None and s["n_strict_separation"] < base["n_strict_separation"]:
            verdict.append("sep↓")
        verdict_str = " ".join(verdict) if verdict else "≈"
        out_lines.append(
            f"{key:<24s} {s['mean_auc']:>6.3f} {s['n_strict_separation']:>9d} "
            f"{s['mean_relative_margin']:>11.3f} "
            f"{(s['valid_saturation_cv'] if s['valid_saturation_cv'] is not None else float('nan')):>8.3f} "
            f"{verdict_str:>20s}"
        )

    text = "\n".join(out_lines)
    with open(TXT_OUT, "w") as f:
        f.write(text + "\n")
    with open(JSON_OUT, "w") as f:
        json.dump(summary, f, indent=2)
    print(text)
    print(f"\nWrote {TXT_OUT}")
    print(f"Wrote {JSON_OUT}")


def main():
    rows = load_rows()
    if not rows:
        raise SystemExit(f"empty CSV at {CSV_PATH}")
    write_report(rows)


if __name__ == "__main__":
    main()
