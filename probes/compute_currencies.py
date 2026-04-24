"""Currency-reframing Phase 1: compute candidate currencies on the 97-record corpus.

Loads (rebuilds) the same 97 records that paper_upgrade_3/corpus_canonical.json
indexes, but with cycle/movers/det in-memory, and computes:

    L          : len(cycle)
    kappa_mov  : |{(p, c[(p-1)%n], c[p], c[(p+1)%n]) : k step, p == movers[k]}|
    kappa_tot  : |{(p, c[(p-1)%n], c[p], c[(p+1)%n]) : any step k, any p}|
    H_pos      : per-position empirical entropy of values along cycle, summed
    H_mover    : entropy of mover-position distribution
    H_joint    : entropy of joint (i-1, i, i+1) value triples across (k, i)
    coverage   : L / product           (sanity check vs canonical)

Writes a CSV alongside this script at ./currencies_97.csv with one row per
record, plus a brief stdout summary by class.

Notes on the kappa definition. The program memo (currency_reframing_program.md
§Candidate 2) defines kappa as "the number of distinct (i, a, b, c) tuples
such that at some step k of C, position i is the MOVER, c_k(i-1)=a, c_k(i)=b,
c_k(i+1)=c. This counts the detOf-determined entries in the rule table." We
take that as the primary kappa = kappa_mov, and additionally report kappa_tot
which counts all det-determined entries (including the no-move ones where
det(p,L,S,R)=S). kappa_tot >= kappa_mov, and kappa_tot is a strict upper bound
on the number of (p, L, S, R) entries pinned by the cycle.

Provenance: builders are the canonical phase1 + wave4 ones used to produce
corpus_canonical.json (overall_hash_16=f4b017b1f57687cc, 97 records). After
the per-record build we cross-check (n, sorted_ms, L) multiplicity against
the canonical 97-record set and report any drift.
"""
from __future__ import annotations

import csv
import importlib.util
import json
import math
import os
import sys
import time
from collections import Counter, defaultdict

import numpy as np

ROOT = "."
PU1 = os.path.join(ROOT, "docs/lean_docs/paper_upgrade_1")
W4 = os.path.join(ROOT, "docs/lean_docs/topo_revival/wave4")
DOCS = os.path.join(ROOT, "docs")
CLAUDE = os.path.join(ROOT, "claude")

sys.path.insert(0, PU1)
sys.path.insert(0, W4)
sys.path.insert(0, DOCS)
sys.path.insert(0, CLAUDE)

# phase1 has its OWN copies of build_sub_corpus_n8, build_n9_table7_corpus,
# load_smalln_witnesses, build_record_from_witness. These are the canonical
# producers of the 4 absorbers + 59 n=8 sub + 9 n=9 Table7 sub records.
import probe_strengthening1_n8_subthreshold as p1  # noqa: E402

# wave4 has its OWN copies of build_at_corpus + build_sub_corpus(per_n=8).
# These produce the 6 CLB ternary-strip witnesses + 19 small-n sub records.
spec = importlib.util.spec_from_file_location(
    "wave4", os.path.join(W4, "probe_wave4_combined_2026-05-03.py")
)
w4 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w4)


def kappa_mover(cycle, movers, n):
    seen = set()
    for k, c in enumerate(cycle):
        p = movers[k]
        seen.add((p, c[(p - 1) % n], c[p], c[(p + 1) % n]))
    return len(seen)


def kappa_total(cycle, n):
    seen = set()
    for c in cycle:
        for p in range(n):
            seen.add((p, c[(p - 1) % n], c[p], c[(p + 1) % n]))
    return len(seen)


def _entropy_from_counter(cnt):
    total = sum(cnt.values())
    if total == 0:
        return 0.0
    H = 0.0
    for v in cnt.values():
        if v == 0:
            continue
        p = v / total
        H -= p * math.log2(p)
    return H


def H_per_position(cycle, n):
    Hs = []
    for p in range(n):
        c = Counter(cfg[p] for cfg in cycle)
        Hs.append(_entropy_from_counter(c))
    return Hs


def H_mover(movers, n):
    return _entropy_from_counter(Counter(movers))


def H_joint(cycle, n):
    cnt = Counter()
    for cfg in cycle:
        for p in range(n):
            cnt[(p, cfg[(p - 1) % n], cfg[p], cfg[(p + 1) % n])] += 1
    return _entropy_from_counter(cnt)


def normalize_record(rec):
    """Standardize cycle to list of tuples, movers to list of ints."""
    cycle = [tuple(c) for c in rec["cycle"]]
    movers = list(rec["movers"])
    n = rec["n"]
    return cycle, movers, n


def compute_row(rec):
    cycle, movers, n = normalize_record(rec)
    L = len(cycle)
    assert L == rec["L"], f"L mismatch on {rec.get('class')} ms={rec['ms']}"
    km = kappa_mover(cycle, movers, n)
    kt = kappa_total(cycle, n)
    Hpos = H_per_position(cycle, n)
    Hp_sum = sum(Hpos)
    Hp_avg = Hp_sum / n
    Hm = H_mover(movers, n)
    Hj = H_joint(cycle, n)
    prod = int(np.prod(rec["ms"]))
    return {
        "class": rec["class"],
        "name": rec.get("name", ""),
        "n": n,
        "ms": "[" + ",".join(str(x) for x in rec["ms"]) + "]",
        "sorted_ms": "[" + ",".join(str(x) for x in sorted(rec["ms"])) + "]",
        "product": prod,
        "log2_product": math.log2(prod),
        "L": L,
        "kappa_mov": km,
        "kappa_tot": kt,
        "H_pos_sum": round(Hp_sum, 6),
        "H_pos_avg": round(Hp_avg, 6),
        "H_mover": round(Hm, 6),
        "H_joint": round(Hj, 6),
        "coverage": round(L / prod, 6),
        "L_over_n": round(L / n, 4),
        "L_over_n2": round(L / (n * n), 4),
        "kappa_mov_over_L": round(km / L, 4),
        "kappa_mov_over_nL": round(km / (n * L), 4),
        "Hpos_over_log2prod": round(Hp_sum / math.log2(prod), 4) if prod > 1 else 0.0,
        "Hpos_over_nlog23": round(Hp_sum / (n * math.log2(3)), 4),
    }


def is_valid_class(class_):
    """The 10 'valid' records are at_clb (6) + at_smallN (4). The 87
    sub-threshold records are sub + sub_n9table7."""
    return class_ in ("at_clb", "at_smallN")


def main():
    print("=" * 72)
    print("CURRENCY REFRAMING — Phase 1 compute (L, kappa, H) on 97-record corpus")
    print("=" * 72)
    t0 = time.time()

    cache_path = "./lean/LeanMn/LowerBound/SK/cycles_97_cache.json"
    os.makedirs(os.path.dirname(cache_path), exist_ok=True)

    if os.path.exists(cache_path):
        print(f"\n[cache] loading rebuilt corpus from {cache_path}...", flush=True)
        all_recs = json.load(open(cache_path))
        # det dicts came back as {str(tuple): val}; convert to tuple keys
        for r in all_recs:
            det_in = r["det"]
            new_det = {}
            for k, v in det_in.items():
                if isinstance(k, str):
                    # "(p,L,S,R)" string → tuple
                    nums = tuple(int(x) for x in k.strip("()").split(","))
                    new_det[nums] = v
                else:
                    new_det[tuple(k)] = v
            r["det"] = new_det
            r["cycle"] = [tuple(c) for c in r["cycle"]]
        print(f"      loaded {len(all_recs)} cached records", flush=True)
    else:
        print("\n[1/5] phase1.load_smalln_witnesses() (4 absorbers, n=5..8)...", flush=True)
        abs_recs = p1.load_smalln_witnesses()
        for r in abs_recs:
            r["class"] = "at_smallN"
        print(f"      got {len(abs_recs)} absorbers")

        print("\n[2/5] wave4.build_at_corpus() (6 CLB ternary-strip, n=5..10)...", flush=True)
        clb_recs = w4.build_at_corpus()
        for r in clb_recs:
            r["class"] = "at_clb"
        print(f"      got {len(clb_recs)} ternary-strip")

        print("\n[3/5] wave4.build_sub_corpus(per_n=8) (small-n sub, n=5,6,7)...", flush=True)
        sub_small = w4.build_sub_corpus(per_n=8)
        for r in sub_small:
            r["class"] = "sub"
        print(f"      got {len(sub_small)} small-n sub")

        print("\n[4/5] phase1.build_sub_corpus_n8 (n=8 sub-threshold)...", flush=True)
        n8_sub, n8_missed = p1.build_sub_corpus_n8(per_ordering_budget=8.0, max_orderings=30)
        for r in n8_sub:
            r["class"] = "sub"
        print(f"      got {len(n8_sub)} n=8 sub  (missed {len(n8_missed)})")

        print("\n[5/5] phase1.build_n9_table7_corpus (n=9 Table 7 sub)...", flush=True)
        n9_table7, n9_missed = p1.build_n9_table7_corpus(per_ordering_budget=15.0, max_orderings=150)
        for r in n9_table7:
            r["class"] = "sub_n9table7"
        print(f"      got {len(n9_table7)} n=9 Table 7  (missed {len(n9_missed)})")

        all_recs = abs_recs + clb_recs + sub_small + n8_sub + n9_table7

        # cache for re-runs
        cacheable = []
        for r in all_recs:
            cacheable.append({
                "class": r["class"], "name": r.get("name", ""),
                "n": r["n"], "ms": list(r["ms"]),
                "cycle": [list(c) for c in r["cycle"]],
                "movers": list(r["movers"]),
                "det": {str(k): v for k, v in r["det"].items()},
                "L": r["L"], "product": int(r["product"]),
            })
        with open(cache_path, "w") as f:
            json.dump(cacheable, f)
        print(f"\n[cache] wrote {cache_path} ({len(all_recs)} records)", flush=True)
    by_class = Counter(r["class"] for r in all_recs)
    print(f"\nTotal rebuilt: {len(all_recs)}")
    print(f"By class: {dict(by_class)}")

    # cross-check vs canonical
    canon_path = os.path.join(ROOT, "docs/lean_docs/paper_upgrade_3/corpus_canonical.json")
    canon = json.load(open(canon_path))
    canon_by_class = {k: v["total"] for k, v in canon["meta"]["summary_by_class"].items()}
    print(f"Canonical n_records={canon['meta']['n_records']}, by_class={canon_by_class}")

    # build canonical (n, sorted_ms, L) multiset for cross-check
    canon_keys = Counter(
        (r["n"], tuple(sorted(r["ms"])), r["L"]) for r in canon["records"]
    )
    rebuilt_keys = Counter(
        (r["n"], tuple(sorted(r["ms"])), r["L"]) for r in all_recs
    )
    only_canon = canon_keys - rebuilt_keys
    only_rebuilt = rebuilt_keys - canon_keys
    if only_canon:
        print(f"  In canonical but not rebuilt: {sum(only_canon.values())} records")
        for k, v in list(only_canon.items())[:5]:
            print(f"    {k}: x{v}")
    if only_rebuilt:
        print(f"  In rebuilt but not canonical: {sum(only_rebuilt.values())} records")
        for k, v in list(only_rebuilt.items())[:5]:
            print(f"    {k}: x{v}")

    print(f"\nComputing currencies on {len(all_recs)} records...", flush=True)
    rows = []
    for i, r in enumerate(all_recs):
        row = compute_row(r)
        row["id"] = i + 1
        row["valid"] = is_valid_class(r["class"])
        rows.append(row)

    # write CSV — write to /tmp/claude (sandbox-writable); we'll mirror it
    # into docs/currency via the Write tool after the script finishes.
    csv_path = "./lean/LeanMn/LowerBound/SK/currencies_97.csv"
    os.makedirs(os.path.dirname(csv_path), exist_ok=True)
    field_order = [
        "id", "class", "valid", "name", "n", "ms", "sorted_ms",
        "product", "log2_product",
        "L", "kappa_mov", "kappa_tot",
        "H_pos_sum", "H_pos_avg", "H_mover", "H_joint",
        "coverage", "L_over_n", "L_over_n2",
        "kappa_mov_over_L", "kappa_mov_over_nL",
        "Hpos_over_log2prod", "Hpos_over_nlog23",
    ]
    with open(csv_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=field_order)
        w.writeheader()
        for row in rows:
            w.writerow(row)
    print(f"Wrote {csv_path}")

    # quick stdout summary
    print(f"\nSummary by class (means):")
    print(f"  {'class':14s} {'cnt':>4s} {'L̄':>6s} {'κ̄_mov':>8s} {'κ̄_tot':>8s} "
          f"{'H̄_pos':>8s} {'cover̄':>7s}")
    by_cls = defaultdict(list)
    for row in rows:
        by_cls[row["class"]].append(row)
    for cls, lst in sorted(by_cls.items()):
        mL = np.mean([x["L"] for x in lst])
        mKm = np.mean([x["kappa_mov"] for x in lst])
        mKt = np.mean([x["kappa_tot"] for x in lst])
        mH = np.mean([x["H_pos_sum"] for x in lst])
        mC = np.mean([x["coverage"] for x in lst])
        print(f"  {cls:14s} {len(lst):>4d} {mL:>6.1f} {mKm:>8.1f} {mKt:>8.1f} "
              f"{mH:>8.3f} {mC:>7.3f}")

    print(f"\nTotal runtime: {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
