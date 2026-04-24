#!/usr/bin/env python3
"""
Characterize the A1 non-oscillatory residual class.

Search guidance only. Fills the questions posed in
`a1_residual_characterization_spec_2026-04-13.md`.
"""

from __future__ import annotations

import importlib.util
import random
import statistics
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


A1 = load_module(
    "a1_probe", ROOT / "probes/branch_b_bypass/derisk_A1_stretched_ssr_tail.py"
)
Budget = load_module(
    "budget_probe", ROOT / "probes/zw_mechanism_budget_probe.py"
)


@dataclass(frozen=True)
class Family:
    n: int
    label: str
    ms: tuple[int, ...]
    expected_residual: int


FAMILIES = [
    Family(9, "n9 pivot alt", (2, 3, 2, 3, 2, 3, 3, 3, 3), 348),
    Family(11, "n11 pivot 3bin", (2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3), 2028),
]


def step_dir(word, k, n):
    curr = word[k]
    nxt = word[(k + 1) % len(word)]
    if nxt == A1.R_(curr, n):
        return "cw"
    if nxt == curr:
        return "stay"
    return "ccw"


def fire_count(word, n):
    return [sum(1 for x in word if x == p) for p in range(n)]


def stay_steps_at(word, p):
    return sum(1 for k in range(len(word)) if word[k] == p and word[(k + 1) % len(word)] == p)


def reversal_count(word, n):
    dirs = [step_dir(word, k, n) for k in range(len(word))]
    out = 0
    for k in range(len(word)):
        d1 = dirs[k]
        d2 = dirs[(k + 1) % len(word)]
        if (d1, d2) in {("cw", "ccw"), ("ccw", "cw")}:
            out += 1
    return out


def compress_blocks(items):
    out = []
    for item in items:
        if out and out[-1][0] == item:
            out[-1][1] += 1
        else:
            out.append([item, 1])
    return out


def cyclic_slice(word, s, e):
    out = [word[s]]
    k = s
    while k != e:
        k = (k + 1) % len(word)
        out.append(word[k])
    return out


def binary_positions(ms):
    return [i for i, m in enumerate(ms) if m == 2]


def gap_pairs(ms, n):
    return Budget.binary_pairs(list(ms), n)


def any_oscillatory_b2b(word, ms, n):
    for b, c, interior in gap_pairs(ms, n):
        for s, e in Budget.find_gap_runs(word, b, c, interior):
            if Budget.is_oscillatory(word, s, e, n):
                return True
    return False


def ternary_b2b_runs(word, ms, n):
    runs = []
    for b, c, interior in gap_pairs(ms, n):
        if any(ms[p] != 3 for p in interior):
            continue
        for s, e in Budget.find_gap_runs(word, b, c, interior):
            runs.append(
                {
                    "b1": b,
                    "b2": c,
                    "length": len(cyclic_slice(word, s, e)),
                    "word_slice": cyclic_slice(word, s, e),
                    "start": s,
                    "end": e,
                }
            )
    return runs


def run_becomes_oscillatory_after_removing_stays(word_slice, n):
    reduced = [word_slice[0]]
    for x in word_slice[1:]:
        if x != reduced[-1]:
            reduced.append(x)
    has_cw = False
    has_ccw = False
    for a, b in zip(reduced, reduced[1:]):
        if b == A1.R_(a, n):
            has_cw = True
        elif b == A1.L_(a, n):
            has_ccw = True
    return has_cw and has_ccw


def binary_visit_adjacency(word, ms):
    out = {}
    n = len(ms)
    for b in binary_positions(ms):
        pairs = []
        for k in range(len(word)):
            if word[k] == b:
                prevp = word[(k - 1) % len(word)]
                nextp = word[(k + 1) % len(word)]
                pairs.append((prevp, nextp))
        out[b] = tuple(pairs)
    return out


def structure_sketch(word, ms, n):
    dirs = [step_dir(word, k, n) for k in range(len(word))]
    blocks = compress_blocks(dirs)
    dir_part = " / ".join(f"{d}×{c}" for d, c in blocks)
    bin_stays = {b: stay_steps_at(word, b) for b in binary_positions(ms) if stay_steps_at(word, b) > 0}
    tern_stays = sum(stay_steps_at(word, p) for p in range(n) if ms[p] != 2)
    extra = []
    if bin_stays:
        extra.append("binary stays " + ",".join(f"{b}:{c}" for b, c in sorted(bin_stays.items())))
    if tern_stays:
        extra.append(f"ternary stays total {tern_stays}")
    if not extra:
        extra.append("no stays")
    return f"direction blocks {dir_part}; " + "; ".join(extra)


def branch_a_fail_cycle(word, ms, n):
    saw_pair = False
    failed = False
    for b, c, interior in A1.binary_pairs(ms, n):
        pairs = A1.find_stretched_ssr_pairs(word, b, c, interior, n)
        if not pairs:
            continue
        saw_pair = True
        witness = A1.find_two_site_provider(word, ms, n, b, c, interior)
        if witness is None:
            failed = True
    return saw_pair and failed


def residual_population(fam: Family):
    raw = A1.enumerate_min_length_cycles(list(fam.ms), fam.n)
    uniq = sorted(set(A1.canonical_rotation(w) for w in raw))
    zw = [w for w in uniq if A1.is_zw_cwpos(w, fam.n)]
    residual = [
        w
        for w in zw
        if branch_a_fail_cycle(w, fam.ms, fam.n) and not any_oscillatory_b2b(w, fam.ms, fam.n)
    ]
    return residual


def characterize_cycle(word, fam: Family):
    fc = fire_count(word, fam.n)
    stay_at = [stay_steps_at(word, p) for p in range(fam.n)]
    ternary_runs = ternary_b2b_runs(word, fam.ms, fam.n)
    return {
        "word": word,
        "fc_per_proc": fc,
        "is_min_CL_no_stay": all(fc[p] == fam.ms[p] and stay_at[p] == 0 for p in range(fam.n)),
        "stay_count_total": sum(stay_at),
        "stay_count_at_binaries": sum(stay_at[p] for p in binary_positions(fam.ms)),
        "reversalCount": reversal_count(word, fam.n),
        "cwStepCount": sum(1 for k in range(len(word)) if step_dir(word, k, fam.n) == "cw"),
        "ccwStepCount": sum(1 for k in range(len(word)) if step_dir(word, k, fam.n) == "ccw"),
        "stayStepCount": sum(1 for k in range(len(word)) if step_dir(word, k, fam.n) == "stay"),
        "has_ternary_B2B_run": bool(ternary_runs),
        "ternary_B2B_runs": ternary_runs,
        "binary_visit_adjacency": binary_visit_adjacency(word, fam.ms),
        "sketch": structure_sketch(word, fam.ms, fam.n),
    }


def fmt_counter(counter, limit=None):
    items = counter.most_common(limit)
    return ", ".join(f"{k}:{v}" for k, v in items)


def q4_summary(cycles, fam):
    with_runs = [c for c in cycles if c["has_ternary_B2B_run"]]
    run_lengths = Counter()
    stay_broken_count = 0
    stay_broken_runs = 0
    for c in with_runs:
        cycle_has = False
        for run in c["ternary_B2B_runs"]:
            run_lengths[run["length"]] += 1
            original_osc = Budget.is_oscillatory(tuple(run["word_slice"]), 0, len(run["word_slice"]) - 1, fam.n)
            reduced_osc = run_becomes_oscillatory_after_removing_stays(run["word_slice"], fam.n)
            if (not original_osc) and reduced_osc:
                cycle_has = True
                stay_broken_runs += 1
        if cycle_has:
            stay_broken_count += 1
    modal_length = None if not run_lengths else run_lengths.most_common(1)[0][0]
    return {
        "with_runs": len(with_runs),
        "total": len(cycles),
        "modal_length": modal_length,
        "stay_broken_cycle_count": stay_broken_count,
        "stay_broken_run_count": stay_broken_runs,
    }


def sample_cycles(cycles, k, seed):
    rng = random.Random(seed)
    return rng.sample(cycles, k)


def main():
    families_data = {}
    drift = []
    total_no_stay = 0

    for fam in FAMILIES:
        residual_words = residual_population(fam)
        if len(residual_words) != fam.expected_residual:
            drift.append(f"{fam.label}: expected {fam.expected_residual}, got {len(residual_words)}")
        cycles = [characterize_cycle(word, fam) for word in residual_words]
        families_data[fam.label] = {
            "fam": fam,
            "cycles": cycles,
        }
        total_no_stay += sum(1 for c in cycles if c["is_min_CL_no_stay"])

    if drift:
        print("DRIFT DETECTED: " + "; ".join(drift))
        return

    verdict = "B" if total_no_stay > 0 else "A"
    print(f"Verdict: {verdict}")
    print()

    # Q1
    for fam in FAMILIES:
        cycles = families_data[fam.label]["cycles"]
        count = sum(1 for c in cycles if c["is_min_CL_no_stay"])
        print(f"Q1 {fam.label}: {count} / {fam.expected_residual}")
    print()

    # Q2
    q2_nonempty = False
    for fam in FAMILIES:
        subset = [c for c in families_data[fam.label]["cycles"] if c["is_min_CL_no_stay"]]
        if subset:
            q2_nonempty = True
            bins = binary_positions(fam.ms)
            per_bin = {b: Counter(c["fc_per_proc"][b] for c in subset) for b in bins}
            anomalies = sum(1 for c in subset for b in bins if c["fc_per_proc"][b] > 2)
            print(f"Q2 {fam.label}: per-binary fc { {b: dict(cnt) for b, cnt in per_bin.items()} }, anomalies={anomalies}")
    if not q2_nonempty:
        print("Q2: N/A (empty subset)")
    print()

    # Q3
    for fam in FAMILIES:
        comp = [c for c in families_data[fam.label]["cycles"] if not c["is_min_CL_no_stay"]]
        rev_hist = Counter(c["reversalCount"] for c in comp)
        stay_at_bin_pos = sum(1 for c in comp if c["stay_count_at_binaries"] >= 1)
        stay_any_pos = sum(1 for c in comp if c["stay_count_total"] >= 1)
        binary_vals = []
        for c in comp:
            for b in binary_positions(fam.ms):
                binary_vals.append(c["fc_per_proc"][b])
        print(
            f"Q3 {fam.label}: rev_hist_top={fmt_counter(rev_hist, 5)}; "
            f"stay_at_binaries>=1 {stay_at_bin_pos}/{len(comp)}; "
            f"stay_anywhere>=1 {stay_any_pos}/{len(comp)}; "
            f"max_fc_b={max(binary_vals)} median_fc_b={statistics.median(binary_vals)}; "
            f"fc_b>=4 cycles={sum(1 for c in comp if any(c['fc_per_proc'][b] >= 4 for b in binary_positions(fam.ms)))}"
        )
    print()

    # Q4
    for fam in FAMILIES:
        summary = q4_summary(families_data[fam.label]["cycles"], fam)
        frac = f"{summary['with_runs']} / {summary['total']}"
        print(
            f"Q4 {fam.label}: has_ternary_B2B_run {frac}; modal_length={summary['modal_length']}; "
            f"stay-broken-osc cycles={summary['stay_broken_cycle_count']} runs={summary['stay_broken_run_count']}"
        )
    print()

    # Q5
    for idx, fam in enumerate(FAMILIES):
        samples = sample_cycles(families_data[fam.label]["cycles"], 5, seed=20260413 + idx)
        print(f"Q5 {fam.label} samples:")
        for c in samples:
            print(
                f"  word={list(c['word'])}; fc={c['fc_per_proc']}; "
                f"stay_count_at_binaries={c['stay_count_at_binaries']}; "
                f"reversalCount={c['reversalCount']}; is_min_CL_no_stay={c['is_min_CL_no_stay']}; "
                f"sketch={c['sketch']}"
            )
        print()


if __name__ == "__main__":
    main()
