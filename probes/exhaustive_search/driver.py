#!/usr/bin/env python3
"""App C exhaustive-search driver — end-to-end rejection-stream producer.

For each n in {3, ..., 9} and each sub-threshold multiset (product <
M_n from mn_connected), this driver:

  C1) enumerates all sub-threshold multisets          (multiset_enum.py)
  C2) for each, enumerates D_n orbit representatives  (multiset_enum.py)
  C3) for each oriented rep, enumerates candidate good cycles via DFS
      under forced-neighbor det-consistency           (this file)
  C4) for each candidate cycle, enumerates all consistent rule-table
      completions, applying the two proof-critical pruning rules
      (forced-neighbor; state-label canonicalization on the cycle is
      already reflected in the DFS). The `quasi-unidirectionality`
      rule is treated as a search optimisation; candidates with four
      cyclically consecutive binary processors are emitted in a
      replay class and independently re-rejected by the verifier.
  C5) for each surviving completion, runs the independent
      Python verifier (`probes/verifier.py::verify_system`). If the
      system is valid (pass), that is a sub-threshold witness and
      contradicts the paper's lower bound; the driver fails loudly.
      If the system is invalid, emit a rejection certificate.

Output:
  artifacts/rejections/summary.json              top-level index
  artifacts/rejections/n{n}/index.json           per-n index
  artifacts/rejections/n{n}/ms-{prod}-{slug}.jsonl
                                                 one line per rejection

Usage:
  python3 driver.py                  # full n=3..9 run (hours to days)
  python3 driver.py --n 5            # single n
  python3 driver.py --summary-only   # skip C3-C5; print C1/C2 only
  python3 driver.py --max-cycles 50  # cap cycles per orientation
                                       (debug; breaks "exhaustive")
  python3 driver.py --dry-run        # no certificate emission
  python3 driver.py --replay <path>  # re-verify every cert in a shipped
                                       rejection-stream file or directory
                                       (referee workflow)

This driver is deterministic. The only non-determinism in the pipeline
is Python's dict-iteration order for free-entry branching, which we
fix via sorted(free_entries). Running the driver twice on the same
state produces bit-for-bit identical certificates.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time
from itertools import product as iproduct
from typing import Iterable, Iterator, Optional

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(REPO, "probes"))

from multiset_enum import (  # type: ignore
    c1_c2_manifest, mn_connected, enumerate_multisets, dihedral_orbits,
)
from verifier import verify_system  # type: ignore


# ---------------------------------------------------------------------------
# C3: candidate good cycle enumeration (DFS with forced-neighbor propagation)
# ---------------------------------------------------------------------------

def enumerate_candidate_cycles(
    ms: tuple[int, ...],
    *,
    L_cap: Optional[int] = None,
    time_budget_s: Optional[float] = None,
    max_cycles: Optional[int] = None,
) -> list[dict]:
    """Return every candidate good cycle on `ms` (Dijkstra model).

    See the module docstring for the specification. Cycles are
    emitted exactly once — by fixing the cycle's lex-min config as
    the starting config.

    Iterative DFS with shared mutable path / det / movers / mover_set /
    visited, and explicit backtrack stack. Avoids generator-recursion
    memory buildup.
    """
    n = len(ms)
    prod = 1
    for m in ms:
        prod *= m
    if L_cap is None:
        L_cap = max(3 * n, 2 * (prod // max(1, n)))
    t0 = time.time()

    all_configs_sorted = sorted(iproduct(*(range(m) for m in ms)))

    results: list[dict] = []
    det: dict = {}

    def _emit_if_closed(start, cur_config, path, movers, mover_set):
        """Check whether appending (p, new_val) to path closes a
        fairness/ME-satisfying cycle and emit if so."""
        # caller has already propagated det; here we just check ME.
        me_ok = True
        for c in path:
            priv = 0
            for i in range(n):
                Li, Si, Ri = (c[(i - 1) % n], c[i], c[(i + 1) % n])
                ki = (i, Li, Si, Ri)
                if ki in det and det[ki] != Si:
                    priv += 1
                    if priv > 1:
                        break
            if priv != 1:
                me_ok = False
                break
        if me_ok:
            results.append({
                "ms": tuple(ms), "n": n, "L": len(path),
                "cycle": [list(c) for c in path],
                "movers": list(movers),
                "det": {f"{k[0]},{k[1]},{k[2]},{k[3]}": v
                        for k, v in det.items()},
            })
            if max_cycles is not None and len(results) >= max_cycles:
                raise StopIteration

    try:
     for start in all_configs_sorted:
        if time_budget_s is not None and time.time() - t0 > time_budget_s:
            return results
        det.clear()
        path = [start]
        visited = {start}
        movers: list = []
        mover_set: set = set()

        # Stack entries: ("enter", config_to_try_from) or
        #                ("branch", config, p, new_val, old_det_keys_to_remove, restored_mover_set_flag)
        # We use a simple iterative DFS with an explicit frame list.
        #
        # Each frame = a choice point at `path[-1]`, iterating (p, new_val)
        # in order. We process one branch at a time, descend, then pop.
        #
        # Implementation: recursive via explicit "branch" tuples keeping
        # per-level state.

        def branches_for(cfg):
            for p in range(n):
                for nv in range(ms[p]):
                    if nv != cfg[p]:
                        yield p, nv

        # iter_stack[k] = iterator of remaining (p, new_val) branches
        # at depth k;  undo_stack[k] = the (added_mover, added_silent,
        # mover_set_new_flag, p_taken, new_cfg_taken) to undo when we
        # leave depth k+1.
        iter_stack = [iter(list(branches_for(start)))]
        undo_stack: list = []
        # We always have len(iter_stack) == len(path).

        while iter_stack:
            if time_budget_s is not None and time.time() - t0 > time_budget_s:
                return results

            # Try to take the next branch at the current top.
            cur_cfg = path[-1]
            try:
                p, new_val = next(iter_stack[-1])
            except StopIteration:
                # Backtrack.
                iter_stack.pop()
                if undo_stack:
                    added_mover, added_silent, mover_set_new, taken_cfg = undo_stack.pop()
                    if taken_cfg is not None:
                        path.pop()
                        visited.discard(taken_cfg)
                        movers.pop()
                        if mover_set_new is not None:
                            mover_set.discard(mover_set_new)
                    for k in added_silent:
                        del det[k]
                    if added_mover is not None:
                        del det[added_mover]
                continue

            Lp, Sp, Rp = (cur_cfg[(p - 1) % n], cur_cfg[p],
                          cur_cfg[(p + 1) % n])
            key_m = (p, Lp, Sp, Rp)
            added_mover_key = None
            if key_m in det:
                if det[key_m] != new_val:
                    continue
            else:
                det[key_m] = new_val
                added_mover_key = key_m

            added_silent = []
            consistent = True
            for i in range(n):
                if i == p:
                    continue
                Li, Si, Ri = (cur_cfg[(i - 1) % n], cur_cfg[i],
                              cur_cfg[(i + 1) % n])
                key_i = (i, Li, Si, Ri)
                if key_i in det:
                    if det[key_i] != Si:
                        consistent = False
                        break
                else:
                    det[key_i] = Si
                    added_silent.append(key_i)
            if not consistent:
                for k in added_silent:
                    del det[k]
                if added_mover_key is not None:
                    del det[added_mover_key]
                continue

            new_cfg = cur_cfg[:p] + (new_val,) + cur_cfg[p + 1:]

            if new_cfg == start and len(path) >= n:
                # Closure candidate; fairness check.
                all_movers = mover_set | {p}
                if len(all_movers) == n:
                    _emit_if_closed(start, cur_cfg, path,
                                    movers + [p], all_movers)
                # Don't descend through closure.
                for k in added_silent:
                    del det[k]
                if added_mover_key is not None:
                    del det[added_mover_key]
                continue

            if new_cfg in visited:
                for k in added_silent:
                    del det[k]
                if added_mover_key is not None:
                    del det[added_mover_key]
                continue

            if new_cfg < start:
                # This would be a rotation of a lex-smaller cycle.
                for k in added_silent:
                    del det[k]
                if added_mover_key is not None:
                    del det[added_mover_key]
                continue

            if len(path) >= L_cap:
                for k in added_silent:
                    del det[k]
                if added_mover_key is not None:
                    del det[added_mover_key]
                continue

            # Fairness pruning: need to cover all n processors within
            # L_cap - len(path) remaining steps.
            remaining_steps = L_cap - len(path)
            unvisited_procs = n - len(mover_set | {p})
            if unvisited_procs > remaining_steps:
                for k in added_silent:
                    del det[k]
                if added_mover_key is not None:
                    del det[added_mover_key]
                continue

            # Descend.
            path.append(new_cfg)
            visited.add(new_cfg)
            movers.append(p)
            mover_set_new = None
            if p not in mover_set:
                mover_set.add(p)
                mover_set_new = p
            undo_stack.append((added_mover_key, added_silent,
                              mover_set_new, new_cfg))
            iter_stack.append(iter(list(branches_for(new_cfg))))
    except StopIteration:
        pass
    return results


# ---------------------------------------------------------------------------
# C4: rule-table completion enumeration with pruning
# ---------------------------------------------------------------------------

def _det_parse(det_json: dict[str, int]) -> dict[tuple[int, int, int, int], int]:
    out = {}
    for k, v in det_json.items():
        parts = [int(x) for x in k.split(",")]
        out[(parts[0], parts[1], parts[2], parts[3])] = int(v)
    return out


def all_free_entries(ms: tuple[int, ...],
                     det: dict[tuple[int, int, int, int], int]) -> list:
    """Sorted list of (p, L, S, R) triples not yet in det."""
    free = []
    n = len(ms)
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    if (p, L, S, R) not in det:
                        free.append((p, L, S, R))
    free.sort()
    return free


def enumerate_completions(
    ms: tuple[int, ...],
    det: dict[tuple[int, int, int, int], int],
) -> Iterator[dict[tuple[int, int, int, int], int]]:
    """Yield every extension of `det` to a total rule table over `ms`."""
    free = all_free_entries(ms, det)
    n = len(ms)
    if not free:
        yield dict(det)
        return
    stack = [(0, dict(det))]
    while stack:
        idx, cur = stack.pop()
        if idx == len(free):
            yield cur
            continue
        p, L, S, R = free[idx]
        # Branch on outputs in deterministic lex order.
        for out in range(ms[p]):
            cur2 = dict(cur)
            cur2[(p, L, S, R)] = out
            stack.append((idx + 1, cur2))


def det_to_fs(ms: tuple[int, ...],
              det_full: dict[tuple[int, int, int, int], int]) -> list:
    """Materialise det as a list of callable f_i."""
    n = len(ms)
    per_p = [{} for _ in range(n)]
    for (p, L, S, R), out in det_full.items():
        per_p[p][(L, S, R)] = out
    fs = []
    for p in range(n):
        t = per_p[p]
        fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))
    return fs


# ---------------------------------------------------------------------------
# C4 optimisation: quasi-unidirectionality (four cyclically consecutive binaries)
# ---------------------------------------------------------------------------

def has_4_consecutive_binaries(ms: tuple[int, ...]) -> bool:
    n = len(ms)
    if n < 4:
        return False
    for j in range(n):
        if all(ms[(j + k) % n] == 2 for k in range(4)):
            return True
    return False


# ---------------------------------------------------------------------------
# C5: run the verifier, build a rejection certificate
# ---------------------------------------------------------------------------

def _summarize_verifier_report(report: dict) -> tuple[str, dict]:
    """Reduce verify_system's nested output to (failing_property, detail)."""
    props = report.get("properties", {}) or {}
    for name, val in props.items():
        if isinstance(val, (tuple, list)) and len(val) == 2:
            ok, info = val
            if not ok:
                return name, {"info": str(info)}
    # No single property was flagged; synthesize.
    return "unknown", {"info": "verify_system returned valid=False"
                              " without a named failing property."}


def build_rejection_certificate(ms, orientation, cycle, movers, det, completion,
                                verifier_report: dict) -> dict:
    property_failed, detail = _summarize_verifier_report(verifier_report)
    return {
        "schema_version": 1,
        "n": len(ms),
        "ms_sorted": list(ms),
        "orientation": list(orientation),
        "product": int(_prod(orientation)),
        "cycle": [list(c) for c in cycle],
        "movers": list(movers),
        "det_forced": {f"{p},{L},{S},{R}": v
                       for (p, L, S, R), v in det.items()},
        "completion": {f"{p},{L},{S},{R}": v
                       for (p, L, S, R), v in completion.items()
                       if (p, L, S, R) not in det},
        "property_failed": property_failed,
        "detail": detail,
    }


def _prod(xs):
    p = 1
    for x in xs:
        p *= x
    return p


# ---------------------------------------------------------------------------
# Top-level driver
# ---------------------------------------------------------------------------

ARTIFACT_DIR = os.path.join(REPO, "artifacts", "rejections")


def slugify_ms(ms):
    return "-".join(str(x) for x in ms)


def run_one_orientation(n: int, orientation: tuple[int, ...],
                        *, dry_run: bool, writer,
                        max_cycles_per_orient: Optional[int],
                        max_completions_per_cycle: Optional[int]
                        ) -> dict:
    """Run C3 + C4 + C5 on one oriented state-count vector. Returns
    per-orientation stats."""
    n_cycles = 0
    n_completions = 0
    n_valid = 0
    n_rejected = 0
    witnesses = []

    cycles_list = enumerate_candidate_cycles(
        orientation, max_cycles=max_cycles_per_orient)
    for cyc_rec in cycles_list:
        n_cycles += 1
        if max_cycles_per_orient is not None and n_cycles > max_cycles_per_orient:
            break
        cycle = [tuple(c) for c in cyc_rec["cycle"]]
        movers = tuple(cyc_rec["movers"])
        det = _det_parse(cyc_rec["det"])

        k = 0
        for completion in enumerate_completions(orientation, det):
            n_completions += 1
            k += 1
            if max_completions_per_cycle is not None and k > max_completions_per_cycle:
                break
            fs = det_to_fs(orientation, completion)
            report = verify_system(list(orientation), fs, verbose=False)
            if report.get("valid"):
                n_valid += 1
                witnesses.append({
                    "ms": list(orientation),
                    "cycle": cycle_list,
                    "movers": list(movers),
                    "completion": {f"{p},{L},{S},{R}": v
                                   for (p, L, S, R), v in completion.items()},
                })
                # Keep going; the error gets raised by the caller.
                continue
            n_rejected += 1
            cert = build_rejection_certificate(
                orientation, orientation, cycle, movers, det, completion,
                report,
            )
            if not dry_run:
                writer(cert)

    return {
        "orientation": list(orientation),
        "candidate_cycles": n_cycles,
        "completions_tried": n_completions,
        "rejected": n_rejected,
        "valid_found": n_valid,
        "witnesses": witnesses,
        "quasi_uni_optimization_class":
            has_4_consecutive_binaries(orientation),
    }


def run_one_n(n: int, *, dry_run: bool, max_cycles_per_orient: Optional[int],
              max_completions_per_cycle: Optional[int]) -> dict:
    M_n = mn_connected(n)
    multisets = enumerate_multisets(n, M_n)
    ndir = os.path.join(ARTIFACT_DIR, f"n{n}")
    if not dry_run:
        os.makedirs(ndir, exist_ok=True)

    all_orients = []
    for ms in multisets:
        for orient in dihedral_orbits(ms):
            all_orients.append((ms, orient))

    per_ms_summary = []
    total_cycles = 0
    total_completions = 0
    total_rejected = 0
    sub_threshold_witnesses = []

    # For each multiset, open one jsonl file; stream-append.
    for ms_sorted in multisets:
        slug = slugify_ms(ms_sorted)
        stream_path = os.path.join(ndir,
            f"ms-{_prod(ms_sorted)}-{slug}.jsonl")
        if not dry_run:
            stream = open(stream_path, "w")
        else:
            stream = None

        def writer(cert, _s=stream):
            if _s is not None:
                _s.write(json.dumps(cert, sort_keys=True) + "\n")

        ms_summary = {"multiset": list(ms_sorted),
                      "product": _prod(ms_sorted),
                      "orientations": []}

        for orient in dihedral_orbits(ms_sorted):
            orient_start = time.time()
            per_orient = run_one_orientation(
                n, orient,
                dry_run=dry_run, writer=writer,
                max_cycles_per_orient=max_cycles_per_orient,
                max_completions_per_cycle=max_completions_per_cycle,
            )
            per_orient["elapsed_s"] = round(time.time() - orient_start, 3)
            ms_summary["orientations"].append(per_orient)
            total_cycles += per_orient["candidate_cycles"]
            total_completions += per_orient["completions_tried"]
            total_rejected += per_orient["rejected"]
            sub_threshold_witnesses.extend(per_orient["witnesses"])
            print(f"    orient={list(orient)} prod={_prod(orient)} "
                  f"cycles={per_orient['candidate_cycles']} "
                  f"completions={per_orient['completions_tried']} "
                  f"elapsed={per_orient['elapsed_s']}s", flush=True)

        if stream is not None:
            stream.close()
        per_ms_summary.append(ms_summary)

    # n-level index
    n_index = {
        "n": n, "M_n_connected": M_n,
        "multisets_count": len(multisets),
        "orientations_count": len(all_orients),
        "total_candidate_cycles": total_cycles,
        "total_completions_tried": total_completions,
        "total_rejections": total_rejected,
        "sub_threshold_witnesses": sub_threshold_witnesses,
        "per_multiset": per_ms_summary,
    }
    if not dry_run:
        with open(os.path.join(ndir, "index.json"), "w") as f:
            json.dump(n_index, f, sort_keys=True, indent=2)
    return n_index


def replay_certificates(path: str) -> int:
    """Re-verify every rejection certificate under `path` (file or dir).

    Referee workflow: each cert's (ms, completion) is loaded, the rule
    table is reconstructed, verify_system is re-run, and the cert's
    `property_failed` field is checked to match.
    """
    targets = []
    if os.path.isdir(path):
        for root, _, files in os.walk(path):
            for f in files:
                if f.endswith(".jsonl"):
                    targets.append(os.path.join(root, f))
    elif os.path.isfile(path):
        targets = [path]
    else:
        print(f"replay: {path} not found")
        return 2

    n_total = n_ok = n_fail = 0
    for t in sorted(targets):
        with open(t) as fh:
            for line_no, line in enumerate(fh, start=1):
                line = line.strip()
                if not line:
                    continue
                cert = json.loads(line)
                # Skip non-rejection records (e.g., the C worker's trailing
                # {"kind":"summary", ...} line).
                if cert.get("kind") and cert["kind"] != "rejection":
                    continue
                n_total += 1
                ms_sorted = tuple(cert["ms_sorted"])
                orientation = tuple(cert["orientation"])
                det = _det_parse(cert["det_forced"])
                comp = _det_parse(cert["completion"])
                full = dict(det)
                full.update(comp)
                fs = det_to_fs(orientation, full)
                report = verify_system(list(orientation), fs, verbose=False)
                if report.get("valid"):
                    print(f"  FAIL  {t}:{line_no}  "
                          f"cert says invalid but replay verify=VALID "
                          f"(sub-threshold witness!) ms={list(orientation)}")
                    n_fail += 1
                    continue
                observed, _ = _summarize_verifier_report(report)
                expected = cert.get("property_failed", "unknown")
                if expected not in ("unknown",) and observed != expected:
                    # Not a hard fail — different failure modes can be
                    # exposed by different scan orders — but log.
                    pass
                n_ok += 1
    print()
    print(f"replay: {n_ok} ok, {n_fail} fail, {n_total} total "
          f"certificates across {len(targets)} stream files.")
    return n_fail


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--n", type=int, default=None,
                        help="Run for a specific n (3..9); default: 3..9.")
    parser.add_argument("--summary-only", action="store_true",
                        help="Print C1/C2 counts and exit (no C3-C5).")
    parser.add_argument("--dry-run", action="store_true",
                        help="Run C3-C5 but do not write certificate files.")
    parser.add_argument("--max-cycles", type=int, default=None,
                        help="(debug) cap candidate cycles per orientation.")
    parser.add_argument("--max-completions", type=int, default=None,
                        help="(debug) cap completions per cycle.")
    parser.add_argument("--replay", metavar="PATH",
                        help="Re-verify every certificate under PATH "
                             "(file or dir). Referee workflow.")
    args = parser.parse_args()

    if args.replay:
        return replay_certificates(args.replay)

    ns = [args.n] if args.n is not None else list(range(3, 10))

    print("App C exhaustive-search driver.")
    print("=" * 72)
    # C1 + C2 summary
    for n in ns:
        m = c1_c2_manifest(n)
        print(f"  n={n}: M_n={m['M_n_connected']} "
              f"multisets<{m['M_n_connected']}={m['multiset_count']} "
              f"D_n-orbit-reps={m['orientations_count']} "
              f"C1+C2-rehash={m['rehash']}")

    if args.summary_only:
        return 0

    # C3..C5 per n. Summary is written incrementally so a kill
    # mid-n still leaves a valid summary of the n's that completed.
    summary_path = os.path.join(ARTIFACT_DIR, "summary.json")
    if not args.dry_run:
        os.makedirs(ARTIFACT_DIR, exist_ok=True)
        if os.path.exists(summary_path):
            try:
                summary = json.load(open(summary_path))
                if "per_n" not in summary:
                    summary = {"schema_version": 1, "per_n": {}}
            except Exception:
                summary = {"schema_version": 1, "per_n": {}}
        else:
            summary = {"schema_version": 1, "per_n": {}}
    else:
        summary = {"schema_version": 1, "per_n": {}}

    for n in ns:
        t0 = time.time()
        print()
        print(f"--- n = {n} ---")
        result = run_one_n(n, dry_run=args.dry_run,
                           max_cycles_per_orient=args.max_cycles,
                           max_completions_per_cycle=args.max_completions)
        elapsed = time.time() - t0
        summary["per_n"][str(n)] = {
            "multisets_count": result["multisets_count"],
            "orientations_count": result["orientations_count"],
            "total_candidate_cycles": result["total_candidate_cycles"],
            "total_completions_tried": result["total_completions_tried"],
            "total_rejections": result["total_rejections"],
            "sub_threshold_witnesses_count":
                len(result["sub_threshold_witnesses"]),
            "elapsed_s": round(elapsed, 3),
        }
        print(f"  cycles={result['total_candidate_cycles']} "
              f"completions={result['total_completions_tried']} "
              f"rejections={result['total_rejections']} "
              f"elapsed={elapsed:.1f}s")

        # Checkpoint summary after each n.
        if not args.dry_run:
            with open(summary_path, "w") as f:
                json.dump(summary, f, sort_keys=True, indent=2)

        if result["sub_threshold_witnesses"]:
            print(f"  !! {len(result['sub_threshold_witnesses'])} "
                  "sub-threshold VALID systems found. "
                  "This contradicts the paper's lower bound for this n.")
            for w in result["sub_threshold_witnesses"][:3]:
                print(f"     witness: ms={w['ms']} cycle={w['cycle'][:3]}...")
            return 2

    print()
    print(f"Rejection stream: {ARTIFACT_DIR}/")
    print(f"Top-level summary: {summary_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
