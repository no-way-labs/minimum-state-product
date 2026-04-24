#!/usr/bin/env python3
"""Probe B1 Option 3 — does a (j, q, v') exist that makes S = {c', c''} closed?

Spec recap (from sk_b1_port_hour1_verdict.md Option 3):
  For a good cycle `gc` at n ≥ 5, pick step j with mover p_j, pick position
  q ∉ E_j := {p_{j-1}, p_j-1, p_j, p_j+1, p_{j+1}} (mod n) and value
  v' ∈ V_q \ {c_{j-1}[q]}. Define
    c' = c_{j-1}[q ↦ v']
    c'' = c_{j-1}[q ↦ v', p_j ↦ c_j[p_j]]  (which equals c'[p_j ↦ v])
  c' → c'' is forced via p_j (paper-verified).
  For closure we need c'' → some x in S = {c', c''} forced.

  The task description labels one condition as testing "c'' → c'" but we
  verify both interpretations explicitly (see deliverable for the caveat):

  Interpretation A (literal, "move at q"):
    Find step m in cycle with mover p_m = q, source triple at q =
    (c_{j-1}[q-1], v', c_{j-1}[q+1]), with target value c_{j-1}[q].
    Forced move lands at c''[q ↦ c_{j-1}[q]] = c_j ∈ C (cycle config!)
    — so actually closes into C, NOT S. This is what the task literally
    specifies.

  Interpretation B (geometric, "move at p_j"):
    Find step m in cycle with mover p_m = p_j, source triple at p_j =
    (c_j[p_j-1], c_j[p_j], c_j[p_j+1]), with target c_{j-1}[p_j].
    Forced move lands at c''[p_j ↦ c_{j-1}[p_j]] = c', which IS in S.
    This actually closes {c', c''}.

  We also apply the detOf EARLIEST-MATCH semantics strictly: find? returns
  the first k whose triple at that position matches; the target is
  configs[(k+1)%L][position]. If that first-k has position as NON-mover,
  then configs[k+1][position] equals configs[k][position] (stays) ⇒
  forcedOutput returns none (no forced move). So for a forced move, the
  EARLIEST match must be a mover step at the tested position.

Enumerate all sub-sharp multisets at n ∈ {5,6,7,8}; for each good cycle,
test both interpretations.

Outputs to sk_phase0_out/b1_option3.json.
"""
from __future__ import annotations
import importlib.util, json, os, sys, time
from collections import Counter, defaultdict
from itertools import product as iproduct
from math import prod

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_A_PATH = os.path.join(_HERE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py")
_spec = importlib.util.spec_from_file_location("probe_a", _A_PATH)
probe_a = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe_a)

enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart
m_n_sharp = probe_a.m_n_sharp


# ------------------------------------------------------------------
# sub-sharp multiset enumeration
# ------------------------------------------------------------------

def all_sub_sharp_multisets(n, max_state):
    """All position-tuples with each m_i in [2..max_state], prod < M_n."""
    Mn = m_n_sharp(n)
    out = []
    for t in iproduct(range(2, max_state + 1), repeat=n):
        if prod(t) >= Mn:
            continue
        out.append(t)
    return out


def canonical_subsharp_multisets(n, max_state):
    """Sorted canonical multisets with prod < M_n."""
    Mn = m_n_sharp(n)
    seen = set()
    for t in iproduct(range(2, max_state + 1), repeat=n):
        if prod(t) >= Mn:
            continue
        key = tuple(sorted(t))
        seen.add(key)
    return sorted(seen)


# ------------------------------------------------------------------
# detOf simulator
# ------------------------------------------------------------------

def build_cycle_arrays(cycle, movers, n):
    """From cycle configs list and movers, precompute useful arrays.
    cycle is a list of L configs (tuples), movers[i] is the mover at step i
    (taking cycle[i] -> cycle[(i+1) % L]).
    """
    L = len(cycle)
    return L


def detOf_at(cycle, movers, n, i, l, s, r):
    """Simulate Lean's detOf at position i with context (l, s, r).
    Returns (found, is_move, target) where:
      found = True if any step has triple at i equal to (l, s, r)
      is_move = True if at the EARLIEST matching step, i IS the mover (so
                a move edge may be induced; otherwise config stays)
      target = the successor value at position i at that step
               (configs[(k+1)%L][i])
    Note: if is_move is False (non-mover match), target == s (stay), and
    Lean's forcedOutput returns none.
    If found is False, returns (False, False, None).
    """
    L = len(cycle)
    for k in range(L):
        ck = cycle[k]
        if ck[(i - 1) % n] == l and ck[i] == s and ck[(i + 1) % n] == r:
            k1 = (k + 1) % L
            target = cycle[k1][i]
            is_move = (movers[k] == i)
            return True, is_move, target
    return False, False, None


def forced_output_move(cycle, movers, n, c, i):
    """Mirror Lean's forcedOutput: return target v if detOf at c's context at i
    returns some v with v != c[i], else None.
    """
    ctx_l = c[(i - 1) % n]
    ctx_s = c[i]
    ctx_r = c[(i + 1) % n]
    found, is_move, target = detOf_at(cycle, movers, n, i, ctx_l, ctx_s, ctx_r)
    if not found:
        return None
    if target == ctx_s:
        return None  # stay — no move
    return target


# ------------------------------------------------------------------
# Option 3 test per cycle
# ------------------------------------------------------------------

def test_cycle_option3(cycle, movers, ms, n):
    """For one good cycle, scan (j, q, v') and test both interpretations.

    Returns dict with:
      A_any_witness: True if ANY (j, q, v') yields a move at position q in c''
                     landing at c_{j-1}[q] via earliest-match mover-step
                     (Interpretation A).
      B_any_witness: True if ANY (j, q, v') yields a move at position p_j in
                     c'' landing at c_{j-1}[p_j] via earliest-match mover-step
                     (Interpretation B — this closes {c', c''}).
      *_witness: one representative (j, q, v') for each if found.
      A_count: count of (j, q, v') with A property.
      B_count: count of (j, q, v') with B property.
    """
    L = len(cycle)
    # Build valueSets
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])

    A_any = False
    B_any = False
    A_count = 0
    B_count = 0
    A_witness = None
    B_witness = None

    for j in range(L):
        # c_{j-1} is cycle[(j-1) % L] (=cycle[j-1] if j>=1 else cycle[L-1]).
        # Note: Lean uses configs as list of length L (configs list);
        # step j takes cycle[j-1] -> cycle[j] via mover p_{j-1}? Convention check.
        # In our enumeration, movers[k] is the mover at step k taking
        # cycle[k] -> cycle[(k+1)%L]. Sticking with this:
        #   at step m taking cycle[m] -> cycle[(m+1)%L] via movers[m].
        # We'll index the B1 construction by "step j" meaning the mover
        # p_j = movers[j], predecessor c_{j-1} = cycle[j], c_j = cycle[(j+1)%L].
        # Then p_{j-1} = movers[(j-1)%L], p_{j+1} = movers[(j+1)%L].
        p_j = movers[j]
        p_prev = movers[(j - 1) % L]
        p_next = movers[(j + 1) % L]
        c_jm1 = cycle[j]          # c_{j-1} in paper
        c_j = cycle[(j + 1) % L]  # c_j in paper

        excl = {p_prev, (p_j - 1) % n, p_j, (p_j + 1) % n, p_next}
        for q in range(n):
            if q in excl:
                continue
            for vprime in V[q]:
                if vprime == c_jm1[q]:
                    continue
                # c' and c'' definitions (explicit for clarity)
                # c' = c_{j-1}[q -> vprime]
                # c'' = c'[p_j -> c_j[p_j]]  (differs from c' only at p_j)
                # c''[q-1] = c_{j-1}[q-1] (q-1 ∉ {p_j-1, p_j, p_j+1} ⇒ p_j flip doesn't touch)
                # c''[q+1] = c_{j-1}[q+1]
                # c''[q]   = vprime
                # c''-triple at q = (c_{j-1}[q-1], vprime, c_{j-1}[q+1])
                tri_q_l = c_jm1[(q - 1) % n]
                tri_q_s = vprime
                tri_q_r = c_jm1[(q + 1) % n]

                # Interpretation A: forced move at q in c''
                found, is_move, target = detOf_at(
                    cycle, movers, n, q, tri_q_l, tri_q_s, tri_q_r)
                # Move condition: target != c''[q] = vprime, AND
                # is_move == True (earliest match is a mover-step) — otherwise
                # target == vprime anyway so target != c''[q] is False.
                # Interpretation A is "move lands at c_{j-1}[q]".
                if found and is_move and target == c_jm1[q] and target != vprime:
                    A_count += 1
                    if not A_any:
                        A_any = True
                        A_witness = {
                            'j': j, 'q': q, 'vprime': vprime,
                            'p_j': p_j, 'target_at_q': target,
                            'c_jm1_q': c_jm1[q],
                        }

                # Interpretation B: forced move at p_j in c'' lands at c'
                # c''-triple at p_j = (c_{j-1}[p_j-1], c_j[p_j], c_{j-1}[p_j+1])
                # but since q ∉ {p_j-1, p_j+1}, c_{j-1}[p_j±1] = c_j[p_j±1]
                # (p_j is the mover at step j taking c_{j-1} -> c_j; neighbors unchanged).
                # So triple = (c_j[p_j-1], c_j[p_j], c_j[p_j+1])
                tri_pj_l = c_j[(p_j - 1) % n]
                tri_pj_s = c_j[p_j]  # = v
                tri_pj_r = c_j[(p_j + 1) % n]
                found_B, is_move_B, target_B = detOf_at(
                    cycle, movers, n, p_j, tri_pj_l, tri_pj_s, tri_pj_r)
                # Move condition: target_B != c''[p_j] = c_j[p_j] = tri_pj_s
                # and target_B == c_{j-1}[p_j] (so landing at c').
                if (found_B and is_move_B
                        and target_B == c_jm1[p_j]
                        and target_B != tri_pj_s):
                    B_count += 1
                    if not B_any:
                        B_any = True
                        B_witness = {
                            'j': j, 'q': q, 'vprime': vprime,
                            'p_j': p_j, 'target_at_pj': target_B,
                            'c_jm1_pj': c_jm1[p_j],
                        }

    return {
        'L': L,
        'A_any_witness': A_any,
        'A_count': A_count,
        'A_witness': A_witness,
        'B_any_witness': B_any,
        'B_count': B_count,
        'B_witness': B_witness,
    }


# ------------------------------------------------------------------
# Main driver
# ------------------------------------------------------------------

def run_for_n(n, max_state, time_budget_per_ms, max_cycles_per_ms,
              L_min, L_max, ms_cap=None):
    Mn = m_n_sharp(n)
    ms_list = all_sub_sharp_multisets(n, max_state)
    if ms_cap is not None and len(ms_list) > ms_cap:
        # Sample deterministically by stride
        stride = len(ms_list) // ms_cap + 1
        ms_list = ms_list[::stride]
    canon_count = len(set(tuple(sorted(t)) for t in ms_list))
    print(f"\n=== n={n}  M_n={Mn}  #ms_tuples={len(ms_list)}  "
          f"canonical={canon_count}", flush=True)

    per_cycle_records = []
    ms_with_cycles = 0
    t_start = time.time()
    for idx, ms in enumerate(ms_list):
        # wall-time check
        if time.time() - t_start > 30 * 60:
            print(f"  [wall-time 30min exceeded at ms_idx={idx}]", flush=True)
            break
        cycles = enumerate_cycles_multistart(
            ms, n, L_min=L_min, L_max=L_max,
            time_budget=time_budget_per_ms, max_cycles=max_cycles_per_ms)
        if not cycles:
            continue
        ms_with_cycles += 1
        for cycle, movers, det in cycles:
            rec = test_cycle_option3(cycle, movers, ms, n)
            rec['ms'] = list(ms)
            per_cycle_records.append(rec)

    total = len(per_cycle_records)
    A_ok = sum(1 for r in per_cycle_records if r['A_any_witness'])
    B_ok = sum(1 for r in per_cycle_records if r['B_any_witness'])
    AB_ok = sum(1 for r in per_cycle_records
                if r['A_any_witness'] or r['B_any_witness'])

    summary = {
        'n': n,
        'M_n': Mn,
        'num_ms_tuples': len(ms_list),
        'ms_with_cycles': ms_with_cycles,
        'total_cycles': total,
        'A_any_count': A_ok,
        'B_any_count': B_ok,
        'either_count': AB_ok,
        'A_none_count': total - A_ok,
        'B_none_count': total - B_ok,
    }
    print(f"  n={n}  cycles={total}  A_ok={A_ok}/{total}  "
          f"B_ok={B_ok}/{total}  either={AB_ok}/{total}", flush=True)

    # Failure witnesses (small cycle so we can inspect)
    A_fails = [r for r in per_cycle_records if not r['A_any_witness']]
    B_fails = [r for r in per_cycle_records if not r['B_any_witness']]
    either_fails = [r for r in per_cycle_records
                    if not (r['A_any_witness'] or r['B_any_witness'])]
    if either_fails:
        # Sort by L to get smallest witnesses
        either_fails_sorted = sorted(either_fails, key=lambda r: (r['L'], r['ms']))
        summary['either_fail_witnesses'] = [
            {'ms': r['ms'], 'L': r['L']} for r in either_fails_sorted[:3]
        ]
    return summary, per_cycle_records


def main():
    outdir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(outdir, exist_ok=True)

    # Allow restricting to a single n via env var to enable fast iteration
    only_n = os.environ.get("ONLY_N")
    only_n = int(only_n) if only_n else None

    plans = [
        # (n, max_state, time_budget_per_ms, max_cycles_per_ms, L_min, L_max, ms_cap)
        (5, 6, 6.0, 200, 5, 22, None),
        (6, 5, 10.0, 100, 6, 24, None),
        (7, 4, 15.0, 60, 7, 24, None),
        # n=8: sample 60 ms_tuples (canonical=12), shorter budget
        (8, 4, 6.0, 25, 8, 22, 60),
    ]

    all_summary = {}
    all_sample_fail_cycles = {}

    for n, ms_state, tb, mc, Lmin, Lmax, cap in plans:
        if only_n is not None and n != only_n:
            continue
        summary, recs = run_for_n(n, ms_state, tb, mc, Lmin, Lmax, ms_cap=cap)
        all_summary[f'n={n}'] = summary
        # Capture a few full-cycle records for failures (for deliverable)
        fails = [r for r in recs if not (r['A_any_witness'] or r['B_any_witness'])]
        if fails:
            # Record smallest-L failure with full cycle info
            fails_sorted = sorted(fails, key=lambda r: (r['L'], r['ms']))
            pick = fails_sorted[0]
            all_sample_fail_cycles[f'n={n}'] = {
                'ms': pick['ms'],
                'L': pick['L'],
                # cycle and movers aren't in rec; re-enumerate will work
            }

    # Aggregate verdict
    total = sum(s['total_cycles'] for s in all_summary.values())
    either = sum(s['either_count'] for s in all_summary.values())
    print("\n" + "=" * 70)
    print(f"  AGGREGATE  cycles={total}  either_A_or_B_witness={either}/{total}")
    if total == 0:
        verdict = 'INCONCLUSIVE'
    elif either == total:
        verdict = 'GREEN'
    elif (total - either) / total < 0.05:
        verdict = 'YELLOW'
    else:
        verdict = 'RED'
    print(f"  VERDICT: {verdict}")
    print("=" * 70)

    out = {
        'per_n': all_summary,
        'sample_failures': all_sample_fail_cycles,
        'aggregate_verdict': verdict,
    }
    with open(os.path.join(outdir, 'b1_option3.json'), 'w') as f:
        json.dump(out, f, indent=2)
    print(f"\n  wrote sk_phase0_out/b1_option3.json")


if __name__ == "__main__":
    main()
