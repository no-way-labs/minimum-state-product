#!/usr/bin/env python3
"""Probe C — Forced-successor chain closure for canonical Hamming-1 witness.

Extends probe_sk_hamming1_empty_discriminator_2026-04-17.py (Probe A).
For each good cycle, compute Probe A's canonical lex-first survivor c* in
peel(N_1 ∩ VC_NG). Then:

  1. Trace the forced-successor CHAIN starting at c*. At each step, the
     "forced successors" of c are the non-good configs reachable via a
     defined forced move (det entry with val ≠ c[p]) at some position p.
     We follow the unique-lex successor when the set is a singleton; when
     it branches we record the branching and continue with the lex-first
     option.
  2. Track termination mode (dead-end / loop / reach-cycle) and the
     sequence of Hamming distances to the cycle.
  3. Compute the minimal forward-closed set T(c*) ⊆ VC_NG reachable from
     c* via forced moves. Report |T(c*)|.
  4. Aggregate.

Lean relevance: if T(c*) is small and always contained in VC_NG, the Lean
witness-membership proof for SK is: exhibit T, prove it is closed under
`hasForcedNeighborIn` (each config has at least one forced neighbor in
T), invoke `SK_closed`.

Reuses Probe A's functions via import.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter, deque
import importlib.util, json, csv, os, sys, time

sys.setrecursionlimit(100000)

# --- Import Probe A module dynamically ---
_HERE = os.path.dirname(os.path.abspath(__file__))
_A_PATH = os.path.join(_HERE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py")
_spec = importlib.util.spec_from_file_location("probe_a", _A_PATH)
probe_a = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe_a)

enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart
build_N1_and_peel = probe_a.build_N1_and_peel
m_n_sharp = probe_a.m_n_sharp


# --- Forced-successor machinery (global, not restricted to N_1) ---

def forced_successors(c, det, n, cycle_set):
    """Return list of (p, new_config) for each defined forced move at c
    whose target is in VC_NG (non-good).

    A forced move at position p exists iff det has key (p, c[p-1], c[p],
    c[p+1]) and the stored value ≠ c[p]. We only list targets outside
    the good cycle (VC_NG = non-good).
    """
    out = []
    for p in range(n):
        ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        if ctx not in det:
            continue
        val = det[ctx]
        if val == c[p]:
            continue
        nc = list(c)
        nc[p] = val
        nc = tuple(nc)
        if nc in cycle_set:
            # forced move lands on cycle — record but note
            out.append(('cycle', p, nc))
        else:
            out.append(('ng', p, nc))
    return out


def hamming(c, cycle_set):
    """Minimum Hamming distance from c to any config in cycle_set."""
    n = len(c)
    best = n
    for cc in cycle_set:
        d = sum(1 for i in range(n) if c[i] != cc[i])
        if d < best:
            best = d
    return best


def trace_chain(c_star, det, n, cycle_set, max_steps=2000):
    """Follow lex-first forced-successor chain in VC_NG from c*.

    At each step, list forced successors (NG only). If empty -> dead-end.
    If nonempty but all targets in good cycle -> reach-cycle (record).
    Else pick lex-first NG target; if already visited -> loop (record
    loop length).

    Returns dict with keys: path, termination, loop_len (if loop),
    hamming_trajectory, branching_history (list of branchings observed).
    """
    path = [c_star]
    visited_order = {c_star: 0}
    hammings = [hamming(c_star, cycle_set)]
    branchings = []  # (step, #NG choices)
    termination = None
    loop_len = None
    reach_cycle_step = None

    for step in range(max_steps):
        c = path[-1]
        succs = forced_successors(c, det, n, cycle_set)
        ng = [(p, nc) for (kind, p, nc) in succs if kind == 'ng']
        on_cycle = [(p, nc) for (kind, p, nc) in succs if kind == 'cycle']

        if len(ng) > 1:
            branchings.append((step, len(ng)))

        if not ng and not on_cycle:
            termination = 'dead_end'
            break
        if not ng and on_cycle:
            termination = 'reach_cycle'
            reach_cycle_step = step
            break

        # pick lex-first NG target
        ng.sort(key=lambda x: x[1])
        nc = ng[0][1]
        if nc in visited_order:
            termination = 'loop'
            loop_len = len(path) - visited_order[nc]
            break
        visited_order[nc] = len(path)
        path.append(nc)
        hammings.append(hamming(nc, cycle_set))

    if termination is None:
        termination = 'max_steps'

    return {
        'path_length': len(path),
        'termination': termination,
        'loop_len': loop_len,
        'reach_cycle_step': reach_cycle_step,
        'hamming_trajectory': hammings,
        'max_hamming': max(hammings),
        'branchings': branchings,
        'num_branchings': len(branchings),
    }


def forward_closure(c_star, det, n, cycle_set, cap=100000):
    """Compute T(c*) = set of all VC_NG configs forward-reachable from c*
    via forced moves (without entering the good cycle).

    Returns dict with T (frozenset), size, and whether the closure is
    VC_NG-closed (every c in T has at least one forced successor in T,
    or forced successor on cycle).
    """
    T = {c_star}
    frontier = deque([c_star])
    reach_cycle_configs = set()  # NG configs in T that have a cycle-forced successor
    dead_ends = set()  # NG configs in T with NO forced successor
    any_cycle_only = set()  # NG configs with forced successors ONLY going to cycle
    while frontier:
        c = frontier.popleft()
        succs = forced_successors(c, det, n, cycle_set)
        ng_succs = [nc for (kind, p, nc) in succs if kind == 'ng']
        on_cycle = [nc for (kind, p, nc) in succs if kind == 'cycle']
        if not succs:
            dead_ends.add(c)
            continue
        if not ng_succs and on_cycle:
            any_cycle_only.add(c)
            reach_cycle_configs.add(c)
            continue
        if on_cycle:
            reach_cycle_configs.add(c)
        for nc in ng_succs:
            if nc not in T:
                T.add(nc)
                frontier.append(nc)
                if len(T) >= cap:
                    return {'T': T, 'size': len(T), 'truncated': True,
                            'dead_ends': dead_ends,
                            'reach_cycle_configs': reach_cycle_configs,
                            'any_cycle_only': any_cycle_only}
    # Closure analysis: every c in T must have either:
    #   (a) a forced successor in T (good: keeps it in SK if T ⊆ SK), or
    #   (b) forced successor ONLY going to cycle — but then c is NOT in SK
    #       because cycle is good and SK is inside VC_NG.
    non_closed = []
    for c in T:
        succs = forced_successors(c, det, n, cycle_set)
        ng_succs = [nc for (kind, p, nc) in succs if kind == 'ng']
        on_cycle = [nc for (kind, p, nc) in succs if kind == 'cycle']
        if not succs:
            non_closed.append(('dead', c))
        elif not ng_succs:
            # only cycle-bound forced moves — NOT in SK
            non_closed.append(('cycle_only', c))
        else:
            if not any(nc in T for nc in ng_succs):
                non_closed.append(('escape', c))  # should never happen (T is closure)
    return {
        'T': T,
        'size': len(T),
        'truncated': False,
        'dead_ends': dead_ends,
        'reach_cycle_configs': reach_cycle_configs,
        'any_cycle_only': any_cycle_only,
        'non_closed': non_closed,
        'num_non_closed': len(non_closed),
    }


def canonical_witness_from_peel(peel_set, provenance, V, ms, n, L):
    """Pick lex-first peel survivor; confirm Probe A's q=n-2 fingerprint."""
    if not peel_set:
        return None
    c_star = sorted(peel_set)[0]
    # verify signature (for logging)
    q_info = provenance[c_star]  # list of (q, v, i)
    q_list = sorted({q for (q, v, i) in q_info})
    return c_star, q_list


# --- Main run ---

def run_one(n, ms, L_min, L_max, time_budget, max_cycles):
    cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                          time_budget=time_budget,
                                          max_cycles=max_cycles)
    records = []
    for cycle, movers, det in cycles:
        L = len(movers)
        N1, adj, peel_set, provenance, V, move_entries, cycle_set = build_N1_and_peel(
            ms, n, cycle, det)
        rec = {
            'n': n, 'ms': list(ms), 'L': L,
            'N1_size': len(N1), 'peel_size': len(peel_set),
            'cycle_size': len(cycle_set),
        }
        if not peel_set:
            rec['witness'] = None
            records.append(rec)
            continue
        cw = canonical_witness_from_peel(peel_set, provenance, V, ms, n, L)
        if cw is None:
            records.append(rec)
            continue
        c_star, q_list = cw
        # Trace chain
        chain = trace_chain(c_star, det, n, cycle_set, max_steps=2000)
        # Forward closure
        fc = forward_closure(c_star, det, n, cycle_set, cap=100000)

        # Every c in chain path: is it in VC_NG? (c_star is by construction,
        # forced-successor chain only hops to ng targets)
        # Verify chain in VC_NG:
        chain_in_vcng = True  # by construction

        # Is T(c*) ⊆ peel set (i.e., inside N_1)?
        T = fc['T']
        T_in_N1 = sum(1 for c in T if c in N1)

        # SK-local peel: iteratively remove T configs with no NG neighbor in T
        cur = set(T)
        peel_rounds = 0
        while True:
            peel_rounds += 1
            to_remove = set()
            for c in cur:
                has_in = False
                for (kind, p, nc) in forced_successors(c, det, n, cycle_set):
                    if kind == 'ng' and nc in cur:
                        has_in = True; break
                if not has_in:
                    to_remove.add(c)
            if not to_remove:
                break
            cur -= to_remove
            if peel_rounds > 30:
                break
        SK_local_size = len(cur)
        c_star_in_SK_local = c_star in cur

        rec['witness'] = {
            'c_star': list(c_star),
            'q_list': q_list,
            'chain_length': chain['path_length'],
            'termination': chain['termination'],
            'loop_len': chain['loop_len'],
            'reach_cycle_step': chain['reach_cycle_step'],
            'hamming_trajectory': chain['hamming_trajectory'][:20],  # truncate for storage
            'max_hamming_in_chain': chain['max_hamming'],
            'num_branchings_in_chain': chain['num_branchings'],
            'T_size': fc['size'],
            'T_truncated': fc['truncated'],
            'T_in_N1': T_in_N1,
            'T_fraction_in_N1': T_in_N1 / max(1, fc['size']),
            'T_dead_ends': len(fc.get('dead_ends', [])),
            'T_any_cycle_only': len(fc.get('any_cycle_only', [])),
            'T_non_closed': fc.get('num_non_closed', 0),
            'SK_local_size': SK_local_size,
            'SK_local_peel_rounds': peel_rounds,
            'c_star_in_SK_local': c_star_in_SK_local,
        }
        records.append(rec)
    return records


def main():
    out_dir = os.path.join(_HERE, 'sk_hamming1_chain_closure_out')
    os.makedirs(out_dir, exist_ok=True)

    # n=5..9 per user instruction
    plans = [
        (5, 15.0, 8, 13, [(2,2,2,3,3), (2,2,3,3,3), (2,2,2,3,4)]),
        (6, 20.0, 8, 15, [(2,2,2,3,3,3), (2,2,3,2,3,3), (2,2,2,2,3,3)]),
        (7, 30.0, 6, 17, [(2,2,2,3,3,3,3), (2,2,3,2,3,3,3), (2,2,2,2,3,3,3)]),
        (8, 45.0, 5, 19, [(2,2,2,3,3,3,3,3), (2,2,3,2,3,3,3,3), (2,2,2,2,3,3,3,3)]),
        (9, 60.0, 4, 22, [(2,2,2,3,3,3,3,3,3), (2,2,3,2,3,3,3,3,3), (2,2,2,2,3,3,3,3,3)]),
    ]

    all_records = []
    t_start = time.time()
    for n, tb, mc, L_max, picked in plans:
        Mn = m_n_sharp(n)
        picked = [ms for ms in picked if __import__('math').prod(ms) < Mn]
        print(f"\n=== n={n}  M_n={Mn}  picked={picked}", flush=True)
        for ms in picked:
            if time.time() - t_start > 55 * 60:
                print("  [wall-time cap reached; stopping]", flush=True)
                break
            t0 = time.time()
            recs = run_one(n, ms, L_min=2*n+2, L_max=L_max,
                            time_budget=tb, max_cycles=mc)
            dt = time.time() - t0
            if not recs:
                print(f"  ms={ms}  no cycles found in {dt:.1f}s", flush=True)
                continue
            # summary
            with_w = [r for r in recs if r.get('witness')]
            chain_lens = [r['witness']['chain_length'] for r in with_w]
            T_sizes = [r['witness']['T_size'] for r in with_w]
            terms = Counter(r['witness']['termination'] for r in with_w)
            max_h = max((r['witness']['max_hamming_in_chain'] for r in with_w), default=0)
            print(f"  ms={ms}  {len(recs)} cycles  chains={chain_lens}  "
                  f"T_sizes={T_sizes}  term={dict(terms)}  maxH={max_h}  dt={dt:.1f}s",
                  flush=True)
            all_records.extend(recs)

    # --- Save ---
    json_path = os.path.join(out_dir, 'records.json')
    with open(json_path, 'w') as f:
        json.dump(all_records, f, indent=2)

    csv_path = os.path.join(out_dir, 'summary.csv')
    with open(csv_path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['n','ms','L','cycle_size','N1_size','peel_size',
                    'chain_length','termination','loop_len','reach_cycle_step',
                    'max_hamming_in_chain','num_branchings',
                    'T_size','T_in_N1','T_fraction_in_N1',
                    'T_dead_ends','T_any_cycle_only','T_non_closed',
                    'SK_local_size','SK_local_peel_rounds','c_star_in_SK_local'])
        for r in all_records:
            wit = r.get('witness') or {}
            w.writerow([
                r['n'], r['ms'], r['L'], r.get('cycle_size'),
                r['N1_size'], r['peel_size'],
                wit.get('chain_length'), wit.get('termination'),
                wit.get('loop_len'), wit.get('reach_cycle_step'),
                wit.get('max_hamming_in_chain'), wit.get('num_branchings_in_chain'),
                wit.get('T_size'), wit.get('T_in_N1'),
                f"{wit.get('T_fraction_in_N1', 0):.3f}" if wit else None,
                wit.get('T_dead_ends'), wit.get('T_any_cycle_only'),
                wit.get('T_non_closed'),
                wit.get('SK_local_size'), wit.get('SK_local_peel_rounds'),
                wit.get('c_star_in_SK_local'),
            ])

    # --- Aggregate report ---
    print("\n" + "=" * 80)
    print("PROBE C — chain closure summary")
    print("=" * 80)
    by_n = defaultdict(list)
    for r in all_records:
        by_n[r['n']].append(r)
    grand_chain = []
    grand_T = []
    grand_max_h = []
    grand_term = Counter()
    for n in sorted(by_n):
        recs = by_n[n]
        with_w = [r for r in recs if r.get('witness')]
        chain_lens = [r['witness']['chain_length'] for r in with_w]
        T_sizes = [r['witness']['T_size'] for r in with_w]
        max_hs = [r['witness']['max_hamming_in_chain'] for r in with_w]
        terms = Counter(r['witness']['termination'] for r in with_w)
        loops = [r['witness']['loop_len'] for r in with_w
                 if r['witness']['termination'] == 'loop']
        branches = [r['witness']['num_branchings_in_chain'] for r in with_w]
        T_frac_in_N1 = [r['witness']['T_fraction_in_N1'] for r in with_w]
        SK_loc_sizes = [r['witness']['SK_local_size'] for r in with_w]
        SK_loc_rounds = [r['witness']['SK_local_peel_rounds'] for r in with_w]
        cstar_in_SK = [r['witness']['c_star_in_SK_local'] for r in with_w]
        print(f"  n={n:2d}  cycles_with_peel={len(with_w)}/{len(recs)}")
        print(f"    SK_local  min/avg/max = "
              f"{min(SK_loc_sizes) if SK_loc_sizes else 0}/"
              f"{(sum(SK_loc_sizes)/len(SK_loc_sizes)) if SK_loc_sizes else 0:.2f}/"
              f"{max(SK_loc_sizes) if SK_loc_sizes else 0}")
        print(f"    SK_peel_rounds max = {max(SK_loc_rounds) if SK_loc_rounds else 0}")
        print(f"    c_star_in_SK_local = {sum(cstar_in_SK)}/{len(cstar_in_SK)}")
        print(f"    chain_len  min/avg/max = "
              f"{min(chain_lens) if chain_lens else 0}/"
              f"{(sum(chain_lens)/len(chain_lens)) if chain_lens else 0:.2f}/"
              f"{max(chain_lens) if chain_lens else 0}")
        print(f"    T_size     min/avg/max = "
              f"{min(T_sizes) if T_sizes else 0}/"
              f"{(sum(T_sizes)/len(T_sizes)) if T_sizes else 0:.2f}/"
              f"{max(T_sizes) if T_sizes else 0}")
        print(f"    max_hamming_in_chain   = "
              f"{max(max_hs) if max_hs else 0}  (across all cycles)")
        print(f"    termination = {dict(terms)}")
        if loops:
            print(f"    loop_len  min/avg/max = "
                  f"{min(loops)}/{sum(loops)/len(loops):.2f}/{max(loops)}")
        print(f"    branchings  min/avg/max = "
              f"{min(branches) if branches else 0}/"
              f"{(sum(branches)/len(branches)) if branches else 0:.2f}/"
              f"{max(branches) if branches else 0}")
        print(f"    T_frac_in_N1 min/avg/max = "
              f"{min(T_frac_in_N1) if T_frac_in_N1 else 0:.3f}/"
              f"{(sum(T_frac_in_N1)/len(T_frac_in_N1)) if T_frac_in_N1 else 0:.3f}/"
              f"{max(T_frac_in_N1) if T_frac_in_N1 else 0:.3f}")
        grand_chain.extend(chain_lens)
        grand_T.extend(T_sizes)
        grand_max_h.extend(max_hs)
        grand_term.update(terms)
    print("\n  GRAND TOTAL")
    print(f"    chain_len  max = {max(grand_chain) if grand_chain else 0}")
    print(f"    T_size     max = {max(grand_T) if grand_T else 0}")
    print(f"    max Hamming in any chain = {max(grand_max_h) if grand_max_h else 0}")
    print(f"    termination = {dict(grand_term)}")
    print(f"\n  raw JSON: {json_path}")
    print(f"  summary CSV: {csv_path}")


if __name__ == "__main__":
    main()
