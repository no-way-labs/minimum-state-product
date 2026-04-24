"""
Fusion defect classification probe (2026-04-19 very late).

After CSP refutation and CTCL promotion, the fusion regime is the one
true anomaly: Σ_twists χ = 6 + ε with ε ∈ {0, 1, 2} at n ≤ 8. This
probe classifies ε by:

  - fusion event multiset (FDC-1, FDC-2 additivity)
  - adjacency pattern (FDC-4)
  - compression candidate: is ε the "excess charge" carried by the
    compressed representation of what would otherwise be a longer
    R/L word? (FDC-3)

Approach for additivity test: for each fusion event type e assign
candidate local charge χ_fusion(e) := Δi(e) + 2·Δq(e). Compare
Σ χ_fusion summed over fusion events to the total ε of the record;
additivity holds if ε = Σ_fusion χ - C for a fixed offset C.

Actually more directly:
  ε(record) = (Σ_all χ) − 6
            = (Σ_native χ_native + Σ_fusion χ_fusion) − 6
  If native events pair up balanced (as in DTNF-like sub-structure),
  Σ_native χ_native = (#native_R + #native_L) + stretch-imbalance.
  We already know native events are all R or L in fusion records.
  So we can decompose ε cleanly.

Input : probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json
Output: probes/sk_phase0_out/r4b_fusion_defect_2026-04-19.json
"""
import json
from collections import Counter, defaultdict
from pathlib import Path

IN_PATH = Path("probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json")
OUT_PATH = Path("probes/sk_phase0_out/r4b_fusion_defect_2026-04-19.json")


def signed_mod(x, m):
    r = x % m
    return r - m if r > m // 2 else r


def classify(dq, di):
    if dq == -1 and di >= 3:
        return ('R', di - 3)
    if dq == 2 and di <= -3:
        return ('L', (-di) - 3)
    if dq == -2 and di < 0:
        return ('F', (-di) - 3)
    return ('E', (dq, di))


def main():
    data = json.loads(IN_PATH.read_text())
    records = [r for r in data['records']
               if r['min_case_C'] == 6 and len(r['c_forensics']) == 6]

    print("=" * 72)
    print("Fusion defect classification")
    print("=" * 72)

    fusion_records = []
    for r in records:
        n = r['n']
        L = r['L']
        tw = sorted(r['c_forensics'], key=lambda f: f['t'])
        classes = []
        for f in tw:
            dq = signed_mod(f['dq_mod_n'], n)
            di = signed_mod(f['di_mod_L'], L)
            classes.append((classify(dq, di), dq, di, f['t'], f['p'], f['p_arity']))
        regime_tags = [c[0][0] for c in classes]
        if any(t == 'F' for t in regime_tags):
            continue   # fold regime — CTCL exact, not this probe's scope
        if not any(t == 'E' for t in regime_tags):
            continue   # dominant regime — CTCL exact
        fusion_records.append((r, classes))

    print(f"\nFusion records: {len(fusion_records)}")

    # Classification 1: fusion signature (multiset of E-type events)
    print("\n--- FDC classification by fusion event multiset ---")
    print(f"{'signature':<60}  {'ε=0':>4}  {'ε=1':>4}  {'ε=2':>4}  {'total':>5}")
    sig_eps = defaultdict(lambda: Counter())
    for r, classes in fusion_records:
        fusion_events = tuple(sorted(c[0][1] for c in classes if c[0][0] == 'E'))
        eps = sum(c[2] + 2 * c[1] for c in classes) - 6
        sig_eps[fusion_events][eps] += 1
    for sig, counts in sorted(sig_eps.items(),
                               key=lambda kv: -sum(kv[1].values())):
        total = sum(counts.values())
        sig_str = str(list(sig))
        print(f"  {sig_str:<58}  {counts[0]:>4}  {counts[1]:>4}  {counts[2]:>4}  {total:>5}")

    # Classification 2: native R/L structure per fusion signature
    print("\n--- Native R/L structure per fusion signature ---")
    sig_native = defaultdict(lambda: Counter())
    for r, classes in fusion_records:
        fusion_events = tuple(sorted(c[0][1] for c in classes if c[0][0] == 'E'))
        n_R = sum(1 for c in classes if c[0][0] == 'R')
        n_L = sum(1 for c in classes if c[0][0] == 'L')
        kR = sum(c[0][1] for c in classes if c[0][0] == 'R')
        kL = sum(c[0][1] for c in classes if c[0][0] == 'L')
        sig_native[fusion_events][(n_R, n_L, kR, kL)] += 1
    for sig, counts in sorted(sig_native.items(),
                               key=lambda kv: -sum(kv[1].values())):
        sig_str = str(list(sig))
        print(f"  {sig_str}")
        for native, c in counts.most_common():
            nR, nL, kR, kL = native
            print(f"    R{nR}L{nL}, k_R={kR}, k_L={kL}:  {c} records")

    # Classification 3: per-event local charge
    print("\n--- Per-event local charge χ (raw) ---")
    event_chi = {}
    event_counts = Counter()
    for r, classes in fusion_records:
        for c in classes:
            if c[0][0] == 'E':
                dq_di = c[0][1]
                chi = c[2] + 2 * c[1]
                event_chi[dq_di] = chi
                event_counts[dq_di] += 1
    print(f"{'event (Δq,Δi)':<20}  {'χ':>4}  {'count':>6}")
    for ev, chi in sorted(event_chi.items()):
        print(f"  {str(list(ev)):<20}  {chi:>+4}  {event_counts[ev]:>6}")

    # Additivity check: ε = Σ_fusion(χ) − 6 + native χ adjustment
    # For dominant 4R+2L with balance: native χ = 6, so if all 6 twists
    # are R/L, ε = 0.
    # For fusion records with m exceptions + (6-m) native R/L:
    #   native has #R=a, #L=b, a+b=6-m, kR=kL (we've already tested that
    #   native in fusion DOES have a/b not = 4/2). Let's measure.
    #
    # Key additivity hypothesis: ε = Σ_{event ∈ fusion} δ(event)
    # where δ(event) is a fixed per-event-type value.
    print("\n--- Additivity test: ε = Σ δ(event) per event type ---")
    print("If fusion charge decomposes additively, each event type has a fixed δ.")
    per_event_delta = {}
    for sig, counts in sig_eps.items():
        # For each record with signature sig, ε is counts key
        # If ε/|sig| is constant over all records with this signature, additivity holds per-signature.
        for eps, c in counts.items():
            if len(sig) == 0:
                continue
            # average contribution per event
            avg_delta = eps / len(sig)
            print(f"  sig={str(list(sig))}  |sig|={len(sig)}  ε={eps}  "
                  f"avg δ/event={avg_delta:.3f}  ({c} records)")

    # Try to solve δ per event type linearly across signatures
    print("\n--- Linear solve: δ(event type) ---")
    from itertools import combinations
    # Enumerate unique event types
    all_types = sorted(set(t for sig in sig_eps for t in sig))
    print(f"  Event types: {[list(t) for t in all_types]}")
    # Build system: for each signature+ε, equation Σ δ(t) · count(t in sig) = ε
    # If every record with signature sig has the SAME ε, we have one equation per signature.
    eqs = []   # (coeffs_dict, rhs)
    for sig, counts in sig_eps.items():
        eps_vals = list(counts.keys())
        if len(set(eps_vals)) == 1:
            eps = eps_vals[0]
            coeffs = Counter(sig)
            eqs.append((coeffs, eps))
        else:
            print(f"  Signature {list(sig)} has MULTIPLE ε values: {dict(counts)} — additivity FAILS")
    # Solve the linear system (small, use direct)
    if eqs:
        # Build matrix
        import numpy as np
        A = []
        b = []
        for coeffs, rhs in eqs:
            row = [coeffs.get(t, 0) for t in all_types]
            A.append(row)
            b.append(rhs)
        A = np.array(A, dtype=float)
        b = np.array(b, dtype=float)
        sol, resid, rank, _ = np.linalg.lstsq(A, b, rcond=None)
        residual = A @ sol - b
        print(f"  δ values (least-squares solution):")
        for t, d in zip(all_types, sol):
            print(f"    δ({list(t)}) = {d:+.3f}")
        print(f"  residual (per-equation): {residual}")
        print(f"  max |residual|: {abs(residual).max():.6f}")
        if abs(residual).max() < 1e-9:
            print("  → FDC-2 ADDITIVITY HOLDS exactly with these δ values.")
        else:
            print("  → Additivity does NOT hold as a simple per-type sum.")

    # Adjacency analysis: do fusion events cluster in time or arity?
    print("\n--- Adjacency analysis ---")
    adj_counter = Counter()
    for r, classes in fusion_records:
        fusion_ts = sorted(c[3] for c in classes if c[0][0] == 'E')
        if len(fusion_ts) < 2:
            continue
        # Check cyclic gaps
        n_twists = 6
        gaps = []
        for i in range(len(fusion_ts)):
            g = (fusion_ts[(i + 1) % len(fusion_ts)] - fusion_ts[i]) % n_twists
            gaps.append(g)
        gaps_sorted = tuple(sorted(gaps))
        adj_counter[gaps_sorted] += 1
    print(f"  Cyclic-gap patterns between fusion events:")
    for gaps, c in adj_counter.most_common():
        print(f"    gaps={gaps}:  {c} records")

    def to_j(obj):
        if isinstance(obj, dict):
            return {str(k): to_j(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [to_j(x) for x in obj]
        return obj

    out = {
        'fusion_records': len(fusion_records),
        'sig_eps': to_j({str(list(k)): dict(v) for k, v in sig_eps.items()}),
        'sig_native': to_j({str(list(k)): {str(x): c for x, c in v.items()}
                            for k, v in sig_native.items()}),
        'event_chi': {str(list(k)): {'chi': v, 'count': event_counts[k]}
                      for k, v in event_chi.items()},
        'adj_counter': {str(list(k)): v for k, v in adj_counter.items()},
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(out, indent=2, default=str))
    print(f"\nWrote {OUT_PATH.resolve()}")


if __name__ == "__main__":
    main()
