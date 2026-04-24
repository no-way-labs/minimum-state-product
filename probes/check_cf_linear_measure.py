#!/usr/bin/env python3
"""Find optimal measure for CF steps.
Check: for each CF step, what is (ΔPsi, Δfc)?
Can we find a linear combo α*Psi + β*fc that always decreases?
Also check max |ΔPsi| per unit |Δfc| on each step type."""

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def get_ms(n):
    ms = [3]*n; ms[0] = 2; ms[n-1] = 2; return ms

def get_trans(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

def frontierTypeVal(a, b):
    if a == b: return 0
    return (b + 3 - a) % 3

def W1(n, j):
    if j + 1 == n: return 0
    if j + 2 == n: return 1
    return j + 1

def W2(n, j):
    if j + 1 == n: return 0
    if j == 0: return n - 1
    return n - 1 - j

def psiWeightVal(n, j, a, b):
    if a == b: return 0
    if frontierTypeVal(a, b) == 1: return W1(n, j)
    return W2(n, j)

def psi(config, n):
    return sum(psiWeightVal(n, j, config[j], config[(j+1)%n]) for j in range(n))

def fc(config, n):
    return sum(1 for j in range(n) if config[j] != config[(j+1)%n])

def fire(config, n, i):
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    new_config = list(config); new_config[i] = new_S
    return tuple(new_config)

def build_good_set(n):
    config = tuple([0] * n)
    good = {config}
    cur = list(config)
    for phase in range(3):
        rng = range(n) if phase % 2 == 0 else range(n-1, -1, -1)
        for i in rng:
            new = fire(tuple(cur), n, i)
            if new is not None:
                cur = list(new)
                good.add(tuple(cur))
    return good

def compute_future_fc(n, good_set):
    ms = get_ms(n)
    from itertools import product as iproduct
    all_configs = list(iproduct(*[range(m) for m in ms]))
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)
    adj = {}
    for c in bad_configs:
        adj[c] = []
        for i in range(n):
            new = fire(c, n, i)
            if new is not None and new in bad_set:
                adj[c].append(new)
    ff = {c: fc(c, n) for c in bad_configs}
    changed = True
    iters = 0
    while changed:
        changed = False
        iters += 1
        for c in bad_configs:
            for s in adj[c]:
                if ff[s] > ff[c]:
                    ff[c] = ff[s]
                    changed = True
        if iters > len(bad_configs):
            break
    return ff, bad_set

for n in [5, 7, 9, 11]:
    print(f"\n{'='*60}")
    print(f"n={n}")
    good_set = build_good_set(n)
    ff, bad_set = compute_future_fc(n, good_set)

    # Collect all (ΔPsi, Δfc) pairs for CF steps
    deltas = []
    fcinc_max_dpsi = 0  # max ΔPsi on fc-increasing CF steps
    fcinc_max_ratio = 0  # max ΔPsi/Δfc on fc-increasing
    fcdec_max_dpsi = 0  # max ΔPsi on fc-decreasing CF steps (where ΔPsi > 0)
    fcdec_max_ratio = 0  # max ΔPsi/(-Δfc) on fc-decreasing

    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] != ff[c]:
                continue
            dpsi = psi(new, n) - psi(c, n)
            dfc = fc(new, n) - fc(c, n)
            deltas.append((dpsi, dfc))

            if dfc > 0:
                fcinc_max_dpsi = max(fcinc_max_dpsi, dpsi)
                fcinc_max_ratio = max(fcinc_max_ratio, dpsi / dfc)
            elif dfc < 0 and dpsi > 0:
                fcdec_max_dpsi = max(fcdec_max_dpsi, dpsi)
                fcdec_max_ratio = max(fcdec_max_ratio, dpsi / (-dfc))

    print(f"  CF steps: {len(deltas)}")
    print(f"  fc-inc: max ΔPsi = {fcinc_max_dpsi}, max ratio ΔPsi/Δfc = {fcinc_max_ratio:.2f}")
    print(f"  fc-dec: max ΔPsi (when >0) = {fcdec_max_dpsi}, max ratio ΔPsi/(-Δfc) = {fcdec_max_ratio:.2f}")

    # Check specific linear measures: α*Psi + β*(n-fc) for fc-inc and α*Psi + γ*fc for fc-dec
    # We need: α*ΔPsi + β*Δ(n-fc) < 0 for all CF steps
    # But β*Δ(n-fc) = -β*Δfc, so need α*ΔPsi - β*Δfc < 0

    # For fc=0: need α*ΔPsi < 0 → α > 0 (since ΔPsi < 0)
    # For fc-inc: need α*ΔPsi - β*Δfc < 0 → β > α*ΔPsi/Δfc (since Δfc>0, ΔPsi>0)
    # For fc-dec: need α*ΔPsi - β*Δfc < 0 → -β*Δfc < -α*ΔPsi → β*(-Δfc) > α*ΔPsi
    #   If ΔPsi < 0: auto satisfied for β > 0
    #   If ΔPsi > 0: β > α*ΔPsi/(-Δfc)
    # So need β > α * max(ΔPsi/Δfc for fc-inc, ΔPsi/(-Δfc) for fc-dec with ΔPsi>0)
    # The measure would be α*Psi + β*(n-fc)... wait, for fc-dec, Δ(n-fc) > 0.
    # So α*ΔPsi + β*Δ(n-fc) could be > 0 when β > 0 and Δ(n-fc) > 0.

    # Actually let me just try: M = K*(n-fc) + Psi. Need:
    # fc=0: ΔPsi < 0 ✓
    # fc-inc: -K*Δfc + ΔPsi < 0 → K > ΔPsi/Δfc → K > fcinc_max_ratio
    # fc-dec: K*(-Δfc) + ΔPsi < 0 → but -Δfc > 0, so K*(-Δfc) > 0. Need K*(-Δfc) + ΔPsi < 0
    #   i.e., ΔPsi < K*Δfc. Since Δfc < 0, this means ΔPsi < negative. Only works if ΔPsi < 0.
    #   But ΔPsi can be > 0 on fc-dec steps. Then need K*Δfc < -ΔPsi → K > ΔPsi/(-Δfc).
    #   Wait, Δfc < 0, so K*Δfc < 0. We need K*Δfc < -ΔPsi → -K*(-Δfc) < -ΔPsi → K*(-Δfc) > ΔPsi
    #   i.e., K > ΔPsi/(-Δfc). Since ΔPsi > 0 and -Δfc > 0, this gives K > positive.
    #   But for fc-inc: K > ΔPsi/Δfc, and now sign issue...
    #
    # Let me re-derive: M = K*(n-fc) + Psi
    # ΔM = -K*Δfc + ΔPsi
    # For fc-inc (Δfc > 0): ΔM = -K*Δfc + ΔPsi. Need < 0: K > ΔPsi/Δfc ✓ (K big enough)
    # For fc-dec (Δfc < 0): ΔM = -K*Δfc + ΔPsi = K*|Δfc| + ΔPsi.
    #   This is K*|Δfc| + ΔPsi. Since K > 0 and |Δfc| > 0, this is ≥ K + ΔPsi.
    #   If ΔPsi ≥ -K, then ΔM ≥ 0. FAILS for any K > 0 when ΔPsi > -K.
    #   In particular, if ΔPsi > 0, then ΔM > 0 always. FAILS.

    # So K*(n-fc) + Psi can NEVER decrease on fc-dec steps with ΔPsi > 0. Confirmed.

    # Try M = Psi - K*fc = Psi + K*(n-fc) - K*n
    # Same as above up to constant. Doesn't help.

    # What about M = Psi + K*(fc*(n-fc))?
    # Δ(fc*(n-fc)) = (fc+Δfc)*(n-fc-Δfc) - fc*(n-fc) = Δfc*(n-2fc-Δfc)
    # For small Δfc: ≈ Δfc*(n-2fc)
    # ΔM = ΔPsi + K*Δfc*(n-2fc-Δfc)

    # For fc-inc (Δfc=1): ΔM = ΔPsi + K*(n-2fc-1). Need < 0.
    #   If fc < (n-1)/2: n-2fc-1 > 0, so K makes it worse (ΔPsi > 0 already)
    #   If fc > (n-1)/2: n-2fc-1 < 0, so K helps

    # For fc-dec (Δfc=-1): ΔM = ΔPsi - K*(n-2fc+1)
    #   If fc < (n+1)/2: n-2fc+1 > 0, so -K*(positive) helps (makes ΔM more negative)
    #   If fc > (n+1)/2: n-2fc+1 < 0, so -K*(negative) = K*(positive), makes it worse

    # So this only helps in certain fc ranges. Not universal.

    # Conclusion: no linear measure works. Check quadratic?
    # M = Psi² + K*fc*(n-fc)?
    # ΔM = ΔPsi² + K*Δ(fc*(n-fc)) = (2*Psi + ΔPsi)*ΔPsi + K*Δfc*(n-2fc-Δfc)
    # Too complex to analyze.

    # Instead, let's just check: for which integer β does β*(n-fc) + Psi decrease on max CF steps?
    best_beta = None
    best_fail = len(deltas)
    for beta in range(-3*n, 3*n+1):
        fails = 0
        for (dpsi, dfc) in deltas:
            dm = -beta * dfc + dpsi
            if dm >= 0:
                fails += 1
        if fails < best_fail:
            best_fail = fails
            best_beta = beta
    print(f"  Best linear β*(n-fc)+Psi: β={best_beta}, fails={best_fail}/{len(deltas)}")

    # Check Psi alone
    psi_fails = sum(1 for (dpsi, dfc) in deltas if dpsi >= 0)
    print(f"  Psi alone fails: {psi_fails}/{len(deltas)}")

    # Check (n-fc)*B + Psi for B = max Psi
    B = n * n
    nfc_psi_fails = sum(1 for (dpsi, dfc) in deltas if -B*dfc + dpsi >= 0)
    print(f"  n²*(n-fc)+Psi fails: {nfc_psi_fails}/{len(deltas)}")

    # Check: are ALL failures on fc-changing steps?
    fceq_fails = sum(1 for (dpsi, dfc) in deltas if dfc == 0 and dpsi >= 0)
    print(f"  fc=0 failures (Psi alone): {fceq_fails}")

    # KEY CHECK: does fc-dec + (n-fc,Psi) Lex combo work?
    # Define: M(c) = 2*n*Psi(c) + (n - fc(c))
    # fc=0: ΔM = 2n*ΔPsi < 0 ✓ (since ΔPsi ≤ -1, ΔM ≤ -2n)
    # fc-inc (Δfc=k≥1): ΔM = 2n*ΔPsi - k. Need 2n*ΔPsi < k.
    #   ΔPsi can be up to ~n. So 2n*n vs k ≥ 1. FAILS.
    # Reversed: M = (n-fc) * B + Psi where B > n^2
    # fc=0: ΔM = ΔPsi < 0 ✓
    # fc-inc: ΔM = -B*Δfc + ΔPsi. B*Δfc ≥ B ≥ n². ΔPsi ≤ ~n. So ΔM < 0 ✓
    # fc-dec: ΔM = B*|Δfc| + ΔPsi ≥ B + min(ΔPsi). If ΔPsi > -B: ΔM > 0 ✗
    # Even if ΔPsi = -n², B*|Δfc| ≥ B = n². So ΔM ≥ 0. FAILS.

    # The issue is ALWAYS that fc-dec steps make (n-fc) increase.
    # There is NO linear measure in (fc, Psi, n-fc) that works.

    # Let's check: on fc-dec CF steps with ΔPsi > 0, what is Δfc?
    print(f"  fc-dec CF steps with ΔPsi > 0:")
    fcdec_dpsi_pos = [(dpsi, dfc) for (dpsi, dfc) in deltas if dfc < 0 and dpsi > 0]
    if fcdec_dpsi_pos:
        max_dpsi = max(d[0] for d in fcdec_dpsi_pos)
        min_dfc = min(d[1] for d in fcdec_dpsi_pos)
        max_dfc = max(d[1] for d in fcdec_dpsi_pos)
        print(f"    count={len(fcdec_dpsi_pos)}, max ΔPsi={max_dpsi}, Δfc range=[{min_dfc},{max_dfc}]")
        # Distribution
        from collections import Counter
        dist = Counter(fcdec_dpsi_pos)
        for (dp, df), cnt in sorted(dist.items()):
            print(f"    (ΔPsi={dp}, Δfc={df}): {cnt}")
    else:
        print(f"    NONE! All fc-dec CF steps have ΔPsi ≤ 0!")
        print(f"    *** (n-fc, Psi) Lex works for ALL CF steps! ***")
