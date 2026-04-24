#!/usr/bin/env python3
"""
Verify PhiFull = fc + 1{c[0]=1, c[1]=2, c[n-1]=1} at n=14.
Uses numpy for speed on the ~2M config space.
"""

import sys, time, numpy as np
from collections import defaultdict

sys.stdout.reconfigure(line_buffering=True)

# ── CUP-2 tables as numpy arrays ────────────────────────────────────────
# T_mid[S][L][R] -> output
T_mid_arr = np.array([
    [[0,0,0],[1,0,0],[2,0,0]],  # S=0
    [[0,1,1],[1,1,1],[2,1,1]],  # S=1
    [[0,0,2],[1,0,2],[2,0,2]],  # S=2
], dtype=np.int8)

T_lo_adj_arr = np.array([
    [[0,0,0],[1,0,0],[-1,-1,-1]],  # S=0, L in {0,1}
    [[0,1,1],[1,1,1],[-1,-1,-1]],  # S=1
    [[0,0,2],[1,0,2],[-1,-1,-1]],  # S=2
], dtype=np.int8)

T_hi_adj_arr = np.array([
    [[0,0],[1,0],[2,0]],  # S=0
    [[0,1],[1,1],[2,1]],  # S=1
    [[0,0],[1,0],[2,0]],  # S=2
], dtype=np.int8)

# T_low[S][L][R] -> output, S,L in {0,1}, R in {0,1,2}
T_low_arr = np.array([
    [[0,0,0],[0,0,0]],  # S=0
    [[0,0,0],[0,1,0]],  # S=1
], dtype=np.int8)

# T_high[S][L][R] -> output, S,R in {0,1}, L in {0,1,2}
T_high_arr = np.array([
    [[0,0],[0,0],[0,0]],  # S=0
    [[0,1],[0,1],[0,1]],  # S=1
], dtype=np.int8)

def build_all(n):
    """Build config array and precompute everything."""
    # Config encoding: product of moduli
    mods = [2 if i == 0 or i == n-1 else 3 for i in range(n)]
    total = 1
    for m in mods:
        total *= m

    # Build all configs as numpy array
    configs = np.zeros((total, n), dtype=np.int8)
    idx = np.arange(total)
    for i in range(n-1, -1, -1):
        configs[:, i] = idx % mods[i]
        idx //= mods[i]

    return configs, total

def compute_outputs(n, configs):
    """Compute output for each proc at each config."""
    total = len(configs)
    outputs = np.copy(configs)

    # Position 0: T_low[S, L, R] where S=c[0], L=c[n-1], R=c[1]
    outputs[:, 0] = T_low_arr[configs[:, 0], configs[:, n-1], configs[:, 1]]

    # Position 1: T_lo_adj[S, L, R] where S=c[1], L=c[0], R=c[2]
    outputs[:, 1] = T_lo_adj_arr[configs[:, 1], configs[:, 0], configs[:, 2]]

    # Positions 2..n-3: T_mid[S, L, R]
    for j in range(2, n-2):
        outputs[:, j] = T_mid_arr[configs[:, j], configs[:, j-1], configs[:, j+1]]

    # Position n-2: T_hi_adj[S, L, R] where S=c[n-2], L=c[n-3], R=c[n-1]
    outputs[:, n-2] = T_hi_adj_arr[configs[:, n-2], configs[:, n-3], configs[:, n-1]]

    # Position n-1: T_high[S, L, R] where S=c[n-1], L=c[n-2], R=c[0]
    outputs[:, n-1] = T_high_arr[configs[:, n-1], configs[:, n-2], configs[:, 0]]

    return outputs

def compute_fc(n, configs):
    """Compute fc for all configs."""
    shifted = np.roll(configs, -1, axis=1)
    return np.sum(configs != shifted, axis=1)

def compute_privileged(n, configs, outputs):
    """Compute privileged mask: privileged[i, j] = (output[j] != config[j])"""
    return outputs != configs

def compute_tp(n, configs):
    """Compute TP invariant (e2, i21, ew) for all configs."""
    e2 = np.zeros(len(configs), dtype=np.int32)
    i21 = np.zeros(len(configs), dtype=np.int32)
    ew = np.zeros(len(configs), dtype=np.int32)
    for j in range(2, n-2):
        is2 = configs[:, j] == 2
        r = configs[:, (j+1) % n]
        is_01 = (r == 0) | (r == 1)
        mask = is2 & is_01
        e2 += mask.astype(np.int32)
        ew += mask.astype(np.int32) * j
        i21 += (is2 & (r == 1)).astype(np.int32)
    return e2, i21, ew

def main():
    n = 14
    print(f"PhiFull formula verification at n={n}")
    t0 = time.time()

    configs, total = build_all(n)
    print(f"  {total} configs built ({time.time()-t0:.1f}s)")

    outputs = compute_outputs(n, configs)
    fc_vals = compute_fc(n, configs)
    priv = compute_privileged(n, configs, outputs)
    priv_count = np.sum(priv, axis=1)

    # Good configs: exactly 1 privileged
    good_mask = priv_count == 1
    bad_mask = ~good_mask
    n_good = np.sum(good_mask)
    n_bad = np.sum(bad_mask)
    print(f"  {n_good} good, {n_bad} bad ({time.time()-t0:.1f}s)")

    # Compute TP invariant
    e2, i21, ew = compute_tp(n, configs)
    print(f"  TP computed ({time.time()-t0:.1f}s)")

    # PhiFull via Bellman-Ford
    # For each bad config, we need to find max fc reachable via TP-preserving bad moves
    phi = np.where(good_mask, 0, fc_vals).astype(np.int32)

    # Build adjacency: for each config, for each privileged position,
    # compute successor and check TP + bad
    # This is expensive for n=14 (~2M configs * 14 positions), so let's use vectorized approach

    # For each position p, compute:
    # - which configs have p privileged AND are bad
    # - the successor config after firing p
    # - which successors are bad and TP-preserving

    print(f"  Building TP edges...", end=" ", flush=True)

    # Encode configs as integers for fast lookup
    mods = [2 if i == 0 or i == n-1 else 3 for i in range(n)]
    weights = np.ones(n, dtype=np.int64)
    for i in range(n-2, -1, -1):
        weights[i] = weights[i+1] * mods[i+1]
    config_ids = np.sum(configs.astype(np.int64) * weights, axis=1)

    # For fast lookup: config_id -> index
    id_to_idx = np.full(int(config_ids.max()) + 1, -1, dtype=np.int32)
    id_to_idx[config_ids] = np.arange(total, dtype=np.int32)

    # Bellman-Ford iterations
    for iteration in range(3 * n):
        changed = False
        for p in range(n):
            # Mask: bad AND privileged at p
            mask = bad_mask & priv[:, p]
            if not np.any(mask):
                continue

            # Indices of these configs
            idxs = np.where(mask)[0]

            # Build successor configs
            succ_configs = configs[idxs].copy()
            succ_configs[:, p] = outputs[idxs, p]

            # Compute successor IDs
            succ_ids = np.sum(succ_configs.astype(np.int64) * weights, axis=1)

            # Look up successor indices
            valid_id = (succ_ids >= 0) & (succ_ids < len(id_to_idx))
            succ_idxs = np.full(len(idxs), -1, dtype=np.int32)
            succ_idxs[valid_id] = id_to_idx[succ_ids[valid_id]]

            # Filter: successor exists and is bad
            valid = (succ_idxs >= 0) & bad_mask[succ_idxs.clip(0)]
            valid &= (succ_idxs >= 0)

            if not np.any(valid):
                continue

            # TP check: e2, i21, ew must match
            src_idx = idxs[valid]
            dst_idx = succ_idxs[valid]

            tp_match = ((e2[src_idx] == e2[dst_idx]) &
                        (i21[src_idx] == i21[dst_idx]) &
                        (ew[src_idx] == ew[dst_idx]))

            if not np.any(tp_match):
                continue

            # Update phi: phi[src] = max(phi[src], phi[dst])
            src_final = src_idx[tp_match]
            dst_final = dst_idx[tp_match]

            new_phi = np.maximum(phi[src_final], phi[dst_final])
            updates = new_phi > phi[src_final]
            if np.any(updates):
                phi[src_final[updates]] = new_phi[updates]
                changed = True

        if not changed:
            print(f"converged in {iteration + 1} iterations ({time.time()-t0:.1f}s)")
            break

    # Verify formula: PhiFull = fc + 1{c[0]=1, c[1]=2, c[n-1]=1}
    delta = ((configs[:, 0] == 1) & (configs[:, 1] == 2) & (configs[:, n-1] == 1)).astype(np.int32)
    predicted = np.where(good_mask, 0, fc_vals + delta)

    # Only check bad configs
    bad_idx = np.where(bad_mask)[0]
    errors = np.sum(phi[bad_idx] != predicted[bad_idx])

    print(f"\n  n={n}: {n_bad} bad configs, {errors} errors")
    if errors == 0:
        print(f"  PASS: PhiFull = fc + 1{{c[0]=1, c[1]=2, c[n-1]=1}} confirmed at n={n}")
    else:
        print(f"  FAIL!")
        # Show first few errors
        err_idx = bad_idx[phi[bad_idx] != predicted[bad_idx]][:5]
        for i in err_idx:
            print(f"    c={tuple(configs[i])}, fc={fc_vals[i]}, phi={phi[i]}, predicted={predicted[i]}")

    print(f"\n  Total time: {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
