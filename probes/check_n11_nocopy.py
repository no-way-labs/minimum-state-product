#!/usr/bin/env python3
"""Check at n=11: all qualifying no-copy TP-preserving PhiFull-preserving
boundary-changing bad steps have isNoCopyEdge = true."""

import numpy as np
import time

n = 11
ms = [2,3,3,3,3,3,3,3,3,3,2]
total = 1
for m in ms:
    total *= m
assert total == 78732

# Weights for config encoding
weight = [0]*n
weight[n-1] = 1
for j in range(n-2, -1, -1):
    weight[j] = weight[j+1] * ms[j+1]
assert weight[0] == 39366
assert weight[0] * ms[0] == total

# Transition tables
TLow = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
THigh = {(0,0,0):1,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):1,
         (1,0,0):1,(1,0,1):1,(1,1,0):0,(1,1,1):2,(1,2,0):1,(1,2,1):1,
         (2,0,0):2,(2,0,1):2,(2,1,0):2,(2,1,1):0,(2,2,0):0,(2,2,1):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
        (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
        (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
        (2,2,0):0,(2,2,1):2,(2,2,2):2}

def outval(p, L, S, R):
    if p == 0:
        return (S+1) % 2
    elif p == 1:
        return TLow[(S, R)]
    elif p == n-2:
        return THigh[(L, S, R)]
    elif p == n-1:
        return (S+1) % 2
    else:
        return TMid[(L, S, R)]

# Decode config index to array
def decode(idx):
    c = [0]*n
    rem = idx
    for j in range(n):
        c[j] = rem // weight[j]
        rem = rem % weight[j]
    return c

def encode(c):
    s = 0
    for j in range(n):
        s += c[j] * weight[j]
    return s

# Precompute all configs as a 2D array: configs[idx] = array of values
print("Precomputing all configs...")
t0 = time.time()
configs = np.zeros((total, n), dtype=np.int8)
for idx in range(total):
    configs[idx] = decode(idx)
print(f"  Done in {time.time()-t0:.1f}s")

# Compute fc for all configs
print("Computing fc...")
t0 = time.time()
fc = np.zeros(total, dtype=np.int32)
for j in range(n):
    jnext = (j+1) % n
    fc += (configs[:, j] != configs[:, jnext]).astype(np.int32)
print(f"  Done in {time.time()-t0:.1f}s")

# Compute TP for all configs: (count2, count2_then_1, sum_of_2positions)
print("Computing TP...")
t0 = time.time()
is2 = (configs == 2)  # shape (total, n)
count2 = is2.sum(axis=1)  # shape (total,)
# count2_then_1: sum over j in 1..n-2 of (c[j]==2 and c[j+1]==1)
count2then1 = np.zeros(total, dtype=np.int32)
for j in range(1, n-1):
    count2then1 += (is2[:, j] & (configs[:, j+1] == 1)).astype(np.int32)
# sum of positions where c[j]==2
sum2pos = np.zeros(total, dtype=np.int32)
for j in range(n):
    sum2pos += (is2[:, j] * j).astype(np.int32)
# Pack TP as a single int64 for fast comparison
tp_packed = count2.astype(np.int64) * 1000000 + count2then1.astype(np.int64) * 1000 + sum2pos.astype(np.int64)
print(f"  Done in {time.time()-t0:.1f}s")

# Build successor graph: for each config and each position, compute successor
# Then compute PhiFull via fixpoint
print("Computing all successors and building PhiFull...")
t0 = time.time()

# phifull starts as fc
phifull = fc.copy()

# Precompute all successors: for each config idx, list of successor indices
# that are TP-preserving
# We'll iterate: phifull[idx] = max(fc[idx], max over TP-preserving successors of phifull[succ])

# First build successor list
# For efficiency, precompute output for each (p, idx) and check TP preservation
print("  Building TP-preserving successor edges...")
t1 = time.time()

# Store edges as (src, dst) pairs
src_list = []
dst_list = []

for p in range(n):
    print(f"    Position {p}...")
    L_col = configs[:, (p-1) % n]
    S_col = configs[:, p]
    R_col = configs[:, (p+1) % n]

    # Compute output for all configs at position p
    out = np.zeros(total, dtype=np.int8)
    if p == 0:
        out = ((S_col + 1) % 2).astype(np.int8)
    elif p == 1:
        for (s, r), v in TLow.items():
            mask = (S_col == s) & (R_col == r)
            out[mask] = v
    elif p == n-2:
        for (l, s, r), v in THigh.items():
            mask = (L_col == l) & (S_col == s) & (R_col == r)
            out[mask] = v
    elif p == n-1:
        out = ((S_col + 1) % 2).astype(np.int8)
    else:
        for (l, s, r), v in TMid.items():
            mask = (L_col == l) & (S_col == s) & (R_col == r)
            out[mask] = v

    # Privileged: out != S
    priv = (out != S_col)
    priv_idx = np.where(priv)[0]

    if len(priv_idx) == 0:
        continue

    # Build successor configs
    succ_configs = configs[priv_idx].copy()
    succ_configs[:, p] = out[priv_idx]

    # Encode successors
    succ_enc = np.zeros(len(priv_idx), dtype=np.int64)
    for j in range(n):
        succ_enc += succ_configs[:, j].astype(np.int64) * weight[j]

    # Check TP preservation
    tp_src = tp_packed[priv_idx]
    tp_dst = tp_packed[succ_enc]
    tp_ok = (tp_src == tp_dst)

    good_src = priv_idx[tp_ok]
    good_dst = succ_enc[tp_ok]

    src_list.append(good_src)
    dst_list.append(good_dst.astype(np.int64))

src_arr = np.concatenate(src_list)
dst_arr = np.concatenate(dst_list)
print(f"  {len(src_arr)} TP-preserving edges")
print(f"  Edge building done in {time.time()-t1:.1f}s")

# PhiFull fixpoint: phifull[src] = max(phifull[src], phifull[dst])
# Iterate until stable
print("  Running PhiFull fixpoint...")
t1 = time.time()
for iteration in range(100):
    old = phifull.copy()
    # For each edge (src, dst), phifull[src] = max(phifull[src], phifull[dst])
    # Use np.maximum.at for scatter
    np.maximum.at(phifull, src_arr, phifull[dst_arr])

    changed = np.sum(phifull != old)
    if changed == 0:
        print(f"  Converged after {iteration+1} iterations")
        break
    if iteration % 5 == 0:
        print(f"    Iteration {iteration}: {changed} changed")
print(f"  PhiFull fixpoint done in {time.time()-t1:.1f}s")

# Boundary encoding: enc(c) = ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]
# = c[0]*3*3*3*2 + c[1]*3*3*2 + c[2]*3*2 + c[n-3]*3*2 + c[n-2]*2 + c[n-1]
# Wait, let me be precise:
# enc = c[0]; enc = enc*3 + c[1]; enc = enc*3 + c[2]; enc = enc*3 + c[n-3]; enc = enc*3 + c[n-2]; enc = enc*2 + c[n-1]
# So enc = c[0]*3^4*2 + c[1]*3^3*2 + c[2]*3^2*2 + c[n-3]*3*2 + c[n-2]*2 + c[n-1]
# = c[0]*162 + c[1]*54 + c[2]*18 + c[8]*6 + c[9]*2 + c[10]
print("Computing boundary encodings...")
benc = (configs[:,0].astype(np.int32) * 162 +
        configs[:,1].astype(np.int32) * 54 +
        configs[:,2].astype(np.int32) * 18 +
        configs[:,n-3].astype(np.int32) * 6 +
        configs[:,n-2].astype(np.int32) * 2 +
        configs[:,n-1].astype(np.int32))
# Max boundary encoding: 1*162 + 2*54 + 2*18 + 2*6 + 2*2 + 1 = 162+108+36+12+4+1 = 323
# So 324 values (0..323)
print(f"  Max boundary encoding: {benc.max()}")

# noCopyEdgeCodes set
noCopyEdgeCodes = set([973,1952,2277,2927,3256,3581,6823,7802,8127,8777,9106,9431,11664,11989,12314,12639,12673,12964,13289,13614,13652,13939,13977,14264,14589,14627,14914,14956,15239,15281,15564,15889,16214,16539,16864,17189,17568,17893,18218,18523,18543,18851,18868,19193,19502,19518,19827,19843,20168,20477,20493,20801,20806,20818,21131,21143,21468,21793,22118,22443,22751,22768,23093,23418,23743,24068,24373,24393,24701,24718,25043,25352,25368,25677,25693,26018,26327,26343,26651,26656,26668,26981,26993,27318,27643,27968,28293,28601,28618,28943,30223,30551,31202,31527,32177,32501,32506,32831,34451,36073,36401,37052,37377,38027,38351,38356,38681,40301,40932,41257,41582,41907,41923,42232,42251,42557,42882,42902,43207,43227,43532,43857,43877,44182,44201,44206,44507,44531,44832,45157,45482,45807,46132,46151,46457,46692,47017,47342,47667,47773,47992,48317,48642,48752,48967,49077,49292,49617,49727,49942,50056,50267,50381,50592,50917,51242,51567,51892,52217,52974,53623,54602,54924,54927,55251,55577,55906,56231,56874,58824,59473,60452,60774,60777,61101,61427,61756,62081,62724,64314,64639,64674,64964,65289,65323,65614,65939,66264,66302,66589,66624,66627,66914,66951,67239,67277,67564,67606,67889,67931,68214,68539,68574,68864,69189,69514,69839,70218,70524,70543,70868,71173,71193,71518,71843,72152,72168,72474,72477,72493,72801,72818,73127,73143,73456,73468,73781,73793,74118,74424,74443,74768,75093,75418,75743,76068,76374,76393,76718,77023,77043,77368,77693,78002,78018,78324,78327,78343,78651,78668,78977,78993,79306,79318,79631,79643,79968,80274,80293,80618,80943,81268,81593,81954,82224,82279,82604,82873,82929,83254,83579,83852,83904,84174,84177,84229,84501,84554,84827,84879,85156,85204,85481,85529,85854,86179,86504,86829,87154,87479,88074,88723,89702,90024,90027,90351,90677,91006,91331,93582,93907,93924,94232,94557,94573,94882,95207,95532,95552,95857,95874,95877,96182,96201,96507,96527,96832,96856,97157,97181,97482,97807,98132,98457,98782,99107,99774,100423,101402,101724,101727,102051,102377,102706,103031])

print(f"\nnoCopyEdgeCodes has {len(noCopyEdgeCodes)} entries")

# Now scan all edges: for each (src, dst) that is TP-preserving,
# check the qualifying conditions
print("\nScanning ALL qualifying edges...")
t0 = time.time()

qualifying = 0
failing = 0
failing_examples = []
qual_by_pos = {}
fail_by_pos = {}

for p in range(n):
    L_col = configs[:, (p-1) % n]
    S_col = configs[:, p]
    R_col = configs[:, (p+1) % n]

    # Compute output
    out = np.zeros(total, dtype=np.int8)
    if p == 0:
        out = ((S_col + 1) % 2).astype(np.int8)
    elif p == 1:
        for (s, r), v in TLow.items():
            mask = (S_col == s) & (R_col == r)
            out[mask] = v
    elif p == n-2:
        for (l, s, r), v in THigh.items():
            mask = (L_col == l) & (S_col == s) & (R_col == r)
            out[mask] = v
    elif p == n-1:
        out = ((S_col + 1) % 2).astype(np.int8)
    else:
        for (l, s, r), v in TMid.items():
            mask = (L_col == l) & (S_col == s) & (R_col == r)
            out[mask] = v

    # Privileged
    priv = (out != S_col)
    priv_idx = np.where(priv)[0]
    if len(priv_idx) == 0:
        continue

    # Build successor configs
    succ_configs = configs[priv_idx].copy()
    succ_configs[:, p] = out[priv_idx]

    # Encode successors
    succ_enc = np.zeros(len(priv_idx), dtype=np.int64)
    for j in range(n):
        succ_enc += succ_configs[:, j].astype(np.int64) * weight[j]

    # Filter 1: no deep copy pair on d
    # For k in range(4, n-4+1) i.e. k=4..7, check d[k]==d[k-1] or d[k]==d[k+1]
    has_deep_copy = np.zeros(len(priv_idx), dtype=bool)
    for k in range(4, n-4+1):  # k=4,5,6,7
        has_deep_copy |= (succ_configs[:, k] == succ_configs[:, k-1])
        has_deep_copy |= (succ_configs[:, k] == succ_configs[:, k+1])
    no_deep_copy = ~has_deep_copy

    # Filter 2: boundary changed
    benc_src = benc[priv_idx]
    benc_dst_vals = (succ_configs[:,0].astype(np.int32) * 162 +
                     succ_configs[:,1].astype(np.int32) * 54 +
                     succ_configs[:,2].astype(np.int32) * 18 +
                     succ_configs[:,n-3].astype(np.int32) * 6 +
                     succ_configs[:,n-2].astype(np.int32) * 2 +
                     succ_configs[:,n-1].astype(np.int32))
    bnd_changed = (benc_src != benc_dst_vals)

    # Filter 3: TP preserved
    tp_src = tp_packed[priv_idx]
    tp_dst = tp_packed[succ_enc]
    tp_ok = (tp_src == tp_dst)

    # Filter 4: PhiFull preserved
    pf_src = phifull[priv_idx]
    pf_dst = phifull[succ_enc]
    pf_ok = (pf_src == pf_dst)

    # All qualifying
    qual = no_deep_copy & bnd_changed & tp_ok & pf_ok
    qual_idx = np.where(qual)[0]

    if len(qual_idx) == 0:
        continue

    # Check isNoCopyEdge
    edge_codes = benc_src[qual_idx].astype(np.int64) * 324 + benc_dst_vals[qual_idx].astype(np.int64)

    pos_qual = 0
    pos_fail = 0
    seen_codes = set()
    fail_codes = set()
    for i, ec in enumerate(edge_codes):
        qualifying += 1
        pos_qual += 1
        ec_int = int(ec)
        seen_codes.add(ec_int)
        if ec_int not in noCopyEdgeCodes:
            failing += 1
            pos_fail += 1
            fail_codes.add(ec_int)
            orig_i = priv_idx[qual_idx[i]]
            if failing <= 10:
                failing_examples.append((p, list(configs[orig_i]), list(succ_configs[qual_idx[i]]), ec_int))
    qual_by_pos[p] = pos_qual
    fail_by_pos[p] = pos_fail
    if pos_qual > 0:
        print(f"  pos {p}: {len(seen_codes)} unique edge codes, {len(fail_codes)} unique failing codes")
        print(f"    sample seen: {sorted(seen_codes)[:5]}")
        if fail_codes:
            print(f"    sample fail: {sorted(fail_codes)[:5]}")

print(f"\nDone in {time.time()-t0:.1f}s")
print(f"\n{'='*60}")
print(f"RESULTS at n={n}:")
print(f"  Total configs: {total}")
print(f"  Qualifying steps (no-copy, TP-pres, PhiFull-pres, bnd-changed): {qualifying}")
print(f"  Failing isNoCopyEdge check: {failing}")
print(f"\n  Per-position breakdown:")
for p in sorted(qual_by_pos.keys()):
    print(f"    pos {p}: qualifying={qual_by_pos[p]}, failing={fail_by_pos[p]}")
if failing == 0:
    print(f"  >>> ALL qualifying steps have isNoCopyEdge = true <<<")
    print(f"  >>> n-independence CONFIRMED at n={n} <<<")
else:
    print(f"  >>> FAILURE: {failing} steps not in noCopyEdgeCodes <<<")
    for ex in failing_examples[:5]:
        p, src, dst, ec = ex
        print(f"    pos={p}, src={src}, dst={dst}, edgeCode={ec}")
