#!/usr/bin/env python3
"""Passive/no-copy obstruction check at n=10, 11, 12 under exact CUP-2 semantics.

For each n, we enumerate ALL bad-step transitions c->d that are:
  (1) bad: fc(c) > 0 and fc(d) > 0
  (2) TP-preserving: tp(d) == tp(c)
  (3) no-drop: PhiFull(d) == PhiFull(c)
  (4) boundary-changing: boundary6(d) != boundary6(c)
  (5) no-deep-copy-pair: for all k in {4,...,n-4}, d[k]!=d[k-1] AND d[k]!=d[k+1]

Then we check whether the boundary 6-tuple pair (beta_src, beta_dst) is in G617.

Key question: is the passive/no-copy + non-617 case empty at n=11, 12?
"""

import sys
import os
import time
from collections import defaultdict, Counter

sys.path.insert(0, os.path.dirname(__file__))

# ================================================================
# CUP-2 tables (from Tables.lean)
# ================================================================
T_bot = {
    (0,0,0):1,(0,0,1):1,(0,0,2):0,
    (0,1,0):1,(0,1,1):1,(0,1,2):1,
    (1,0,0):0,(1,0,1):1,(1,0,2):0,
    (1,1,0):0,(1,1,1):1,(1,1,2):0,
}
T_low = {
    (0,0,0):0,(0,0,1):0,(0,0,2):0,
    (0,1,0):0,(0,1,1):1,(0,1,2):0,
    (0,2,0):0,(0,2,1):2,(0,2,2):0,
    (1,0,0):1,(1,0,1):1,(1,0,2):1,
    (1,1,0):1,(1,1,1):1,(1,1,2):2,
    (1,2,0):0,(1,2,1):1,(1,2,2):2,
}
T_mid = {
    (0,0,0):0,(0,0,1):0,(0,0,2):0,
    (0,1,0):0,(0,1,1):1,(0,1,2):0,
    (0,2,0):0,(0,2,1):2,(0,2,2):0,
    (1,0,0):1,(1,0,1):1,(1,0,2):1,
    (1,1,0):1,(1,1,1):1,(1,1,2):2,
    (1,2,0):0,(1,2,1):1,(1,2,2):2,
    (2,0,0):0,(2,0,1):0,(2,0,2):2,
    (2,1,0):1,(2,1,1):0,(2,1,2):2,
    (2,2,0):0,(2,2,1):2,(2,2,2):2,
}
T_high = {
    (0,0,0):0,(0,0,1):0,
    (0,1,0):0,(0,1,1):0,
    (0,2,0):0,(0,2,1):0,
    (1,0,0):1,(1,0,1):1,
    (1,1,0):1,(1,1,1):2,
    (1,2,0):0,(1,2,1):2,
    (2,0,0):0,(2,0,1):2,
    (2,1,0):0,(2,1,1):2,
    (2,2,0):2,(2,2,1):2,
}
T_top = {
    (0,0,0):0,(0,0,1):0,
    (0,1,0):0,(0,1,1):0,
    (1,0,0):0,(1,0,1):1,
    (1,1,0):1,(1,1,1):1,
    (2,0,0):1,(2,0,1):1,
    (2,1,0):1,(2,1,1):1,
}

# G617 edge set (boundary 6-tuple encoding pairs)
edge_617_list = [(0,6),(0,162),(1,0),(1,7),(2,164),(3,1),(3,9),(4,166),(6,8),(6,168),(7,6),(7,9),(8,170),(9,11),(10,16),(10,172),(11,17),(12,174),(13,12),(14,176),(16,4),(16,178),(17,5),(18,24),(18,180),(19,18),(19,25),(20,182),(21,19),(21,27),(22,184),(24,26),(24,186),(25,24),(25,27),(26,188),(27,29),(28,34),(28,190),(29,35),(30,192),(31,30),(32,194),(34,22),(34,196),(35,23),(36,0),(36,42),(36,198),(37,1),(37,36),(37,43),(38,2),(38,200),(39,3),(39,37),(39,45),(40,4),(40,202),(41,5),(42,6),(42,44),(42,204),(43,7),(43,42),(43,45),(44,8),(44,206),(45,9),(45,47),(46,10),(46,52),(46,208),(47,11),(47,53),(48,12),(48,210),(49,13),(49,48),(50,14),(50,212),(51,15),(52,16),(52,40),(52,214),(53,17),(53,41),(54,0),(54,60),(54,72),(54,216),(55,61),(55,73),(56,2),(56,74),(56,218),(57,55),(57,63),(57,75),(58,59),(58,76),(59,77),(60,6),(60,62),(60,78),(60,222),(61,63),(61,79),(62,8),(62,80),(62,224),(63,65),(63,81),(64,65),(64,70),(64,82),(65,71),(65,83),(66,12),(66,84),(66,228),(67,85),(68,14),(68,86),(68,230),(69,87),(70,58),(70,71),(70,88),(71,59),(71,89),(72,78),(72,90),(72,234),(73,79),(73,91),(74,92),(74,236),(75,73),(75,81),(75,93),(76,77),(76,94),(77,95),(78,80),(78,96),(78,240),(79,81),(79,97),(80,98),(80,242),(81,83),(81,99),(82,83),(82,88),(82,100),(83,89),(83,101),(84,102),(84,246),(85,103),(86,104),(86,248),(87,105),(88,76),(88,89),(88,106),(89,77),(89,107),(90,36),(90,96),(90,252),(91,97),(92,38),(93,91),(93,99),(94,40),(94,95),(96,42),(96,98),(96,258),(97,99),(98,44),(98,260),(99,101),(100,46),(100,101),(100,106),(101,107),(102,48),(104,50),(106,52),(106,94),(106,107),(107,95),(108,0),(108,114),(108,144),(109,115),(110,2),(110,146),(111,109),(111,117),(112,113),(114,6),(114,116),(114,150),(115,117),(116,8),(116,152),(117,119),(118,119),(118,124),(119,125),(120,12),(120,156),(122,14),(122,158),(124,112),(124,125),(125,113),(126,108),(126,132),(126,144),(127,109),(127,133),(128,110),(128,146),(129,111),(129,127),(129,135),(130,112),(130,131),(131,113),(132,114),(132,134),(132,150),(133,115),(133,135),(134,116),(134,152),(135,117),(135,137),(136,118),(136,137),(136,142),(137,119),(137,143),(138,120),(138,156),(139,121),(140,122),(140,158),(141,123),(142,124),(142,130),(142,143),(142,160),(143,125),(143,131),(144,36),(144,150),(145,37),(145,144),(145,151),(146,38),(147,39),(147,145),(147,153),(148,40),(149,41),(150,42),(150,152),(151,43),(151,150),(151,153),(152,44),(153,45),(153,155),(154,46),(154,160),(155,47),(155,161),(156,48),(157,49),(157,156),(158,50),(159,51),(160,52),(160,148),(161,53),(161,149),(162,168),(162,216),(163,1),(163,162),(163,169),(163,217),(164,218),(165,3),(165,163),(165,171),(165,219),(166,220),(167,5),(167,221),(168,170),(168,222),(169,7),(169,168),(169,171),(169,223),(170,171),(170,224),(171,9),(171,173),(171,225),(172,178),(172,226),(173,11),(173,179),(173,227),(174,228),(175,13),(175,174),(175,229),(176,230),(177,15),(177,231),(178,166),(178,232),(179,17),(179,167),(179,233),(180,186),(181,19),(181,180),(181,187),(183,21),(183,181),(183,189),(185,23),(186,188),(187,25),(187,186),(187,189),(188,189),(189,27),(189,191),(190,196),(191,29),(191,197),(193,31),(193,192),(195,33),(196,184),(197,35),(197,185),(198,162),(198,204),(198,252),(199,37),(199,163),(199,198),(199,205),(199,253),(200,164),(201,39),(201,165),(201,199),(201,207),(201,255),(202,166),(203,41),(203,167),(203,257),(204,168),(204,206),(204,258),(205,43),(205,169),(205,204),(205,207),(205,259),(206,170),(206,207),(206,260),(207,45),(207,171),(207,209),(207,261),(208,172),(208,214),(209,47),(209,173),(209,215),(209,263),(210,174),(211,49),(211,175),(211,210),(211,265),(212,176),(213,51),(213,177),(213,267),(214,178),(214,202),(215,53),(215,179),(215,203),(215,269),(216,222),(216,234),(217,216),(217,223),(217,235),(218,236),(219,217),(219,225),(219,237),(220,238),(221,239),(222,224),(222,240),(223,222),(223,225),(223,241),(224,225),(224,242),(225,227),(225,243),(226,232),(226,244),(227,233),(227,245),(228,246),(229,228),(229,247),(230,248),(231,249),(232,220),(232,250),(233,221),(233,251),(234,240),(234,252),(235,234),(235,241),(235,253),(236,254),(237,235),(237,243),(237,255),(238,239),(238,256),(239,257),(240,242),(240,258),(241,240),(241,243),(241,259),(242,243),(242,260),(243,245),(243,261),(244,240),(244,245),(244,250),(244,262),(245,251),(245,263),(246,264),(247,246),(247,265),(248,266),(249,267),(250,238),(250,251),(250,268),(251,239),(251,269),(252,258),(252,306),(253,252),(253,259),(253,307),(254,308),(255,253),(255,261),(255,309),(256,257),(256,310),(257,311),(258,260),(258,312),(259,258),(259,261),(259,313),(260,261),(260,314),(261,263),(261,315),(262,258),(262,263),(262,268),(262,316),(263,269),(263,317),(264,318),(265,319),(266,320),(267,321),(268,256),(268,269),(268,322),(269,257),(269,323),(270,276),(271,109),(271,270),(271,277),(273,111),(273,271),(273,279),(274,275),(275,113),(276,278),(277,115),(277,276),(277,279),(278,279),(279,117),(279,281),(280,276),(280,281),(280,286),(281,119),(281,287),(283,121),(285,123),(286,274),(286,287),(287,125),(287,275),(288,270),(288,294),(289,127),(289,271),(289,288),(289,295),(290,272),(291,129),(291,273),(291,289),(291,297),(292,274),(292,293),(293,131),(293,275),(294,276),(294,296),(295,133),(295,277),(295,294),(295,297),(296,278),(296,297),(297,135),(297,279),(297,299),(298,280),(298,294),(298,299),(298,304),(299,137),(299,281),(299,305),(300,282),(301,139),(301,283),(302,284),(303,141),(303,285),(304,286),(304,292),(304,305),(305,143),(305,287),(305,293),(306,312),(307,145),(307,306),(307,313),(309,147),(309,307),(309,315),(310,311),(311,149),(312,314),(313,151),(313,312),(313,315),(314,315),(315,153),(315,317),(316,312),(316,317),(316,322),(317,155),(317,323),(319,157),(321,159),(322,310),(322,323),(323,161),(323,311)]
G617 = set(edge_617_list)


def build_tables(n):
    """Build transition function list for CUP-2 system of size n."""
    assert n >= 5
    tables = [T_bot, T_low]
    for _ in range(2, n - 2):
        tables.append(T_mid)
    tables.append(T_high)
    tables.append(T_top)
    ms = [2] + [3] * (n - 2) + [2]
    return ms, tables


def analyze_n(n):
    """Full analysis for a given n."""
    t0 = time.time()
    ms, tables = build_tables(n)
    N = 1
    for m in ms:
        N *= m
    print(f"\n{'='*60}")
    print(f"n = {n}, state space = {N}, strip length = {n-8}, parity = {(n-8)%2}")
    print(f"{'='*60}")

    # Config encoding/decoding using mixed radix
    def idx_to_config(idx):
        c = []
        for m in reversed(ms):
            c.append(idx % m)
            idx //= m
        return tuple(reversed(c))

    def config_to_idx(c):
        idx = 0
        for j in range(n):
            idx = idx * ms[j] + c[j]
        return idx

    def move(c, pos):
        L = c[(pos - 1) % n]
        S = c[pos]
        R = c[(pos + 1) % n]
        v = tables[pos][(L, S, R)]
        if v == S:
            return c  # not privileged
        return tuple(c[j] if j != pos else v for j in range(n))

    def fc(c):
        return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

    def tp(c):
        """TP triple: (exp2_count, int_21, exp2_weight)."""
        e = sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] in (0, 1))
        i21 = sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
        w = sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] in (0, 1))
        return (e, i21, w)

    def boundary6(c):
        return ((((c[0] * 3 + c[1]) * 3 + c[2]) * 3 + c[n - 3]) * 3 + c[n - 2]) * 2 + c[n - 1]

    def has_deep_copy_pair(c):
        """Check if d has a deep copy pair: exists k in {4,...,n-4} with d[k]==d[k-1] or d[k]==d[k+1]."""
        for k in range(4, n - 3):  # positions 4 to n-4 inclusive
            if c[k] == c[k - 1] or c[k] == c[k + 1]:
                return True
        return False

    # Step 1: enumerate all bad configs, compute fc and tp
    print(f"Step 1: Enumerating bad configs...", end=" ", flush=True)
    bad_fc = {}    # idx -> fc value
    bad_tp = {}    # idx -> tp triple
    bad_cfg = {}   # idx -> config tuple
    bad_b6 = {}    # idx -> boundary6 encoding

    for i in range(N):
        c = idx_to_config(i)
        f = fc(c)
        if f > 0:
            bad_fc[i] = f
            bad_tp[i] = tp(c)
            bad_cfg[i] = c
            bad_b6[i] = boundary6(c)

    num_bad = len(bad_fc)
    print(f"{num_bad} bad configs ({time.time()-t0:.1f}s)")

    # Step 2: build TP-preserving adjacency and compute PhiFull
    print(f"Step 2: Building adjacency + computing PhiFull...", end=" ", flush=True)
    t1 = time.time()

    # Forward adjacency (all bad steps)
    all_adj = defaultdict(list)   # i -> [(j, pos)]
    tp_adj = defaultdict(list)    # i -> [j] (TP-preserving only)

    for i in bad_fc:
        c = bad_cfg[i]
        for p in range(n):
            c2 = move(c, p)
            if c2 is c:  # identity check (not privileged)
                continue
            j = config_to_idx(c2)
            if j in bad_fc:
                all_adj[i].append((j, p))
                if bad_tp[j] == bad_tp[i]:
                    tp_adj[i].append(j)

    # PhiFull: max fc reachable via TP-preserving bad steps (fixed-point iteration)
    phi_full = dict(bad_fc)  # start with own fc
    tp_rev = defaultdict(list)
    for i in bad_fc:
        for j in tp_adj[i]:
            tp_rev[j].append(i)

    changed = True
    iters = 0
    while changed:
        changed = False
        iters += 1
        for j in bad_fc:
            for i in tp_rev[j]:
                if phi_full[j] > phi_full[i]:
                    phi_full[i] = phi_full[j]
                    changed = True

    print(f"done ({iters} iters, {time.time()-t1:.1f}s)")

    # Step 3: find all no-drop boundary-changing TP-preserving bad steps
    # where destination has no deep copy pair
    print(f"Step 3: Finding no-copy no-drop boundary-changing TP-preserving steps...", end=" ", flush=True)
    t2 = time.time()

    witnesses = []  # (i, j, pos, beta_src, beta_dst, d3, dn4, tp_triple)
    non617_witnesses = []

    for i in bad_fc:
        c = bad_cfg[i]
        b6_src = bad_b6[i]
        tp_i = bad_tp[i]
        pf_i = phi_full[i]

        for j, p in all_adj[i]:
            # TP-preserving?
            if bad_tp[j] != tp_i:
                continue
            # no-drop (PhiFull preserved)?
            if phi_full[j] != pf_i:
                continue
            # boundary-changing?
            b6_dst = bad_b6[j]
            if b6_dst == b6_src:
                continue

            # no-deep-copy-pair in destination?
            d = bad_cfg[j]
            if has_deep_copy_pair(d):
                continue

            # This is a no-copy no-drop boundary-changing TP-preserving witness
            beta = (b6_src, b6_dst)
            d3 = d[3]
            dn4 = d[n - 4]
            witnesses.append((i, j, p, b6_src, b6_dst, d3, dn4, tp_i))

            if beta not in G617:
                non617_witnesses.append((i, j, p, b6_src, b6_dst, d3, dn4, tp_i, c, d))

    print(f"done ({time.time()-t2:.1f}s)")
    total_time = time.time() - t0

    # Report
    print(f"\nResults for n={n}:")
    print(f"  Total bad configs: {num_bad}")
    print(f"  Total no-copy no-drop bd-changing TP-preserving witnesses: {len(witnesses)}")
    print(f"  Non-G617 witnesses: {len(non617_witnesses)}")
    print(f"  Total time: {total_time:.1f}s")

    if non617_witnesses:
        print(f"\n  *** NON-617 WITNESSES FOUND ***")
        for w in non617_witnesses[:20]:
            i, j, p, bs, bd, d3, dn4, tp_tr, c, d = w
            print(f"    c={c} -> d={d}, pos={p}, beta=({bs},{bd}), "
                  f"d[3]={d3}, d[n-4]={dn4}, tp={tp_tr}")
    else:
        print(f"  ==> Passive/no-copy + non-617 case is EMPTY at n={n}")

    # Detailed analysis: beta distribution by (endpoints, parity)
    print(f"\n  --- Beta analysis ---")
    beta_set = set()
    by_endpoints = defaultdict(set)
    by_parity = defaultdict(set)
    by_endp_parity = defaultdict(set)
    strip_len = n - 8
    parity = strip_len % 2

    for w in witnesses:
        _, _, _, bs, bd, d3, dn4, _ = w
        beta = (bs, bd)
        beta_set.add(beta)
        by_endpoints[(d3, dn4)].add(beta)
        by_parity[parity].add(beta)  # single parity for this n
        by_endp_parity[(d3, dn4, parity)].add(beta)

    print(f"  Strip length: {strip_len}, parity: {parity}")
    print(f"  Distinct betas: {len(beta_set)}")
    print(f"  All betas in G617: {all(b in G617 for b in beta_set)}")

    # By endpoints
    print(f"\n  Betas by strip-endpoint pair (d[3], d[n-4]):")
    for ep in sorted(by_endpoints.keys()):
        betas = by_endpoints[ep]
        in617 = sum(1 for b in betas if b in G617)
        print(f"    ({ep[0]}, {ep[1]}): {len(betas)} betas, {in617}/{len(betas)} in G617")

    # TP distribution
    tp_counts = Counter()
    for w in witnesses:
        tp_counts[w[7]] += 1
    print(f"\n  TP triple distribution among witnesses:")
    for tp_val, cnt in sorted(tp_counts.items()):
        print(f"    tp={tp_val}: {cnt} witnesses")

    return {
        'n': n,
        'num_bad': num_bad,
        'num_witnesses': len(witnesses),
        'num_non617': len(non617_witnesses),
        'beta_set': beta_set,
        'by_endpoints': dict(by_endpoints),
        'by_parity': dict(by_parity),
        'non617': non617_witnesses,
        'witnesses': witnesses,
    }


def cross_n_analysis(results_list):
    """Compare beta sets across different n values."""
    print(f"\n{'='*60}")
    print(f"Cross-n analysis")
    print(f"{'='*60}")

    # Collect all endpoint->beta maps
    all_endpoints = set()
    for r in results_list:
        all_endpoints.update(r['by_endpoints'].keys())

    print(f"\nEndpoint pairs seen: {sorted(all_endpoints)}")

    # For each endpoint pair, compare beta sets across n
    print(f"\nBeta sets by (endpoint, n):")
    for ep in sorted(all_endpoints):
        print(f"\n  Endpoint ({ep[0]}, {ep[1]}):")
        for r in results_list:
            n = r['n']
            parity = (n - 8) % 2
            betas = r['by_endpoints'].get(ep, set())
            if betas:
                print(f"    n={n} (parity={parity}): {len(betas)} betas: {sorted(betas)[:10]}{'...' if len(betas)>10 else ''}")
            else:
                print(f"    n={n} (parity={parity}): 0 betas")

    # Check: do beta sets depend on parity only?
    print(f"\nParity dependence check:")
    parity_groups = defaultdict(list)
    for r in results_list:
        parity = (r['n'] - 8) % 2
        parity_groups[parity].append(r)

    for parity, rs in sorted(parity_groups.items()):
        if len(rs) >= 2:
            # Compare beta sets for same parity
            beta_sets = [r['beta_set'] for r in rs]
            ns = [r['n'] for r in rs]
            if all(b == beta_sets[0] for b in beta_sets):
                print(f"  Parity {parity}: beta sets IDENTICAL across n={ns}")
            else:
                print(f"  Parity {parity}: beta sets DIFFER across n={ns}")
                for i, r in enumerate(rs):
                    print(f"    n={r['n']}: {len(r['beta_set'])} betas")
        else:
            n = rs[0]['n']
            print(f"  Parity {parity}: only n={n}")

    # Check: do beta sets depend on (endpoints, parity)?
    print(f"\nEndpoint+parity dependence check:")
    endp_parity_groups = defaultdict(list)
    for r in results_list:
        parity = (r['n'] - 8) % 2
        for ep, betas in r['by_endpoints'].items():
            endp_parity_groups[(ep, parity)].append((r['n'], betas))

    all_match = True
    for key, entries in sorted(endp_parity_groups.items()):
        if len(entries) >= 2:
            beta_sets = [e[1] for e in entries]
            ns = [e[0] for e in entries]
            if not all(b == beta_sets[0] for b in beta_sets):
                print(f"  ({key[0]}, parity={key[1]}): DIFFER across n={ns}")
                all_match = False
            else:
                print(f"  ({key[0]}, parity={key[1]}): MATCH across n={ns} ({len(beta_sets[0])} betas)")

    if all_match:
        print(f"\n  ==> Beta sets are determined by (endpoint, parity) combination")


if __name__ == '__main__':
    results = []
    for n in [10, 11, 12]:
        r = analyze_n(n)
        results.append(r)

    cross_n_analysis(results)

    # Final summary
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    for r in results:
        status = "EMPTY" if r['num_non617'] == 0 else f"*** {r['num_non617']} NON-617 ***"
        print(f"  n={r['n']}: {r['num_witnesses']} witnesses, non-617: {status}")

    all_empty = all(r['num_non617'] == 0 for r in results)
    print(f"\n  Passive/no-copy + non-617 empty at ALL n in {{10,11,12}}: {all_empty}")
