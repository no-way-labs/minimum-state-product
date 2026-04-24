#!/usr/bin/env python3
"""
DERISK #3 (dual-path dispatch):
For every zero-winding cycle at each layout, find WHERE the EC is:
- At a sandwiched ternary (both neighbors binary)? → mechanisms apply
- At a ternary with ONE binary neighbor? → mechanisms DON'T apply as-is
- At a binary proc? → BoundaryShadowEntry path
- At a ternary with NO binary neighbor? → nothing applies

Also: for each EC, check if it's findable via the gap-mechanism approach:
- Find a gap between two firings of the EC proc
- Check if neighbor fire counts in that gap match a mechanism
"""
from itertools import product as iproduct
from collections import Counter

def check_dispatch(n, ms, label, max_len):
    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                if len(results) >= 500: return
            return
        if len(results) >= 500: return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if len(results) >= 500: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= 500: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

    def winding(word):
        w = 0
        for i in range(len(word)):
            d = (word[(i+1)%len(word)] - word[i]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    zw = [w for w in results if winding(w) == 0]
    print(f"\n{label}: n={n}, ms={ms}, {len(zw)} zero-winding cycles")

    ec_location_types = Counter()
    mechanism_reachable = 0
    mechanism_unreachable = 0
    unreachable_details = []

    for word in zw:
        ell = len(word)
        cfgs = [list(start)]
        for i in range(ell):
            c = list(cfgs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
            cfgs.append(c)

        # Find first proc with EC
        ec_proc = None
        for p in range(n):
            m_ctx, n_ctx = set(), set()
            for s in range(ell):
                ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
                if word[s] == p:
                    if ctx in n_ctx: ec_proc = p; break
                    m_ctx.add(ctx)
                else:
                    if ctx in m_ctx: ec_proc = p; break
                    n_ctx.add(ctx)
            if ec_proc is not None: break

        if ec_proc is None:
            ec_location_types['NO_EC'] += 1
            continue

        p = ec_proc
        L_bin = ms[(p-1)%n] == 2
        R_bin = ms[(p+1)%n] == 2
        P_bin = ms[p] == 2
        P_tern = ms[p] == 3

        if P_tern and L_bin and R_bin:
            loc_type = 'sandwiched_ternary'
        elif P_tern and (L_bin or R_bin):
            loc_type = 'ternary_one_binary'
        elif P_tern:
            loc_type = 'ternary_no_binary'
        elif P_bin:
            loc_type = 'binary'
        else:
            loc_type = 'other'

        ec_location_types[loc_type] += 1

        # Check: can we find this EC via gap-mechanism approach?
        # For mechanism to apply: proc needs both neighbors binary
        can_mechanism = (P_tern and L_bin and R_bin) or (P_bin and L_bin and R_bin)

        # Even if proc itself has right neighbors, check if ANY proc
        # with sandwiched-ternary or binary-both-binary has EC
        any_mechanism_reachable = False
        for p2 in range(n):
            p2_tern = ms[p2] == 3
            p2_bin = ms[p2] == 2
            p2_L_bin = ms[(p2-1)%n] == 2
            p2_R_bin = ms[(p2+1)%n] == 2

            if not ((p2_tern and p2_L_bin and p2_R_bin) or (p2_bin)):
                continue

            # Check EC at p2
            m_ctx2, n_ctx2 = set(), set()
            has_ec_p2 = False
            for s in range(ell):
                ctx = (cfgs[s][(p2-1)%n], cfgs[s][p2], cfgs[s][(p2+1)%n])
                if word[s] == p2:
                    if ctx in n_ctx2: has_ec_p2 = True; break
                    m_ctx2.add(ctx)
                else:
                    if ctx in m_ctx2: has_ec_p2 = True; break
                    n_ctx2.add(ctx)

            if has_ec_p2:
                any_mechanism_reachable = True
                break

        if any_mechanism_reachable:
            mechanism_reachable += 1
        else:
            mechanism_unreachable += 1
            if len(unreachable_details) < 3:
                unreachable_details.append((word, ec_proc, loc_type))

    print(f"  EC location types: {dict(sorted(ec_location_types.items()))}")
    print(f"  Mechanism-reachable (EC at sandwiched ternary or binary): {mechanism_reachable}")
    print(f"  Mechanism-unreachable: {mechanism_unreachable}")

    if unreachable_details:
        print(f"  Unreachable examples:")
        for word, p, lt in unreachable_details:
            print(f"    proc {p} ({lt}), word={word[:8]}...")

    if mechanism_unreachable == 0:
        print(f"  *** ALL EC's reachable by mechanisms or binary path ✅ ***")
    else:
        print(f"  *** {mechanism_unreachable} cycles need extended mechanisms ⚠️ ***")

# Test all layouts
check_dispatch(5, [2,3,2,3,2], "n=5 alternating", 16)
check_dispatch(7, [2,3,2,3,2,3,2], "n=7 alternating", 20)
check_dispatch(7, [2,3,3,2,3,3,3], "n=7 non-alt", 22)
check_dispatch(9, [2,3,3,2,3,3,2,3,3], "n=9 non-alt [2,3,3]^3", 26)
check_dispatch(6, [2,3,2,3,3,3], "n=6 non-alt", 18)
