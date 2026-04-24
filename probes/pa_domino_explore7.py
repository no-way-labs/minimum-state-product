#!/usr/bin/env python3
"""
PA Domino Exploration 7: Understand how EC at t arises despite parity obstruction.

The parity obstruction shows: the PRE-neighbor-fire non-mover observation at t
never matches any mover observation at t.

But EC at t DOES occur computationally. So the matching must come from
POST-neighbor-fire non-mover observations — i.e., steps between the neighbor
firing and the next t firing, where some other proc fires (mover ≠ t)
and the context at t has already been updated by the neighbor fire.

The post-fire context at t equals the next t-fire mover context.
So if there's at least one non-mover step between neighbor-fire and t-fire
with that context, we get EC at t.

In a sweep: left(t) fires adjacent to t in CW, right(t) adjacent in CCW.
So there may or may not be a gap.

Let me verify this by tracing exact EC matches.
"""
from collections import Counter

def trace_ec_at_t(n, ms, word, t_pos):
    """Trace exactly how EC at t arises."""
    i_pos = (t_pos - 1) % n
    rr_pos = (t_pos + 1) % n
    ell = len(word)
    start = tuple(0 for _ in range(n))

    # Build configs
    cfgs = [list(start)]
    for idx in range(ell):
        c = list(cfgs[-1])
        c[word[idx]] = (c[word[idx]] + 1) % ms[word[idx]]
        cfgs.append(c)

    # Find EC at t
    mover_ctxs = {}
    nonmover_ctxs = {}
    ec_pair = None
    for s in range(ell):
        ctx = (cfgs[s][(t_pos-1)%n], cfgs[s][t_pos], cfgs[s][(t_pos+1)%n])
        if word[s] == t_pos:
            if ctx in nonmover_ctxs:
                ec_pair = ('mover_hits_nm', s, nonmover_ctxs[ctx], ctx)
                break
            mover_ctxs.setdefault(ctx, s)
        else:
            if ctx in mover_ctxs:
                ec_pair = ('nm_hits_mover', mover_ctxs[ctx], s, ctx)
                break
            nonmover_ctxs.setdefault(ctx, s)

    if ec_pair is None:
        return None

    # Analyze: which steps form the EC pair?
    typ, s_mover, s_nonmover, ctx = ec_pair

    # What fires at the non-mover step?
    nm_mover_proc = word[s_nonmover]

    # Is this right after a neighbor fire?
    # Look backwards from s_nonmover to find the last i_pos or rr_pos fire
    last_neighbor_fire = None
    for back in range(1, ell):
        prev_s = (s_nonmover - back) % ell
        if word[prev_s] in (i_pos, rr_pos):
            last_neighbor_fire = prev_s
            break
        if word[prev_s] == t_pos:
            break  # Hit a t-fire, so we're in a new phase

    # Is this right before a t fire?
    next_t_fire = None
    for fwd in range(1, ell):
        next_s = (s_nonmover + fwd) % ell
        if word[next_s] == t_pos:
            next_t_fire = next_s
            break
        if word[next_s] in (i_pos, rr_pos):
            break  # Another neighbor fires first

    return {
        'type': typ,
        'mover_step': s_mover,
        'nonmover_step': s_nonmover,
        'ctx': ctx,
        'nm_proc': nm_mover_proc,
        'last_neighbor': last_neighbor_fire,
        'next_t': next_t_fire,
    }

# Test at n=5
n = 5
ms_configs = [
    ([2,2,2,3,3], (0,1,2)),
    ([3,2,2,2,3], (1,2,3)),
]

for ms, (i_pos, t_pos, rr_pos) in ms_configs:
    print(f"\nn={n}, ms={ms}, t={t_pos}")
    start = tuple(0 for _ in range(n))
    results = []

    def dfs(word, fc, config):
        if len(results) >= 2000: return
        if len(word) > 6*n: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                return
        remaining = 6*n - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        for nxt in range(n):
            if abs(nxt - word[-1]) % n not in [1, n-1]: continue
            if len(results) >= 2000: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= 2000: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if j==p else 0 for j in range(n)], tuple(first))

    def winding(w):
        wd = 0
        for idx in range(len(w)):
            d = (w[(idx+1)%len(w)] - w[idx]) % n
            if d == 1: wd += 1
            elif d == n-1: wd -= 1
        return wd

    zw = [w for w in results if winding(w) == 0]

    ec_t_count = 0
    post_fire_count = 0
    shown = 0

    for word in zw[:500]:
        ell = len(word)
        fc = Counter(word)
        if fc[t_pos] < 2: continue

        # Check isolated
        t_steps = [s for s in range(ell) if word[s] == t_pos]
        isolated = all(word[(s+1)%ell] != t_pos and word[(s-1)%ell] != t_pos for s in t_steps)
        if not isolated: continue

        result = trace_ec_at_t(n, ms, word, t_pos)
        if result is None: continue

        ec_t_count += 1
        if result['last_neighbor'] is not None:
            post_fire_count += 1

        if shown < 5:
            print(f"  EC at t: mover step {result['mover_step']}, nm step {result['nonmover_step']}")
            print(f"    ctx={result['ctx']}, nm_proc={result['nm_proc']}, last_neighbor={result['last_neighbor']}")

            # Show the mover word around the non-mover step
            s = result['nonmover_step']
            window = [word[(s+d)%ell] for d in range(-3, 4)]
            print(f"    word around nm step: ...{window}... (step {s})")
            shown += 1

    print(f"  EC at t: {ec_t_count} cycles, post-fire: {post_fire_count}")

print("\n" + "="*70)
print("KEY QUESTION: Is EC at the boundary binary (i or rr) UNIVERSAL?")
print("="*70)

# Check if EC at i (boundary binary with ternary left neighbor) is universal
n = 5
ms = [3, 2, 2, 2, 3]
bt = (1, 2, 3)
i_pos, t_pos, rr_pos = bt

print(f"\nn={n}, ms={ms}, checking EC at i={i_pos} (m={ms[i_pos]}, left={ms[(i_pos-1)%n]})")
start = tuple(0 for _ in range(n))
results = []
def dfs(word, fc, config):
    if len(results) >= 3000: return
    if len(word) > 6*n: return
    if len(word) >= n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            return
    remaining = 6*n - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    for nxt in range(n):
        if abs(nxt - word[-1]) % n not in [1, n-1]: continue
        if len(results) >= 3000: return
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    if len(results) >= 3000: break
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if j==p else 0 for j in range(n)], tuple(first))

def winding(w):
    wd = 0
    for idx in range(len(w)):
        d = (w[(idx+1)%len(w)] - w[idx]) % n
        if d == 1: wd += 1
        elif d == n-1: wd -= 1
    return wd

zw = [w for w in results if winding(w) == 0]

# For ALL ZW cycles (not just sorry branch): is EC at i universal?
ec_i_count = 0
no_ec_i_count = 0
for word in zw:
    ell = len(word)
    cfgs = [list(start)]
    for idx in range(ell):
        c = list(cfgs[-1])
        c[word[idx]] = (c[word[idx]] + 1) % ms[word[idx]]
        cfgs.append(c)

    m_ctx = set()
    n_ctx = set()
    found = False
    for s in range(ell):
        ctx = (cfgs[s][(i_pos-1)%n], cfgs[s][i_pos], cfgs[s][(i_pos+1)%n])
        if word[s] == i_pos:
            if ctx in n_ctx: found = True; break
            m_ctx.add(ctx)
        else:
            if ctx in m_ctx: found = True; break
            n_ctx.add(ctx)

    if found:
        ec_i_count += 1
    else:
        no_ec_i_count += 1

print(f"  ZW cycles: {len(zw)}, EC at i: {ec_i_count}, no EC at i: {no_ec_i_count}")

# Check: left(i) (ternary) — EC universal there?
li_pos = (i_pos - 1) % n
ec_li_count = 0
no_ec_li_count = 0
for word in zw:
    ell = len(word)
    cfgs = [list(start)]
    for idx in range(ell):
        c = list(cfgs[-1])
        c[word[idx]] = (c[word[idx]] + 1) % ms[word[idx]]
        cfgs.append(c)

    m_ctx = set()
    n_ctx = set()
    found = False
    for s in range(ell):
        ctx = (cfgs[s][(li_pos-1)%n], cfgs[s][li_pos], cfgs[s][(li_pos+1)%n])
        if word[s] == li_pos:
            if ctx in n_ctx: found = True; break
            m_ctx.add(ctx)
        else:
            if ctx in m_ctx: found = True; break
            n_ctx.add(ctx)

    if found:
        ec_li_count += 1
    else:
        no_ec_li_count += 1

print(f"  EC at left(i)={li_pos}: {ec_li_count}, no EC at left(i): {no_ec_li_count}")
