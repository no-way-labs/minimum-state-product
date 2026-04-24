#!/usr/bin/env python3
"""
PA Domino Final 2: Verify the counterexample satisfies all sorry hypotheses.
"""
from collections import Counter

n = 9
ms = [3,2,2,2,2,2,2,2,2]
word = [0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1]
ell = len(word)

print(f"n={n}, ms={ms}, word length={ell}")
print(f"word={word}")

# Fire counts
fc = Counter(word)
print(f"\nFire counts: {dict(sorted(fc.items()))}")
for p in range(n):
    print(f"  proc {p}: m={ms[p]}, fc={fc[p]}, fc%m={fc[p]%ms[p]}")

# Configs
start = tuple(0 for _ in range(n))
cfgs = [list(start)]
for idx in range(ell):
    c = list(cfgs[-1])
    c[word[idx]] = (c[word[idx]] + 1) % ms[word[idx]]
    cfgs.append(c)

print(f"\nReturns to start? {tuple(cfgs[0]) == tuple(cfgs[ell])}")

# Total displacement
disp = 0
for idx in range(ell):
    curr = word[idx]
    nxt = word[(idx+1) % ell]
    d = (nxt - curr) % n
    if d == 1:
        disp += 1
    elif d == n - 1:
        disp -= 1
    else:
        # Non-adjacent moves (shouldn't happen in a ring walk)
        print(f"  WARNING: non-adjacent move at step {idx}: {curr} -> {nxt}")

print(f"\nTotal displacement (winding number): {disp}")
print(f"|displacement| = {abs(disp)} >= 2*{n} = {2*n}? {abs(disp) >= 2*n}")
print(f"Is sweep? {abs(disp) >= 2*n}")

# Check hno_safe: ¬∃ q, ∀ k, moverAt k ≠ q ∧ moverAt k ≠ left q ∧ moverAt k ≠ right q
# This means: for every q, there exists k such that moverAt k = q or left(q) or right(q)
def left(p): return (p - 1) % n
def right(p): return (p + 1) % n

safe_procs = []
for q in range(n):
    is_safe = True
    for k in range(ell):
        m = word[k]
        if m == q or m == left(q) or m == right(q):
            is_safe = False
            break
    if is_safe:
        safe_procs.append(q)

print(f"\nSafe procs (no mover is q or neighbor of q): {safe_procs}")
print(f"hno_safe satisfied (no safe proc)? {len(safe_procs) == 0}")

# Check 3 consecutive binary
print(f"\n3 consecutive binary positions:")
for start_p in range(n):
    if all(ms[(start_p + j) % n] == 2 for j in range(3)):
        triple = [(start_p + j) % n for j in range(3)]
        print(f"  {triple}")

# Check isolated firings at t = right(i)
# For each consecutive binary triple, check t = right(i)
for start_p in range(n):
    if all(ms[(start_p + j) % n] == 2 for j in range(3)):
        i_pos = start_p
        t_pos = (start_p + 1) % n
        rr_pos = (start_p + 2) % n
        t_steps = [s for s in range(ell) if word[s] == t_pos]
        isolated = all(word[(s+1)%ell] != t_pos and word[(s-1)%ell] != t_pos for s in t_steps)
        print(f"\n  i={i_pos}, t={t_pos}, rr={rr_pos}: fc(t)={fc[t_pos]}, isolated={isolated}")

        if isolated and fc[t_pos] >= 2:
            # Min gap
            min_gap = float('inf')
            min_idx = 0
            for idx in range(len(t_steps)):
                a = t_steps[idx]
                b = t_steps[(idx+1) % len(t_steps)]
                if b <= a: b += ell
                gap = b - a
                if gap < min_gap:
                    min_gap = gap
                    min_idx = idx

            a = t_steps[min_idx]
            b = t_steps[(min_idx+1) % len(t_steps)]
            if b <= a: b += ell

            J = sum(1 for s in range(a+1, b) if word[s%ell] == i_pos)
            K = sum(1 for s in range(a+1, b) if word[s%ell] == rr_pos)
            print(f"    Min gap: size={min_gap}, J={J}, K={K}")
            print(f"    Odd parity? J_odd={J%2==1}, K_odd={K%2==1}")

            # Phase dispatch
            dispatched = (J%2==0 and K%2==0) or (J>=2 and K==0) or (J==0 and K>=2)
            print(f"    Dispatched? {dispatched}")

            # All phases
            for idx2 in range(len(t_steps)):
                a2 = t_steps[idx2]
                b2 = t_steps[(idx2+1) % len(t_steps)]
                if b2 <= a2: b2 += ell
                J2 = sum(1 for s in range(a2+1, b2) if word[s%ell] == i_pos)
                K2 = sum(1 for s in range(a2+1, b2) if word[s%ell] == rr_pos)
                d2 = (J2%2==0 and K2%2==0) or (J2>=2 and K2==0) or (J2==0 and K2>=2)
                print(f"    Phase {idx2}: [{a2},{b2}) J={J2} K={K2} dispatched={d2}")

# Check EC
print("\nEntry Conflict check:")
for p in range(n):
    m_ctx = set()
    n_ctx = set()
    has_ec = False
    for s in range(ell):
        ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
        if word[s] == p:
            if ctx in n_ctx: has_ec = True; break
            m_ctx.add(ctx)
        else:
            if ctx in m_ctx: has_ec = True; break
            n_ctx.add(ctx)
    print(f"  proc {p} (m={ms[p]}): EC={has_ec}, |mover|={len(m_ctx)}, |nonmover|={len(n_ctx)}")

print("\n" + "="*70)
print("CONCLUSION")
print("="*70)
print()
print("If this counterexample satisfies ALL hypotheses of consec_isolated_false")
print("AND has no EC, then the sorry CANNOT be closed without additional hypotheses.")
print()
print("The fix would be to thread hsweep OR to use hconv in a way that")
print("distinguishes this counterexample (if its system doesn't converge).")
