"""Debug the one failure case."""

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 5
moduli = [2, 2, 2, 3, 3]
word = [3, 3, 4, 0, 4, 3, 2, 1, 0, 4, 3, 3, 2, 3, 4, 0, 1, 2]
CL = len(word)

fc = [0] * n
for m in word:
    fc[m] += 1
print(f"fc = {fc}")
print(f"CL = {CL}")
print(f"moduli = {moduli}")

# Check ZW
cw = sum(1 for k in range(CL) if word[(k+1) % CL] == right(word[k], n))
ccw = sum(1 for k in range(CL) if word[(k+1) % CL] == left(word[k], n))
stay = CL - cw - ccw
print(f"cw={cw}, ccw={ccw}, stay={stay}")

# Print mover word with annotations
print("\nStep-by-step:")
for k in range(CL):
    m = word[k]
    m_next = word[(k+1) % CL]
    if m_next == right(m, n):
        d = "CW"
    elif m_next == left(m, n):
        d = "CCW"
    else:
        d = "STAY"
    print(f"  k={k:2d}: mover={m} -> {d}")

# For each proc, show fire steps and intervals
print("\nProc-by-proc analysis:")
for i in range(n):
    fire_steps = [k for k in range(CL) if word[k] == i]
    print(f"\nProc {i} (mod={moduli[i]}): fires at {fire_steps}, fc={fc[i]}")
    print(f"  L={left(i,n)} (mod={moduli[left(i,n)]}), R={right(i,n)} (mod={moduli[right(i,n)]})")

    if len(fire_steps) < 2:
        continue

    li = left(i, n)
    ri = right(i, n)

    for idx in range(len(fire_steps)):
        a1 = fire_steps[idx]
        a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
        if a2_raw <= a1: a2_raw += CL

        print(f"  Interval ({a1}, {a2_raw % CL}): gap={a2_raw - a1 - 1}")

        # Show movers in gap
        gap_movers = [(k % CL, word[k % CL]) for k in range(a1 + 1, a2_raw)]
        print(f"    Movers: {[(k, m) for k, m in gap_movers]}")

        # For each suffix, check
        b_fires_L = 0
        b_fires_R = 0
        for k_raw in range(a2_raw - 1, a1, -1):
            k = k_raw % CL
            m = word[k]
            if m == li: b_fires_L += 1
            if m == ri: b_fires_R += 1

            li_ok = (b_fires_L == 0) or (moduli[li] == 2 and b_fires_L % 2 == 0)
            ri_ok = (b_fires_R == 0) or (moduli[ri] == 2 and b_fires_R % 2 == 0)

            tag = "OK" if (li_ok and ri_ok and m != i) else "  "
            print(f"    suffix from k={k}: L_fires={b_fires_L}, R_fires={b_fires_R}, L_ok={li_ok}, R_ok={ri_ok} {tag}")

# Now do full check (including procs without binary neighbors)
print("\n=== FULL CHECK (all procs, all suffixes) ===")
for i in range(n):
    if fc[i] < 2: continue
    fire_steps = [k for k in range(CL) if word[k] == i]
    li = left(i, n)
    ri = right(i, n)

    for idx in range(len(fire_steps)):
        a1 = fire_steps[idx]
        a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
        if a2_raw <= a1: a2_raw += CL

        gap = list(range(a1 + 1, a2_raw))
        if not gap: continue

        for k2_raw in gap:
            k2 = k2_raw % CL
            if word[k2] == i: continue

            interval = [t % CL for t in range(k2_raw, a2_raw)]
            li_fires = sum(1 for k in interval if word[k] == li)
            ri_fires = sum(1 for k in interval if word[k] == ri)
            li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
            ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)

            if li_ok and ri_ok:
                print(f"WINNER: proc={i}(mod={moduli[i]}), a1={a1}, a2={a2_raw%CL}, k2={k2}, li_fires={li_fires}, ri_fires={ri_fires}")
