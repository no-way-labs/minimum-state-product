"""Recheck the alleged failure word."""
def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 5
moduli = [2, 2, 2, 3, 3]
word = [3, 3, 4, 0, 4, 3, 2, 1, 0, 4, 3, 3, 2, 3, 4, 0, 1, 2]
CL = len(word)

fc = [0] * n
for m in word:
    fc[m] += 1
print(f"fc = {fc}, all>=2: {all(f>=2 for f in fc)}, any>=3: {any(f>=3 for f in fc)}")

cw = sum(1 for k in range(CL) if word[(k+1) % CL] == right(word[k], n))
ccw = sum(1 for k in range(CL) if word[(k+1) % CL] == left(word[k], n))
print(f"cw={cw}, ccw={ccw}, ZW: {cw==ccw}, cw>0: {cw>0}")

# Check locality
for k in range(CL):
    m_curr = word[k]
    m_next = word[(k+1) % CL]
    if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
        print(f"LOCALITY VIOLATION at k={k}: {m_curr} -> {m_next}")
        break
else:
    print("Locality: OK")

# Full exhaustive check - try ALL (i, a1, a2, k2) combos including wrap
print("\nExhaustive check:")
found = False
for i in range(n):
    if fc[i] < 2: continue
    fire_steps = [k for k in range(CL) if word[k] == i]

    for idx in range(len(fire_steps)):
        a1 = fire_steps[idx]
        a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
        if a2_raw <= a1: a2_raw += CL

        for k2_raw in range(a1 + 1, a2_raw):
            k2 = k2_raw % CL
            if word[k2] == i: continue

            interval = [t % CL for t in range(k2_raw, a2_raw)]
            li = left(i, n)
            ri = right(i, n)
            li_fires = sum(1 for k in interval if word[k] == li)
            ri_fires = sum(1 for k in interval if word[k] == ri)
            li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
            ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)

            if li_ok and ri_ok:
                print(f"FOUND: proc={i}, a1={a1}, a2={a2_raw%CL}, k2={k2}, li_fires={li_fires}, ri_fires={ri_fires}")
                found = True

if not found:
    print("NO SOLUTION FOUND - this is a genuine counterexample!")
    print("This means the mechanism doesn't work for ALL valid ZW cycles")
    print("OR this word doesn't correspond to a valid good cycle")

    # Does this actually correspond to a realizable good cycle?
    # Check: is every proc's fire count != 1?
    print(f"\nfc check: {fc}")
    for p in range(n):
        if fc[p] == 1:
            print(f"  proc {p} has fc=1 - invalid for good cycle!")

    # Binary fire counts must be even
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0:
            print(f"  proc {p} is binary with ODD fc={fc[p]} - IMPOSSIBLE in good cycle!")
