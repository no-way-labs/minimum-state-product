"""
Trace the fiber-match propagation for the n=3 counterexample.
ms=[2,2,3], movers=[0,1,2,0,2,1], CL=6.
Violation: g_2=(1,1,0) and g_5=(0,1,0), p=0, d=3.
"""
cycle = [(0,0,0), (1,0,0), (1,1,0), (1,1,1), (0,1,1), (0,1,0)]
movers = [0, 1, 2, 0, 2, 1]
CL = 6
n = 3
p = 0

# Check fib_p for all pairs at distance 3
print("Fiber p=0 (exclude position 0):")
for i in range(CL):
    fib = (cycle[i][1], cycle[i][2])
    print(f"  [{i}] config={cycle[i]} mover={movers[i]} fib={fib}")

print()
# Check which pairs (i, i+3) have matching fibers
for i in range(CL):
    j = i; k = (i+3) % CL
    fib_j = (cycle[j][1], cycle[j][2])
    fib_k = (cycle[k][1], cycle[k][2])
    match = fib_j == fib_k
    same_p = cycle[j][0] == cycle[k][0]
    print(f"Pair ({j},{k}): fib_j={fib_j} fib_k={fib_k} match={match} same_p={same_p} movers=({movers[j]},{movers[k]})")

print()
print("Propagation trace from (2, 5):")
j, k = 2, 5
for step in range(12):
    fib_j = (cycle[j%CL][1], cycle[j%CL][2])
    fib_k = (cycle[k%CL][1], cycle[k%CL][2])
    match = fib_j == fib_k
    mj = movers[j%CL]
    mk = movers[k%CL]
    print(f"  step {step}: j={j%CL} k={k%CL} fib_j={fib_j} fib_k={fib_k} match={match} "
          f"mover_j={mj} mover_k={mk} p_j={cycle[j%CL][0]} p_k={cycle[k%CL][0]}")

    if not match:
        # Which side preserved the fiber?
        fib_jnext = (cycle[(j+1)%CL][1], cycle[(j+1)%CL][2])
        fib_knext = (cycle[(k+1)%CL][1], cycle[(k+1)%CL][2])
        j_preserves = (fib_jnext == fib_j)
        k_preserves = (fib_knext == fib_k)
        print(f"    fib_j+1={fib_jnext} j_preserves={j_preserves}")
        print(f"    fib_k+1={fib_knext} k_preserves={k_preserves}")
        break

    if mj == mk:
        print(f"    Movers match ({mj}). Both advance.")
        j += 1; k += 1
    else:
        # Movers diverge
        fib_jnext = (cycle[(j+1)%CL][1], cycle[(j+1)%CL][2])
        fib_knext = (cycle[(k+1)%CL][1], cycle[(k+1)%CL][2])
        j_preserves = (mj == p)  # if p fires at j, fiber preserved
        k_preserves = (mk == p)  # if p fires at k, fiber preserved
        print(f"    Movers diverge. j_pres={j_preserves} k_pres={k_preserves}")
        if j_preserves and not k_preserves:
            j += 1; print(f"    j advances to {j%CL}")
        elif k_preserves and not j_preserves:
            k += 1; print(f"    k advances to {k%CL}")
        elif j_preserves and k_preserves:
            # Both preserve: both p fires?
            j += 1; k += 1; print(f"    Both advance (both p fires)")
        else:
            # Neither preserves: check if non-p fires still preserve fiber
            # Actually: fiber changes when a non-p proc fires.
            # But: WHICH non-p proc fires matters.
            print(f"    Neither is p-fire. Check directly.")
            print(f"    fib_j+1={fib_jnext} (match fib_j? {fib_jnext==fib_j})")
            print(f"    fib_k+1={fib_knext} (match fib_k? {fib_knext==fib_k})")
            if fib_jnext == fib_k and fib_knext == fib_j:
                print(f"    SWAP! fibers cross.")
            break
