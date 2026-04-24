"""Count ALL simple directed cycles on Q4, including length 2 and 3."""

n = 4
N = 1 << n

def cube_neighbors(v):
    return [(v ^ (1 << b), b) for b in range(n)]

# Length-2 cycles: edge traversed both ways. v0 -> v1 -> v0.
# These are just the 32 undirected edges of Q4.
# Canonical: v0 < v1, direction v0 -> v1 first.
count_len2 = 0
blocked_len2 = 0

all_cfgs = [tuple((v >> b) & 1 for b in range(n)) for v in range(N)]

def cfg(v):
    return tuple((v >> b) & 1 for b in range(n))

def check_blocked_full(codes):
    """Full blocking check for a cycle of vertex codes."""
    L = len(codes)
    path = [cfg(v) for v in codes]

    # Find movers and extract forced entries
    forced = {}  # (proc, L, S, R) -> val
    movers = []
    for k in range(L):
        c = codes[k]
        c_next = codes[(k + 1) % L]
        diff = c ^ c_next
        mover = diff.bit_length() - 1
        movers.append(mover)

    conflict = False
    for k in range(L):
        c = path[k]
        m = movers[k]
        c_next = path[(k + 1) % L]

        # Mover entry
        key = (m, c[(m-1)%n], c[m], c[(m+1)%n])
        val = c_next[m]
        if key in forced and forced[key] != val:
            conflict = True
            break
        forced[key] = val

        # Non-mover entries
        for j in range(n):
            if j == m:
                continue
            key_j = (j, c[(j-1)%n], c[j], c[(j+1)%n])
            val_j = c[j]
            if key_j in forced and forced[key_j] != val_j:
                conflict = True
                break
        if conflict:
            break

    if conflict:
        return True, "TF_CONFLICT"

    # Forced kernel check
    good_set = set(path)
    bad_set = set(c for c in all_cfgs if c not in good_set)

    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c_tup in bad_set:
            v = sum(c_tup[b] << b for b in range(n))
            has_forced_bad = False
            has_unknown = False
            for p in range(n):
                key = (p, c_tup[(p-1)%n], c_tup[p], c_tup[(p+1)%n])
                if key in forced:
                    if forced[key] != c_tup[p]:  # privileged
                        succ_v = v ^ (1 << p)
                        succ_tup = cfg(succ_v)
                        if succ_tup in bad_set:
                            has_forced_bad = True
                else:
                    # Unknown: adversary could make privileged
                    succ_v = v ^ (1 << p)
                    succ_tup = cfg(succ_v)
                    if succ_tup in bad_set:
                        has_unknown = True  # can't remove as sink
            if not has_forced_bad and not has_unknown:
                to_remove.add(c_tup)
        if to_remove:
            bad_set -= to_remove
            changed = True

    if bad_set:
        return True, f"FORCED_KERNEL({len(bad_set)})"
    return False, "SURVIVES"

# Check length-2 cycles
print("=== Length-2 cycles ===")
for v0 in range(N):
    for bit in range(n):
        v1 = v0 ^ (1 << bit)
        if v1 > v0:  # canonical
            is_blocked, reason = check_blocked_full([v0, v1])
            count_len2 += 1
            if is_blocked:
                blocked_len2 += 1
            else:
                print(f"  SURVIVOR: [{v0}, {v1}] reason={reason}")

print(f"Length-2: {count_len2} cycles, {blocked_len2} blocked, {count_len2-blocked_len2} survive")

# Check length-3 cycles (if any exist on Q4)
# A 3-cycle needs v0->v1->v2->v0 with each pair cube-adjacent.
# v0 XOR v1, v1 XOR v2, v2 XOR v0 each a power of 2.
# But (v0 XOR v1) XOR (v1 XOR v2) = v0 XOR v2.
# If v0 XOR v1 = 2^a and v1 XOR v2 = 2^b, then v0 XOR v2 = 2^a XOR 2^b.
# For v0 XOR v2 to be a power of 2, need a = b, but then v0 = v2. Contradiction.
print("\n=== Length-3 cycles ===")
print("Impossible on Q4 (XOR of two different powers of 2 is not a power of 2)")

# Total with length >= 4 (from previous script)
print("\n=== Length >= 4 ===")
print("From previous: 14,704 unique directed cycles, all blocked")

print(f"\n=== GRAND TOTAL: {count_len2 + 14704} cycles, all need to be blocked ===")
if blocked_len2 == count_len2:
    print("Length-2: ALL BLOCKED")
    print("Length >= 4: ALL BLOCKED (from previous)")
    print("Length-3: IMPOSSIBLE")
    print("\n=== ALL CYCLES ON Q4 ARE BLOCKED ===")
