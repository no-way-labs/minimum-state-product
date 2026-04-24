"""
Analyze sorry 6: Pn1:(2,0,0) c1=0 at n=9.
Goal: understand why CPhiStep + boundary-change + non617 + Pn1:(2,0,0) + c1=0 => False.

Boundary values of c: c[0]=0, c[1]=0, c[7]=2, c[8]=0 (n=9, positions n-2=7, n-1=8)
Move at position 8 (top): output = TTopVal(c[7], c[8], c[0]) = TTopVal(2, 0, 0) = 1
So c' has c'[8] = 1, all other positions same as c.
"""

# CUP-2 transition tables
def TBotVal(L, S, R):
    t = {
        (0,0,0):1,(0,0,1):1,(0,0,2):0,
        (0,1,0):1,(0,1,1):1,(0,1,2):1,
        (1,0,0):0,(1,0,1):1,(1,0,2):0,
        (1,1,0):0,(1,1,1):1,(1,1,2):0,
    }
    return t.get((L,S,R), 0)

def TLowVal(L, S, R):
    t = {
        (0,0,0):0,(0,0,1):0,(0,0,2):0,
        (0,1,0):0,(0,1,1):1,(0,1,2):0,
        (0,2,0):0,(0,2,1):2,(0,2,2):0,
        (1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):2,
        (1,2,0):0,(1,2,1):1,(1,2,2):2,
    }
    return t.get((L,S,R), 0)

def TMidVal(L, S, R):
    t = {
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
    return t.get((L,S,R), 0)

def THighVal(L, S, R):
    t = {
        (0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
        (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
        (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2,
    }
    return t.get((L,S,R), 0)

def TTopVal(L, S, R):
    t = {
        (0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
        (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
        (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1,
    }
    return t.get((L,S,R), 0)

# State space dimensions for CUP-2 with n processors
# Position 0: bot (2 states: 0,1)
# Position 1: low (3 states: 0,1,2)
# Positions 2..n-3: mid (3 states each)
# Position n-2: high (3 states: 0,1,2)
# Position n-1: top (2 states: 0,1)

def num_states(n, i):
    if i == 0: return 2
    if i == 1: return 3
    if i == n-1: return 2
    if i == n-2: return 3
    return 3  # mid

def output_val(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

def left(n, i):
    return (i - 1) % n

def right(n, i):
    return (i + 1) % n

def move(n, config, i):
    c = list(config)
    L = c[left(n, i)]
    S = c[i]
    R = c[right(n, i)]
    out = output_val(n, i, L, S, R)
    c[i] = out
    return tuple(c)

def is_privileged(n, config, i):
    L = config[left(n, i)]
    S = config[i]
    R = config[right(n, i)]
    out = output_val(n, i, L, S, R)
    return out != S

def frontier_count(n, config):
    fc = 0
    for j in range(n):
        if config[j] != config[(j+1) % n]:
            fc += 1
    return fc

def exp2_bit(n, j, a, b):
    if 2 <= j and j + 2 < n and a == 2 and b != 2:
        return 1
    return 0

def int21_bit(n, j, a, b):
    if 2 <= j and j + 2 < n and a == 2 and b == 1:
        return 1
    return 0

def tp_invariant(n, config):
    exp2 = sum(exp2_bit(n, j, config[j], config[(j+1)%n]) for j in range(n))
    int21 = sum(int21_bit(n, j, config[j], config[(j+1)%n]) for j in range(n))
    weight = sum(j * exp2_bit(n, j, config[j], config[(j+1)%n]) for j in range(n))
    return (exp2, int21, weight)

def tp_bad_step_fwd(n, config):
    """Return all configs reachable via one TP-preserving bad step."""
    tp = tp_invariant(n, config)
    results = []
    for i in range(n):
        if is_privileged(n, config, i):
            c2 = move(n, config, i)
            if tp_invariant(n, c2) == tp:
                results.append(c2)
    return results

def tp_reachable_set(n, config):
    """BFS to find all TP-reachable configs from config."""
    visited = {config}
    queue = [config]
    while queue:
        c = queue.pop(0)
        for c2 in tp_bad_step_fwd(n, c):
            if c2 not in visited:
                visited.add(c2)
                queue.append(c2)
    return visited

def phi_full(n, config):
    """Max fc over all TP-reachable configs."""
    return max(frontier_count(n, c) for c in tp_reachable_set(n, config))

# === MAIN ANALYSIS ===
n = 9
import itertools

print(f"=== Sorry 6 analysis: Pn1:(2,0,0) c1=0 at n={n} ===")
print(f"c[0]=0, c[1]=0, c[7]=2, c[8]=0")
print()

# Enumerate all possible interior configs (positions 2,3,4,5,6)
# Position 2: mid (0,1,2)
# Position 3: mid (0,1,2)
# Position 4: mid (0,1,2)
# Position 5: mid (0,1,2)
# Position 6 = n-3: mid (0,1,2)
count = 0
contradiction_count = 0
interesting = []

for interior in itertools.product(range(3), repeat=5):
    c2, c3, c4, c5, c6 = interior
    # c = (c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7], c[8])
    config_c = (0, 0, c2, c3, c4, c5, c6, 2, 0)
    config_cprime = move(n, config_c, 8)  # move at position n-1=8

    # Check: is position 8 privileged?
    if not is_privileged(n, config_c, 8):
        continue  # Not a valid step

    count += 1

    fc_c = frontier_count(n, config_c)
    fc_cprime = frontier_count(n, config_cprime)

    # Check fc gain = +1
    if fc_cprime != fc_c + 1:
        continue

    # Check: is move at idx0 also TP-preserving bad step from c?
    tp_c = tp_invariant(n, config_c)

    if is_privileged(n, config_c, 0):
        config_idx0 = move(n, config_c, 0)
        tp_idx0 = tp_invariant(n, config_idx0)
        fc_idx0 = frontier_count(n, config_idx0)

        if tp_idx0 == tp_c:
            # Move at idx0 is TP-preserving
            # Check if this gives fc gain = +2
            if fc_idx0 == fc_c + 2:
                # Both conditions met! Now check PhiFull
                pf_c = phi_full(n, config_c)
                pf_cprime = phi_full(n, config_cprime)
                tp_cprime = tp_invariant(n, config_cprime)

                interesting.append({
                    'config': config_c,
                    'cprime': config_cprime,
                    'fc_c': fc_c,
                    'fc_cprime': fc_cprime,
                    'pf_c': pf_c,
                    'pf_cprime': pf_cprime,
                    'tp_c': tp_c,
                    'tp_cprime': tp_cprime,
                    'tp_eq': tp_c == tp_cprime,
                    'pf_eq': pf_c == pf_cprime,
                })

print(f"Configs with privileged position 8: {count}")
print(f"Configs with fc gain +1 and idx0 TP-preserving with fc gain +2: {len(interesting)}")
print()

for item in interesting:
    print(f"c = {item['config']}")
    print(f"  c' = {item['cprime']}")
    print(f"  fc(c) = {item['fc_c']}, fc(c') = {item['fc_cprime']}")
    print(f"  PhiFull(c) = {item['pf_c']}, PhiFull(c') = {item['pf_cprime']}")
    print(f"  TP(c) = {item['tp_c']}, TP(c') = {item['tp_cprime']}")
    print(f"  TP eq: {item['tp_eq']}, PhiFull eq: {item['pf_eq']}")

    if item['tp_eq'] and item['pf_eq']:
        print(f"  *** WOULD SATISFY CPhiStep hypotheses! ***")
    elif item['tp_eq'] and not item['pf_eq']:
        print(f"  TP preserved but PhiFull changes: {item['pf_c']} -> {item['pf_cprime']}")
        print(f"  This is where the contradiction comes from!")
    elif not item['tp_eq']:
        print(f"  TP NOT preserved: contradiction from TpInvariant change")
    print()

# Also check: for ALL valid configs, does PhiFull ever stay equal?
print("=== Checking ALL Pn1:(2,0,0) configs for PhiFull equality ===")
pf_eq_count = 0
tp_eq_count = 0
both_eq_count = 0

for interior in itertools.product(range(3), repeat=5):
    c2, c3, c4, c5, c6 = interior
    config_c = (0, 0, c2, c3, c4, c5, c6, 2, 0)

    if not is_privileged(n, config_c, 8):
        continue

    config_cprime = move(n, config_c, 8)
    fc_c = frontier_count(n, config_c)
    fc_cprime = frontier_count(n, config_cprime)

    if fc_cprime != fc_c + 1:
        continue

    tp_c = tp_invariant(n, config_c)
    tp_cprime = tp_invariant(n, config_cprime)

    if tp_c != tp_cprime:
        continue

    tp_eq_count += 1

    pf_c = phi_full(n, config_c)
    pf_cprime = phi_full(n, config_cprime)

    if pf_c == pf_cprime:
        pf_eq_count += 1
        both_eq_count += 1
        print(f"  BOTH EQ: c={config_c}, fc={fc_c}->{fc_cprime}, PF={pf_c}->{pf_cprime}")
    else:
        # This is where the contradiction comes from
        pass

print(f"\nTP preserved count: {tp_eq_count}")
print(f"PhiFull also equal: {pf_eq_count}")
print(f"Conclusion: PhiFull equality is {'never' if pf_eq_count == 0 else 'sometimes'} satisfied")
