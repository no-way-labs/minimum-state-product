#!/usr/bin/env python3
"""
Understand the exact scope of the claim.

The exceptions are uniform sweeps at ms=[2,2,2,2,3] (4 binary, 1 ternary).
Key question: do these exceptions have a sandwiched ternary with (1,1) phases
where BOTH neighbors are binary AND both neighbors are NOT adjacent to t?

Actually, re-read: the claim says "at least 3 binary processors" and
"a sandwiched ternary t: m_t = 3, m_{t-1} = 2, m_{t+1} = 2".
The exceptions satisfy this.

But: in the exceptions, the binary procs with all-binary neighbors
(procs 1,2) have ctx_space=8 and still avoid EC because the sweep
uses only 6 out of 8 contexts.

Question: Can we add a condition that the cycle is NOT a uniform sweep?
Or do we need a different approach?

Let me check: are these exceptions REALIZABLE? That is, can they actually
be good cycles of a valid self-stabilizing system?
"""
from collections import Counter

def build_configs(ms, n, word):
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]

def check_system_feasibility(word, configs, ms, n):
    """Check if transition function can be defined consistently.
    For each proc p: the function f_p(L,S,R) must:
    - When p is mover: f_p(L,S,R) != S (must change)
    - When p is non-mover: f_p(L,S,R) = S (must stay)
    Check for conflicts."""
    L = len(word)
    for p in range(n):
        pL, pR = (p-1)%n, (p+1)%n
        # Build required transitions
        transitions = {}  # (L,S,R) -> required output
        for s in range(L):
            ctx = (configs[s][pL], configs[s][p], configs[s][pR])
            if word[s] == p:
                # Mover: output != S
                new_val = configs[(s+1)%L][p]
                if ctx in transitions:
                    if transitions[ctx] != new_val:
                        return False, f"mover conflict at proc {p}"
                transitions[ctx] = new_val
            else:
                # Non-mover: output = S
                if ctx in transitions:
                    if transitions[ctx] != ctx[1]:
                        return False, f"EC conflict at proc {p}: ctx={ctx}"
                transitions[ctx] = ctx[1]
        # Also check mover outputs != own state
        for s in range(L):
            if word[s] == p:
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if transitions[ctx] == ctx[1]:
                    return False, f"mover unchanged at proc {p}"
    return True, "feasible"

# Check the two exceptions
n = 5
ms = [2, 2, 2, 2, 3]
exceptions = [
    (4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4),
    (4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4),
]

for word in exceptions:
    configs = build_configs(ms, n, word)
    ok, msg = check_system_feasibility(word, configs, ms, n)
    fc = Counter(word)
    print(f"word={word}")
    print(f"  fc={dict(fc)}")
    print(f"  feasible: {ok} ({msg})")
    print()

    # Show the transition tables
    L = len(word)
    for p in range(n):
        pL, pR = (p-1)%n, (p+1)%n
        print(f"  Proc {p} (m={ms[p]}):")
        transitions = {}
        for s in range(L):
            ctx = (configs[s][pL], configs[s][p], configs[s][pR])
            if word[s] == p:
                new_val = configs[(s+1)%L][p]
                transitions[ctx] = (new_val, 'FIRE')
            else:
                if ctx not in transitions:
                    transitions[ctx] = (ctx[1], 'stay')
        for ctx in sorted(transitions.keys()):
            val, role = transitions[ctx]
            marker = " <-- FIRE" if role == 'FIRE' else ""
            print(f"    f({ctx}) = {val}{marker}")
    print()

# Now check: what proportion of ALL sub-threshold multisets have exceptions?
print("="*70)
print("SYSTEMATIC CHECK: all sub-threshold multisets at n=5")
print("="*70)

def generate_multisets(n, threshold):
    """Generate all multisets of state sizes with product < threshold, each m_i >= 2."""
    results = []
    def gen(pos, current, prod):
        if pos == n:
            if prod < threshold:
                results.append(tuple(current))
            return
        remaining = n - pos
        for m in range(2, threshold):
            new_prod = prod * m
            if new_prod * (2 ** (remaining - 1)) >= threshold:
                if new_prod >= threshold:
                    break
            gen(pos + 1, current + [m], new_prod)
    gen(0, [], 1)
    return results

# More efficient: just enumerate multisets
from itertools import combinations_with_replacement, permutations

n = 5
threshold = 4 * (3 ** (n-2))
print(f"n={n}, threshold={threshold}")

# Generate sorted multisets with product < threshold
all_multisets = set()
def gen_ms(pos, current, prod_so_far, min_val=2):
    if pos == n:
        if prod_so_far < threshold:
            all_multisets.add(tuple(sorted(current)))
        return
    remaining = n - pos
    max_val = threshold // (prod_so_far * (2 ** (remaining - 1))) + 1
    for m in range(min_val, max_val + 1):
        if prod_so_far * m >= threshold and remaining > 1:
            # Can't possibly stay under with all remaining at 2
            if prod_so_far * m * (2 ** (remaining - 1)) >= threshold:
                break
        gen_ms(pos + 1, current + [m], prod_so_far * m, m)

gen_ms(0, [], 1)
print(f"Found {len(all_multisets)} sorted multisets with product < {threshold}")

# For each, check if it has >=3 binary and a sandwiched ternary
total_relevant = 0
total_exceptions = 0
exception_details = []

for ms_sorted in sorted(all_multisets):
    binary_count = sum(1 for m in ms_sorted if m == 2)
    if binary_count < 3:
        continue

    # Try all rotations (placements on ring)
    seen_placements = set()
    for perm in permutations(ms_sorted):
        ms_list = list(perm)
        # Normalize by rotation to avoid duplicates on ring
        canonical = min(tuple(ms_list[i:] + ms_list[:i]) for i in range(n))
        if canonical in seen_placements:
            continue
        seen_placements.add(canonical)

        ms_list = list(canonical)

        # Check for sandwiched ternary
        sandwiched = [p for p in range(n) if ms_list[p] == 3
                      and ms_list[(p-1)%n] == 2 and ms_list[(p+1)%n] == 2]
        if not sandwiched:
            continue

        prod = 1
        for m in ms_list:
            prod *= m

        total_relevant += 1

        # Enumerate cycles
        words = []
        ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
        start = tuple(0 for _ in range(n))

        def dfs(word, fc, config):
            if len(word) > 16:
                return
            if len(word) >= n and config == start:
                if all(fc[p] > 0 and fc[p] % ms_list[p] == 0 for p in range(n)):
                    words.append(tuple(word))
                return
            last = word[-1]
            for nxt in ring_adj[last]:
                nc = list(config)
                nc[nxt] = (nc[nxt] + 1) % ms_list[nxt]
                nf = list(fc)
                nf[nxt] += 1
                word.append(nxt)
                dfs(word, nf, tuple(nc))
                word.pop()

        for p in range(n):
            first = list(start)
            first[p] = (first[p] + 1) % ms_list[p]
            dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))

        exc_count = 0
        cycle_count = 0
        for word in words:
            configs = build_configs(ms_list, n, word)
            if configs is None:
                continue

            has_11 = False
            for t in sandwiched:
                L = len(word)
                bL = (t - 1) % n
                bR = (t + 1) % n
                t_steps = [s for s in range(L) if word[s] == t]
                if not t_steps:
                    continue
                for idx in range(len(t_steps)):
                    s1 = t_steps[idx]
                    s2 = t_steps[(idx + 1) % len(t_steps)]
                    phase_steps = []
                    s = (s1 + 1) % L
                    while s != s2:
                        phase_steps.append(s)
                        s = (s + 1) % L
                    J = sum(1 for s in phase_steps if word[s] == bL)
                    K = sum(1 for s in phase_steps if word[s] == bR)
                    if J == 1 and K == 1:
                        has_11 = True
                        break
                if has_11:
                    break

            if not has_11:
                continue
            cycle_count += 1

            # Check EC
            has_ec = False
            for p in range(n):
                mover_ctx = set()
                nonmover_ctx = set()
                pL = (p - 1) % n
                pR = (p + 1) % n
                for s in range(L):
                    ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                    if word[s] == p:
                        mover_ctx.add(ctx)
                    else:
                        nonmover_ctx.add(ctx)
                if mover_ctx & nonmover_ctx:
                    has_ec = True
                    break

            if not has_ec:
                exc_count += 1

        if exc_count > 0:
            total_exceptions += 1
            exception_details.append((ms_list, cycle_count, exc_count))
            print(f"  EXCEPTION: ms={ms_list}, prod={prod}, "
                  f"cycles_with_11={cycle_count}, no_EC={exc_count}")

print(f"\nTotal relevant placements: {total_relevant}")
print(f"Placements with exceptions: {total_exceptions}")
for ms_list, cc, ec in exception_details:
    print(f"  ms={ms_list}: {ec}/{cc} exceptions")
