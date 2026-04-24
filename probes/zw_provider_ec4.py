"""
Investigation part 4:

Q1: With >= 3 binary in ring of n >= 9, does B-T-B sandwich always exist?
Q2: If not, what's the alternative EC mechanism for zw_provider_ec?
Q3: Can we bypass zw_provider_ec by proving fc >= 3 impossible more directly?

For Q1: enumerate all possible binary placement patterns.
"""

def has_btb_sandwich(n, binary_positions):
    """Check if there's a ternary proc with binary on both sides."""
    binary_set = set(binary_positions)
    for t in range(n):
        if t not in binary_set:  # t is ternary
            left = (t - 1) % n
            right = (t + 1) % n
            if left in binary_set and right in binary_set:
                return True
    return False

def check_all_placements(n, num_binary):
    """Check all ways to place num_binary binary procs in ring of size n."""
    from itertools import combinations

    total = 0
    no_sandwich = 0
    no_sandwich_examples = []

    for positions in combinations(range(n), num_binary):
        total += 1
        if not has_btb_sandwich(n, positions):
            no_sandwich += 1
            if len(no_sandwich_examples) < 5:
                no_sandwich_examples.append(positions)

    return total, no_sandwich, no_sandwich_examples

print("Q1: Does B-T-B sandwich always exist with >= 3 binary?")
print("=" * 60)

for n in [5, 7, 9, 11]:
    for nb in [3, 4, 5]:
        if nb >= n: continue
        total, no_btb, examples = check_all_placements(n, nb)
        status = "ALL have sandwich" if no_btb == 0 else f"{no_btb}/{total} LACK sandwich"
        print(f"  n={n}, #binary={nb}: {status}")
        for ex in examples:
            print(f"    Example: binary at {ex}")
            # Show the ring pattern
            ring = ['T'] * n
            for p in ex:
                ring[p] = 'B'
            print(f"    Ring: {' '.join(ring)}")

print()
print("=" * 60)
print("Q2: For configurations WITHOUT B-T-B sandwich, what pattern?")
print("=" * 60)
print()
print("Analysis:")
print("No B-T-B means: every ternary proc has at most 1 binary neighbor.")
print("This means all binary procs are 'isolated' — no two are within distance 2.")
print("Pattern: B, T, T+, B, T, T+, B, T, T+, ...")
print("With 3 binary in n=9: e.g., positions 0, 3, 6 → B T T B T T B T T")
print("Check: proc 1 has left=B, right=T → only 1 binary neighbor")
print("       proc 2 has left=T, right=B → only 1 binary neighbor")
print("So no sandwich!")
print()

# Verify
n = 9
ring = ['T'] * n
for p in [0, 3, 6]:
    ring[p] = 'B'
print(f"n=9, binary at {{0,3,6}}: {' '.join(ring)}")
print(f"Has B-T-B sandwich: {has_btb_sandwich(n, [0, 3, 6])}")

print()
print("=" * 60)
print("Q3: Alternative approaches for zw_provider_ec")
print("=" * 60)
print()
print("Since B-T-B sandwich is NOT guaranteed, we need a different approach.")
print()
print("Approach A: Direct ZW argument")
print("Under ZW with cw > 0 and fc >= 3 at some proc q:")
print("  - Total CW steps = total CCW steps (zero winding)")
print("  - CL > 2n (since sum fc > 2n)")
print("  - Some proc fires 3+ times")
print("  - The cycle visits the ring in a back-and-forth manner")
print("  - With sub-threshold product, pigeonhole on configs at binary procs")
print()
print("Approach B: Use a different existing theorem")
print("The codebase might have EC theorems that don't need B-T-B.")
print()
print("Approach C: Prove directly that fc >= 3 is impossible under ZW + cw > 0")
print("without going through EC. If CL = CW + CCW and winding = 0,")
print("then CW = CCW = CL/2. Each proc fires some CW and some CCW.")
print("Can we use the walk structure to bound fc?")
print()

# Let's investigate Approach C more carefully
print("=" * 60)
print("Approach C investigation: ZW + cw > 0 walk structure")
print("=" * 60)

def analyze_zw_walk(word, n):
    """Analyze the CW/CCW structure of a ZW walk."""
    L = len(word)
    cw_steps = []
    ccw_steps = []
    for i in range(L):
        curr = word[i]
        nxt = word[(i + 1) % L]
        if nxt == (curr + 1) % n:
            cw_steps.append(i)
        else:
            ccw_steps.append(i)

    # For each proc, count CW and CCW fires
    proc_cw = [0] * n
    proc_ccw = [0] * n
    for i in range(L):
        p = word[i]
        nxt = word[(i + 1) % L]
        if nxt == (p + 1) % n:
            proc_cw[p] += 1
        else:
            proc_ccw[p] += 1

    return proc_cw, proc_ccw, len(cw_steps), len(ccw_steps)

# Check the CL=12 words with fc >= 3
print("\nCL=12 ZW words with fc >= 3 that have valid cycles:")
words_with_cycles = [
    (0, 1, 2, 3, 4, 0, 4, 3, 4, 3, 2, 1),  # fc=[2,2,2,3,3]
    (0, 1, 2, 3, 4, 3, 4, 0, 4, 3, 2, 1),  # fc=[2,2,2,3,3]
    (0, 1, 2, 3, 4, 3, 4, 3, 2, 1, 0, 4),  # fc=[2,2,2,3,3]
]

for word in words_with_cycles:
    fc = [0] * 5
    for p in word: fc[p] += 1
    proc_cw, proc_ccw, total_cw, total_ccw = analyze_zw_walk(word, 5)
    print(f"\n  Word: {word}")
    print(f"  FC: {fc}")
    print(f"  Total CW={total_cw}, CCW={total_ccw}")
    print(f"  Per-proc CW: {proc_cw}")
    print(f"  Per-proc CCW: {proc_ccw}")

    # Binary procs with fc=2: they fire once CW, once CCW
    for p in range(5):
        if fc[p] == 2:
            print(f"    Proc {p} (fc=2): CW={proc_cw[p]}, CCW={proc_ccw[p]}")

print()
print("=" * 60)
print("KEY OBSERVATION")
print("=" * 60)
print()
print("For a ZW walk with cw > 0:")
print("- CW = CCW = CL/2")
print("- Each step is CW or CCW")
print("- If all fc = 2, then CL = 2n, and CW = CCW = n")
print("- Each proc fires exactly once CW and once CCW (palindrome)")
print()
print("If some fc >= 3, then CL > 2n, CW = CCW > n.")
print("But a proc with fc = 2 still fires 2 times total.")
print("Its CW + CCW fires = 2.")
print("If CW fires = 0 for some proc, it fires 2 CCW → but then the")
print("walk can't complete the CW direction past this proc.")
print()
print("Actually, each proc must fire at least once CW and once CCW")
print("in a zero-winding walk (otherwise the walk can't return).")
print("So for fc=2 procs: exactly 1 CW, 1 CCW.")
print("For fc=3 procs: either 2 CW + 1 CCW, or 1 CW + 2 CCW.")
