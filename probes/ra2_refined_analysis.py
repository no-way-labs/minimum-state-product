"""
Script 5: Refined analysis — why does the double-loop AVOID EC despite pigeonhole?

The key insight from Script 4: CL=10 > ctx_space=8 at proc 1, yet NO EC found.
This means all context repetitions are non-mover-vs-non-mover (harmless).

Let's understand why, and find where the argument DOES work.
"""

from collections import Counter, defaultdict
from itertools import combinations
import random
from math import prod

def build_double_loop_configs(n, ms, num_trials=2000):
    """Build consistent configs for double-loop walk and analyze context reuse."""
    walk = [i % n for i in range(2*n)]
    cl = len(walk)
    results = []

    for _ in range(num_trials):
        config = [random.randrange(ms[p]) for p in range(n)]
        configs = [tuple(config)]
        seen = {tuple(config)}
        ok = True

        for step in range(cl - 1):
            mover = walk[step]
            old_val = config[mover]
            choices = [v for v in range(ms[mover]) if v != old_val]
            random.shuffle(choices)
            found = False
            for new_val in choices:
                config[mover] = new_val
                c = tuple(config)
                if c not in seen:
                    seen.add(c)
                    configs.append(c)
                    found = True
                    break
            if not found:
                ok = False
                break

        if not ok:
            continue

        # Check cycle closure
        mover = walk[cl - 1]
        needed = configs[0][mover]
        close_ok = True
        for p in range(n):
            if p != mover and config[p] != configs[0][p]:
                close_ok = False
                break
        if not close_ok or needed == config[mover]:
            continue

        results.append(configs)
    return walk, results

def analyze_context_reuse(walk, configs, n, ms):
    """For each processor, analyze mover vs non-mover context sets."""
    cl = len(walk)
    analysis = {}

    for p in range(n):
        mover_ctxs = set()
        nonmover_ctxs = set()
        mover_ctx_list = []
        nonmover_ctx_list = []

        for i in range(cl):
            L = configs[i][(p-1) % n]
            S = configs[i][p]
            R = configs[i][(p+1) % n]
            ctx = (L, S, R)

            if walk[i] == p:
                mover_ctxs.add(ctx)
                mover_ctx_list.append((i, ctx))
            else:
                nonmover_ctxs.add(ctx)
                nonmover_ctx_list.append((i, ctx))

        overlap = mover_ctxs & nonmover_ctxs
        # Check if overlap constitutes EC
        ec_at_p = False
        if overlap:
            # For each overlapping context, check if mover output != S
            for ctx in overlap:
                L, S, R = ctx
                # Find mover step with this context
                for i, c in mover_ctx_list:
                    if c == ctx:
                        next_i = (i+1) % cl
                        S_next = configs[next_i][p]
                        if S_next != S:
                            ec_at_p = True
                            break
                if ec_at_p:
                    break

        analysis[p] = {
            'mover_ctxs': mover_ctxs,
            'nonmover_ctxs': nonmover_ctxs,
            'overlap': overlap,
            'ec': ec_at_p,
            'ctx_space': ms[(p-1)%n] * ms[p] * ms[(p+1)%n],
            'total_distinct': len(mover_ctxs | nonmover_ctxs),
        }

    return analysis

print("=" * 70)
print("SCRIPT 5: Refined Context Reuse Analysis")
print("=" * 70)

# Analyze n=5
print("\n--- n=5, ms=[2,2,2,3,3] ---")
n = 5
ms = [2, 2, 2, 3, 3]

walk, configs_list = build_double_loop_configs(n, ms, num_trials=5000)
print(f"Walk: {walk}")
print(f"Found {len(configs_list)} consistent config assignments")

if configs_list:
    # Analyze first few
    for idx, configs in enumerate(configs_list[:3]):
        print(f"\n  Config assignment #{idx}:")
        for i, c in enumerate(configs):
            print(f"    step {i}: mover={walk[i]}, config={c}")

        analysis = analyze_context_reuse(walk, configs, n, ms)
        print(f"\n  Context analysis:")
        for p in range(n):
            a = analysis[p]
            print(f"    Proc {p} (m={ms[p]}): ctx_space={a['ctx_space']}, "
                  f"used={a['total_distinct']}, "
                  f"mover_ctxs={len(a['mover_ctxs'])}, "
                  f"nonmover_ctxs={len(a['nonmover_ctxs'])}, "
                  f"overlap={len(a['overlap'])}, EC={a['ec']}")
            if a['overlap']:
                print(f"      Overlapping contexts: {a['overlap']}")
                # Check: in overlap, does mover output = S?
                for ctx in a['overlap']:
                    L, S, R = ctx
                    print(f"      ctx=({L},{S},{R}): mover changes S={S} to ", end="")
                    for i in range(len(walk)):
                        if walk[i] == p:
                            c = (configs[i][(p-1)%n], configs[i][p], configs[i][(p+1)%n])
                            if c == ctx:
                                next_S = configs[(i+1)%len(configs)][p]
                                print(f"S'={next_S}", end="")
                    print()

    # Statistics across all config assignments
    print(f"\n  Aggregate statistics across {len(configs_list)} assignments:")
    overlap_counts = defaultdict(list)
    ec_counts = Counter()
    for configs in configs_list:
        analysis = analyze_context_reuse(walk, configs, n, ms)
        for p in range(n):
            overlap_counts[p].append(len(analysis[p]['overlap']))
            if analysis[p]['ec']:
                ec_counts[p] += 1

    for p in range(n):
        avg_overlap = sum(overlap_counts[p]) / len(overlap_counts[p])
        print(f"    Proc {p}: avg_overlap={avg_overlap:.2f}, EC_count={ec_counts[p]}/{len(configs_list)}")

# KEY INSIGHT: Why does the double loop avoid EC?
print("\n\n--- KEY INSIGHT: Why double-loop avoids EC ---")
print("""
In the double-loop walk [0,1,2,...,n-1,0,1,...,n-1]:
- Processor p fires at steps p and p+n.
- Between these two firings, config[p] stays fixed (non-mover).

At step p (first firing):
  Context = (config[p][(p-1)%n], config[p][p], config[p][(p+1)%n])
  Mover transitions: S -> S' (different value)

At step p+n (second firing):
  By this time, ALL other processors have fired once.
  The neighbors (p-1) and (p+1) have both changed their values.
  So the context (L', S', R') is COMPLETELY DIFFERENT from step p.
  (L changed because p-1 fired; R changed because p+1 fired; S changed from first firing)

Between firings (steps p+1 to p+n-1): p is non-mover.
  The context changes whenever p-1, p+1 fire (steps p-1, p+1 respectively).
  But S stays at S' (the value after first firing).

The SEPARATION between mover contexts and non-mover contexts arises because:
- Mover steps see S=old_value, non-mover steps (after first firing) see S=new_value.
- Since S differs, the full context (L,S,R) differs even if (L,R) happen to match.

This is the BINARY PROTECTION: with S in {0,1}, the mover sees S=0 (say),
then all subsequent non-mover steps see S=1. Different S => different context.
NO EC possible at this processor for the double loop!

WAIT - but proc 1 has ctx_space=8 and CL=10. If mover contexts have S=0
and non-mover contexts (after first fire) have S=1, that's at most 4+4=8
distinct contexts. With 10 uses, we get 2 repetitions, but they're
within the same role (both non-mover or both mover). HARMLESS.

The double loop is STRUCTURED to avoid EC: the two passes through each
processor are cleanly separated by a full sweep of all other processors,
ensuring maximum context differentiation.
""")

# Now: what about OTHER walk types? Back-and-forth, wiggle, etc.
print("\n--- Other walk types at n=5 ---")
n = 5
ms = [2, 2, 2, 3, 3]

# Generate various walks by sampling
print("\nSampling diverse walks that satisfy hfull + binary parity...")
good_walks = []
bp = [0, 1, 2]
for _ in range(100000):
    cl = random.choice([10, 12, 14])
    walk = [0]
    for _ in range(cl - 1):
        p = walk[-1]
        walk.append(random.choice([(p-1)%n, p, (p+1)%n]))

    fc = Counter(walk)
    if (len(fc) == n and
        all(fc[p] % 2 == 0 and fc[p] >= 2 for p in bp) and
        min(abs(walk[-1] - walk[0]), n - abs(walk[-1] - walk[0])) <= 1):
        good_walks.append(tuple(walk))

good_walks = list(set(good_walks))
print(f"Found {len(good_walks)} distinct valid walks")

# For each walk, build configs and check EC
ec_found = 0
no_ec_found = 0
for walk in good_walks[:200]:
    walk = list(walk)
    cl = len(walk)
    found_config = False
    found_ec = False

    for _ in range(100):
        config = [random.randrange(ms[p]) for p in range(n)]
        configs = [tuple(config)]
        seen = {tuple(config)}
        ok = True

        for step in range(cl - 1):
            mover = walk[step]
            old_val = config[mover]
            choices = [v for v in range(ms[mover]) if v != old_val]
            random.shuffle(choices)
            found = False
            for new_val in choices:
                config[mover] = new_val
                c = tuple(config)
                if c not in seen:
                    seen.add(c)
                    configs.append(c)
                    found = True
                    break
            if not found:
                ok = False
                break

        if not ok:
            continue

        mover = walk[cl - 1]
        needed = configs[0][mover]
        close_ok = True
        for p in range(n):
            if p != mover and config[p] != configs[0][p]:
                close_ok = False
                break
        if not close_ok or needed == config[mover]:
            continue

        found_config = True

        # Check EC
        has_ec = False
        for p in range(n):
            ctx_map = {}
            for i in range(cl):
                L = configs[i][(p-1)%n]
                S = configs[i][p]
                R = configs[i][(p+1)%n]
                ctx = (L, S, R)
                next_i = (i+1) % cl
                S_next = configs[next_i][p]
                output = S_next if walk[i] == p else S

                if ctx in ctx_map:
                    if ctx_map[ctx] != output:
                        has_ec = True
                        break
                else:
                    ctx_map[ctx] = output
            if has_ec:
                break

        if has_ec:
            found_ec = True
        else:
            no_ec_found += 1
            break

    if found_config and found_ec and not any(True for _ in []):
        ec_found += 1

print(f"\nWalks with no-EC config found: {no_ec_found}")
print(f"Walks where all tried configs had EC: {ec_found}")

# Part 2: The REAL question — non-double-loop walks
print("\n\n--- Non-sweep walk analysis ---")
print("""
The double loop is special: it's a SWEEP (visits processors in order).
The actual lower bound proof must handle ALL possible mover sequences.

Key walk types:
1. Sweep (double loop): [0,1,...,n-1,0,1,...,n-1] — avoids EC
2. Back-and-forth: [0,1,2,...,n-1,n-2,...,1,0,...] — palindromic
3. Wiggle: [0,1,0,1,2,1,2,3,...] — local oscillation
4. Mixed: arbitrary ring-adjacent sequence

The lower bound proof (from MEMORY) uses DIFFERENT mechanisms for each:
- Sweep → shadow cycle obstruction
- Non-sweep fc=2 → palindromic entry conflict
- Wiggle → wiggle shadow cycle

The entry conflict is NOT from pigeonhole on context space (which fails
for double loop as shown). It's from the SHADOW CYCLE structure:
a companion cycle that must also be valid, exhausting the config space.
""")

# Part 3: Context space at fc > 2
print("\n--- Part 3: What if fire counts are larger? ---")
print("""
The double loop has fc=2 for all processors. What about fc=4 (quadruple loop)?
""")

for n in [5, 7, 9]:
    ms = [2, 2, 2] + [3] * (n - 3)
    product = prod(ms)
    for fc_target in [2, 4, 6]:
        cl = fc_target * n
        if cl > product:
            continue
        # Context uses for proc 1 (binary, binary neighbors)
        ctx_space = 2 * 2 * 2  # = 8
        # Mover uses: fc_target
        # Non-mover uses: cl - fc_target
        # Total distinct contexts needed if no repetition: cl
        # But we only have 8 slots
        # Mover contexts: fc_target, each with S that alternates 0->1->0->1...
        # Non-mover contexts: cl - fc_target
        print(f"n={n}, fc={fc_target}, CL={cl}: "
              f"mover_uses={fc_target}, nonmover_uses={cl-fc_target}, ctx_space={ctx_space}, "
              f"ratio={cl/ctx_space:.1f}")

print("""
Even at fc=6, CL=30 at n=5: 30 context uses in 8 slots.
But the DOUBLE LOOP structure ensures mover and non-mover contexts are
separated by the S-value flip. So overlap is still avoided.

THE REAL KILLING ARGUMENT:
The impossibility doesn't come from context space exhaustion at a SINGLE
processor. It comes from the GLOBAL constraint: ALL processors must
simultaneously avoid EC, AND configs must be distinct, AND the product
of state sizes bounds the total number of configs.

The shadow cycle argument: for any good cycle of length CL, there exists
a "shadow" cycle of length 2n that must fit in the same product space.
The shadow cycle + original cycle together require 2*CL distinct configs,
which exceeds the product when product < 4*3^(n-2).
""")

# Part 4: Config space vs cycle length
print("\n--- Part 4: Config space budget ---")
print(f"{'n':>4} | {'ms':>20} | {'product':>10} | {'CL=2n':>8} | {'shadow_needs':>14} | {'fits':>6}")
print("-" * 75)
for n in [5, 7, 9, 11]:
    ms = [2, 2, 2] + [3] * (n - 3)
    product = prod(ms)
    cl = 2 * n
    shadow_len = 2 * n  # shadow cycle also length ~2n
    total_need = cl + shadow_len  # original + shadow need distinct configs
    ms_str = str(ms)[:20]
    fits = "YES" if total_need <= product else "NO"
    print(f"{n:4d} | {ms_str:>20} | {product:10d} | {cl:8d} | {total_need:14d} | {fits:>6}")

print("""
The shadow argument: CL + shadow_len = 4n distinct configs needed.
Product = 8 * 3^(n-3).

4n <= 8 * 3^(n-3)?
n=5: 20 <= 72. YES — shadow argument alone doesn't kill n=5.
n=7: 28 <= 648. YES — still room.

The shadow cycle argument works differently: it doesn't need 4n distinct
configs. It shows that the shadow cycle configs OVERLAP with the original
cycle configs in a way that FORCES entry conflict. The overlap is
structural (from the shadow cycle construction), not just a counting argument.
""")
