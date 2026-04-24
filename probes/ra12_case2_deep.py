#!/usr/bin/env python3
"""RA12 Part 2: Deep investigation of Case 2 failures.

Key finding from Part 1: At n=7, 3840/5808 instances have NO EC at q.
But the proof doesn't require EC at q -- it requires EC at SOME processor.

Questions:
1. For Case 2 instances where q has no EC: does some OTHER processor have EC?
2. What is the exact structure of Case 2? Why (a1,b1)=(1,1), (a2,b2)=(0,0)?
3. Trace the detailed step-by-step context evolution for Case 2 instances.
4. Check whether the (1,1) phase assumption is correctly detected.
"""

from collections import Counter

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results

def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def has_ec_at_proc(word, cycle, ms, n, p):
    """Check if processor p has entry conflict."""
    ell = len(word)
    pL = (p - 1) % n
    pR = (p + 1) % n
    mover_ctx = set()
    nonmover_ctx = set()
    for s in range(ell):
        ctx = (cycle[s][pL], cycle[s][p], cycle[s][pR])
        if word[s] == p:
            mover_ctx.add(ctx)
        else:
            nonmover_ctx.add(ctx)
    return bool(mover_ctx & nonmover_ctx)

def has_ec_any(word, cycle, ms, n):
    """Check if ANY processor has entry conflict."""
    for p in range(n):
        if has_ec_at_proc(word, cycle, ms, n, p):
            return True
    return False

def ec_procs(word, cycle, ms, n):
    """Return set of processors with EC."""
    return {p for p in range(n) if has_ec_at_proc(word, cycle, ms, n, p)}

# ===== ANALYSIS FOR n=7 =====
print("=" * 70)
print("RA12 DEEP: Case 2 failure analysis")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
all_bin_ctx = [q for q in range(n)
               if ms[q] == 2 and ms[(q-1)%n] == 2 and ms[(q+1)%n] == 2]
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

print(f"n={n}, ms={ms}")
print(f"All-binary-context procs: {all_bin_ctx}")
print(f"Sandwiched ternary procs: {sandwiched}")

case2_no_ec_at_q = []
case2_with_ec_at_q = []
all_case1 = []
total_instances = 0
cycles_no_ec_anywhere = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    # Check (1,1) phase
    has_11 = False
    for t in sandwiched:
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]
            if len(t_mover) == 1 and len(t_nonmover) >= 1:
                has_11 = True
                break
        if has_11:
            break
    if not has_11:
        continue

    for q in all_bin_ctx:
        if fc[q] != 2:
            continue
        total_instances += 1

        qL = (q - 1) % n
        qR = (q + 1) % n
        q_steps = [s for s in range(ell) if word[s] == q]
        s1, s2 = q_steps

        a1, v1, b1 = cycle[s1][qL], cycle[s1][q], cycle[s1][qR]
        a2, v2, b2 = cycle[s2][qL], cycle[s2][q], cycle[s2][qR]

        is_case2 = (a1, b1) != (a2, b2)
        has_ec_q = has_ec_at_proc(word, cycle, ms, n, q)
        global_ec = has_ec_any(word, cycle, ms, n)
        ep = ec_procs(word, cycle, ms, n)

        if is_case2 and not has_ec_q:
            case2_no_ec_at_q.append((word, q, s1, s2,
                                     (a1,v1,b1), (a2,v2,b2),
                                     global_ec, ep))
            if not global_ec:
                cycles_no_ec_anywhere.append((word, q))
        elif is_case2 and has_ec_q:
            case2_with_ec_at_q.append((word, q))
        elif not is_case2:
            all_case1.append((word, q))

print(f"\nTotal instances: {total_instances}")
print(f"Case 1: {len(all_case1)}")
print(f"Case 2 with EC at q: {len(case2_with_ec_at_q)}")
print(f"Case 2 WITHOUT EC at q: {len(case2_no_ec_at_q)}")
print(f"Case 2 no EC at q but EC somewhere: {sum(1 for x in case2_no_ec_at_q if x[6])}")
print(f"Case 2 no EC ANYWHERE: {len(cycles_no_ec_anywhere)}")

# Show where EC exists for Case 2 instances
if case2_no_ec_at_q:
    ec_elsewhere_dist = Counter()
    for _, q, _, _, _, _, has_global, ep in case2_no_ec_at_q:
        for p in ep:
            ec_elsewhere_dist[p] += 1

    print(f"\nFor Case 2 no-EC-at-q instances ({len(case2_no_ec_at_q)}):")
    print(f"  EC at other processors: {dict(sorted(ec_elsewhere_dist.items()))}")

    # Show detailed examples
    print(f"\n  Detailed examples (first 5):")
    for word, q, s1, s2, ctx1, ctx2, has_global, ep in case2_no_ec_at_q[:5]:
        ell = len(word)
        cycle = build_cycle(ms, n, word)
        print(f"\n  word_len={ell}, q={q}, s1={s1}, s2={s2}")
        print(f"    ctx at s1: {ctx1}")
        print(f"    ctx at s2: {ctx2}")
        print(f"    EC procs: {ep}")
        print(f"    fc: {dict(Counter(word))}")

        # Full context trace at q
        qL, qR = (q-1)%n, (q+1)%n
        print(f"    Step-by-step q context:")
        for s in range(ell):
            ctx = (cycle[s][qL], cycle[s][q], cycle[s][qR])
            mover_str = f"M={word[s]}" + (" <-- q fires!" if word[s] == q else "")
            print(f"      s={s:2d}: ctx={ctx}  {mover_str}")

print("\n" + "=" * 70)
print("CRITICAL CHECK: Do ALL valid cycles have EC at SOME processor?")
print("=" * 70)

all_cycles_checked = 0
no_ec_list = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    all_cycles_checked += 1
    if not has_ec_any(word, cycle, ms, n):
        no_ec_list.append(word)

print(f"Total cycles: {all_cycles_checked}")
print(f"Cycles with EC at some proc: {all_cycles_checked - len(no_ec_list)}")
print(f"Cycles with NO EC at any proc: {len(no_ec_list)}")

if no_ec_list:
    print(f"\nWARNING: {len(no_ec_list)} cycles have no EC anywhere!")
    for word in no_ec_list[:3]:
        print(f"  word={word}")
        fc = Counter(word)
        print(f"  fc={dict(fc)}")
else:
    print("  *** ALL cycles have EC at some processor ***")

# ===== Check: What LR pairs appear in Case 2? =====
print("\n" + "=" * 70)
print("Case 2 LR pair analysis")
print("=" * 70)

pair_counts = Counter()
for word, q, s1, s2, ctx1, ctx2, _, _ in case2_no_ec_at_q:
    pair_counts[((ctx1[0], ctx1[2]), (ctx2[0], ctx2[2]))] += 1

print("LR pair combinations in Case 2 (no EC at q):")
for pair, cnt in sorted(pair_counts.items(), key=lambda x: -x[1]):
    print(f"  (a1,b1)={pair[0]}, (a2,b2)={pair[1]}: {cnt}")

# ===== LAST-3-STEPS ANALYSIS =====
print("\n" + "=" * 70)
print("Last 3 steps before q fires (ring walk constraint)")
print("=" * 70)

last3_patterns = Counter()
for word, q, s1, s2, ctx1, ctx2, _, _ in case2_no_ec_at_q:
    ell = len(word)
    qL, qR = (q-1)%n, (q+1)%n
    # Last 3 steps before s1
    sm2 = (s1 - 2) % ell
    sm1 = (s1 - 1) % ell
    pattern = (word[sm2], word[sm1], word[s1])
    # Classify relative to q
    rel_pattern = []
    for p in [word[sm2], word[sm1], word[s1]]:
        if p == q:
            rel_pattern.append('q')
        elif p == qL:
            rel_pattern.append('qL')
        elif p == qR:
            rel_pattern.append('qR')
        else:
            rel_pattern.append(f'{p}')
    last3_patterns[tuple(rel_pattern)] += 1

print("Relative patterns (s1-2, s1-1, s1):")
for pat, cnt in sorted(last3_patterns.items(), key=lambda x: -x[1]):
    print(f"  {pat}: {cnt}")
