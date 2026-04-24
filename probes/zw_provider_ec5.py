"""
Investigation part 5: Deep mechanism analysis.

For the ZW+fc>=3 words that produce valid cycles at n=5,
analyze exactly WHERE the EC comes from.
"""

import itertools

def analyze_ec_mechanism(word, n, ms):
    """For a given word and ms, find all valid cycles and analyze EC location."""
    L = len(word)
    results = []

    def dfs_configs(step, configs, transitions):
        if step == L:
            if configs[0] != configs[L]: return
            config_tuples = [tuple(c) for c in configs[:L]]
            if len(set(config_tuples)) != L: return

            # Find EC
            for i in range(n):
                mover_ctxs = {}
                nonmover_ctxs = {}
                for k in range(L):
                    c = configs[k]
                    ctx = (c[(i-1) % n], c[i], c[(i+1) % n])
                    if word[k] == i:
                        mover_ctxs[ctx] = mover_ctxs.get(ctx, []) + [k]
                    else:
                        nonmover_ctxs[ctx] = nonmover_ctxs.get(ctx, []) + [k]
                overlap = set(mover_ctxs.keys()) & set(nonmover_ctxs.keys())
                if overlap:
                    for ctx in overlap:
                        is_binary = ms[i] == 2
                        results.append({
                            'proc': i,
                            'binary': is_binary,
                            'ctx': ctx,
                            'mover_steps': mover_ctxs[ctx],
                            'nonmover_steps': nonmover_ctxs[ctx],
                        })
                    break  # Just record first EC proc
            return

        p = word[step]
        c = configs[step]
        ctx = (c[(p-1) % n], c[p], c[(p+1) % n])
        key = (p, ctx[0], ctx[1], ctx[2])

        if key in transitions:
            new_val = transitions[key]
            if new_val == ctx[1]: return
            new_c = c[:]; new_c[p] = new_val
            configs.append(new_c)
            dfs_configs(step + 1, configs, transitions)
            configs.pop()
        else:
            for new_val in range(ms[p]):
                if new_val == ctx[1]: continue
                new_c = c[:]; new_c[p] = new_val
                configs.append(new_c)
                new_trans = dict(transitions)
                new_trans[key] = new_val
                dfs_configs(step + 1, configs, new_trans)
                configs.pop()

    all_configs_space = list(itertools.product(*[range(m) for m in ms]))
    for start in all_configs_space:
        dfs_configs(0, [list(start)], {})

    return results

# Focus on the words that have valid cycles
n = 5
ms = (2, 2, 2, 3, 3)

test_words = [
    (0, 1, 2, 3, 4, 0, 4, 3, 4, 3, 2, 1),  # fc=[2,2,2,3,3]
    (0, 1, 2, 3, 4, 3, 4, 0, 4, 3, 2, 1),  # fc=[2,2,2,3,3]
    (0, 1, 2, 3, 4, 3, 4, 3, 2, 1, 0, 4),  # fc=[2,2,2,3,3]
]

for word in test_words:
    fc = [0] * n
    for p in word: fc[p] += 1
    print(f"\nWord: {word}")
    print(f"FC: {fc}")

    results = analyze_ec_mechanism(word, n, ms)
    print(f"Found {len(results)} EC instances")

    # Summarize
    proc_counts = {}
    for r in results:
        p = r['proc']
        proc_counts[p] = proc_counts.get(p, 0) + 1

    print(f"EC at procs: {proc_counts}")
    for r in results[:3]:
        p = r['proc']
        print(f"  Proc {p} ({'binary' if r['binary'] else 'ternary'}, fc={fc[p]}): "
              f"ctx={r['ctx']}, mover@{r['mover_steps']}, nonmover@{r['nonmover_steps']}")

print("\n" + "="*60)
print("KEY: Which proc has EC? Binary or ternary? fc=2 or fc>=3?")
print("="*60)

# Now let's check ALL CL=12 words more carefully
from collections import Counter

def winding_number(mover_word, n):
    cw = 0; ccw = 0; L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]; nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
        elif nxt == (curr - 1) % n: ccw += 1
        else: return None
    if (cw - ccw) % n != 0: return None
    return (cw - ccw) // n

def cw_count(mover_word, n):
    cw = 0; L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]; nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
    return cw

def enumerate_zw_mover_words(n, cl):
    def dfs(word, pos):
        if len(word) == cl:
            last = word[-1]; first = word[0]
            if (first - last) % n == 1 or (last - first) % n == 1:
                w = winding_number(word, n)
                if w == 0 and cw_count(word, n) > 0:
                    yield tuple(word)
            return
        for nxt in [(pos + 1) % n, (pos - 1) % n]:
            word.append(nxt)
            yield from dfs(word, nxt)
            word.pop()
    seen = set()
    for start in range(n):
        for word in dfs([start], start):
            rotations = [word[i:] + word[:i] for i in range(cl)]
            canonical = min(rotations)
            if canonical not in seen:
                seen.add(canonical)
                yield canonical

print("\n" + "="*60)
print("Exhaustive analysis: ALL CL=12 ZW+fc>=3 words with valid cycles")
print("="*60)

ec_at_binary_count = 0
ec_at_ternary_count = 0
ec_at_fc2_count = 0
ec_at_fc3_count = 0
total_with_cycles = 0

for word in enumerate_zw_mover_words(n, 12):
    fc_list = [0] * n
    for p in word: fc_list[p] += 1
    if any(f < 2 for f in fc_list): continue
    if max(fc_list) < 3: continue

    results = analyze_ec_mechanism(word, n, ms)
    if not results: continue

    total_with_cycles += 1
    for r in results:
        p = r['proc']
        if r['binary']:
            ec_at_binary_count += 1
        else:
            ec_at_ternary_count += 1
        if fc_list[p] == 2:
            ec_at_fc2_count += 1
        else:
            ec_at_fc3_count += 1

print(f"\nWords with valid cycles: {total_with_cycles}")
print(f"EC at binary proc: {ec_at_binary_count}")
print(f"EC at ternary proc: {ec_at_ternary_count}")
print(f"EC at fc=2 proc: {ec_at_fc2_count}")
print(f"EC at fc>=3 proc: {ec_at_fc3_count}")
