"""
Investigation part 2: For ZW+cw>0+fc>=2+fc>=3 mover words,
check EC across ALL possible transition tables at n=5.
"""

import itertools

def winding_number(mover_word, n):
    cw = 0; ccw = 0
    L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
        elif nxt == (curr - 1) % n: ccw += 1
        else: return None
    if (cw - ccw) % n != 0: return None
    return (cw - ccw) // n

def fire_counts(mover_word, n):
    fc = [0] * n
    for p in mover_word: fc[p] += 1
    return fc

def cw_count(mover_word, n):
    cw = 0; L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
    return cw

def enumerate_zw_mover_words(n, cl):
    def dfs(word, pos):
        if len(word) == cl:
            last = word[-1]; first = word[0]
            if (first - last) % n == 1 or (last - first) % n == 1:
                w = winding_number(word, n)
                if w == 0:
                    if cw_count(word, n) > 0:
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

n = 5
ms = (2, 2, 2, 3, 3)

print("Checking ZW+fc>=3 words at n=5, ms=(2,2,2,3,3)")
print("For each word, enumerate ALL valid good cycles and check EC")

cl = 12
print(f"\nCL={cl}:")

word_idx = 0
grand_cycles = 0
grand_ec = 0
grand_no_ec = 0

for word in enumerate_zw_mover_words(n, cl):
    fc = fire_counts(word, n)
    if any(f < 2 for f in fc): continue
    if max(fc) < 3: continue

    word_idx += 1
    if word_idx > 10: break

    L = len(word)
    cycles_found = 0
    ec_found = 0
    no_ec_found = 0

    def dfs_configs(step, configs, transitions):
        global cycles_found, ec_found, no_ec_found

        if step == L:
            if configs[0] != configs[L]: return
            config_tuples = [tuple(c) for c in configs[:L]]
            if len(set(config_tuples)) != L: return

            cycles_found += 1

            has_ec = False
            for i in range(n):
                mover_ctxs = set()
                nonmover_ctxs = set()
                for k in range(L):
                    c = configs[k]
                    ctx = (c[(i-1) % n], c[i], c[(i+1) % n])
                    if word[k] == i:
                        mover_ctxs.add(ctx)
                    else:
                        nonmover_ctxs.add(ctx)
                if mover_ctxs & nonmover_ctxs:
                    has_ec = True
                    break

            if has_ec: ec_found += 1
            else:
                no_ec_found += 1
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

    print(f"  Word {word_idx}: {word}, fc={fc}")
    print(f"    Cycles: {cycles_found}, EC: {ec_found}, No-EC: {no_ec_found}")

    grand_cycles += cycles_found
    grand_ec += ec_found
    grand_no_ec += no_ec_found

print(f"\nTotals (first 10 words): {grand_cycles} cycles, {grand_ec} EC, {grand_no_ec} no-EC")
