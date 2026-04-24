"""
Investigation part 8: Precise mechanism analysis.

For each valid ZW+fc>=3 cycle at n=5, find the exact EC witness
and characterize the mechanism.

The conjectured mechanism:
  1. Find binary b with fc = 2
  2. b fires at steps a1 and a2 (consecutive)
  3. Between a1 and a2, b doesn't fire → b's value is preserved
  4. At a2, context is (L_a2, S_a2, R_a2)
  5. There exists k in (a1, a2) where b is non-mover with same (L,S,R)

Why does step 5 hold? Because:
  - S_k = S_a2 (b doesn't fire, binary so 0 interval fires = even → preserved)
  - For L and R: the walk between a1 and a2 passes through b's position twice
    (going and coming back). At some intermediate step k, the neighbors happen
    to have returned to the same values.

Let me extract the exact witnesses.
"""

import itertools

def fire_counts(word, n):
    fc = [0] * n
    for p in word: fc[p] += 1
    return fc

def winding_number(word, n):
    cw = 0; ccw = 0; L = len(word)
    for i in range(L):
        curr = word[i]; nxt = word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
        elif nxt == (curr - 1) % n: ccw += 1
        else: return None
    if (cw - ccw) % n != 0: return None
    return (cw - ccw) // n

def cw_count(word, n):
    cw = 0; L = len(word)
    for i in range(L):
        curr = word[i]; nxt = word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
    return cw

def enumerate_zw_words(n, cl):
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

n = 5
ms = (2, 2, 2, 3, 3)
binary_set = {0, 1, 2}

print("Detailed EC witness analysis for ZW+fc>=3 cycles at n=5")
print("=" * 70)

# Take the first word with valid cycles
word = (0, 1, 2, 3, 4, 0, 4, 3, 4, 3, 2, 1)
fc = fire_counts(word, n)
print(f"\nWord: {word}")
print(f"FC: {fc}")
print(f"Binary procs with fc=2: {[p for p in range(n) if ms[p] == 2 and fc[p] == 2]}")

L = len(word)

# Find the first valid cycle and analyze it in detail
found = [False]
detail_count = [0]

def dfs_detail(step, configs, transitions):
    if found[0]: return
    if step == L:
        if configs[0] != configs[L]: return
        config_tuples = [tuple(c) for c in configs[:L]]
        if len(set(config_tuples)) != L: return

        detail_count[0] += 1
        if detail_count[0] > 3: return

        print(f"\n--- Valid cycle #{detail_count[0]} ---")
        print(f"Start config: {tuple(configs[0])}")

        # Show full config sequence
        for k in range(L):
            p = word[k]
            ctx = (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n])
            nxt_val = configs[k+1][p]
            print(f"  Step {k:2d}: mover={p}, ctx=(L={ctx[0]},S={ctx[1]},R={ctx[2]})"
                  f" → S'={nxt_val}  config={tuple(configs[k])}")

        # Find EC
        for i in range(n):
            mover_ctxs = {}
            nonmover_ctxs = {}
            for k in range(L):
                c = configs[k]
                ctx = (c[(i-1) % n], c[i], c[(i+1) % n])
                if word[k] == i:
                    mover_ctxs.setdefault(ctx, []).append(k)
                else:
                    nonmover_ctxs.setdefault(ctx, []).append(k)
            overlap = set(mover_ctxs.keys()) & set(nonmover_ctxs.keys())
            if overlap:
                for ctx in overlap:
                    print(f"\n  EC at proc {i} (m={ms[i]}, fc={fc[i]}): ctx={ctx}")
                    print(f"    Mover steps: {mover_ctxs[ctx]}")
                    print(f"    Non-mover steps: {nonmover_ctxs[ctx]}")

                    # Analyze: which steps are between consecutive fires of i?
                    fire_steps = [k for k in range(L) if word[k] == i]
                    nonfire_steps = nonmover_ctxs[ctx]
                    for nf in nonfire_steps:
                        # Which fire pair brackets this non-fire step?
                        for fi in range(len(fire_steps)):
                            a1 = fire_steps[fi]
                            a2 = fire_steps[(fi + 1) % len(fire_steps)]
                            if a1 < a2:
                                if a1 < nf < a2:
                                    print(f"    Step {nf} is between fire steps {a1} and {a2}")
                            elif a2 < a1:
                                if nf > a1 or nf < a2:
                                    print(f"    Step {nf} is between fire steps {a1} and {a2} (wrap)")
                break
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
        dfs_detail(step + 1, configs, transitions)
        configs.pop()
    else:
        for new_val in range(ms[p]):
            if new_val == ctx[1]: continue
            new_c = c[:]; new_c[p] = new_val
            configs.append(new_c)
            new_trans = dict(transitions)
            new_trans[key] = new_val
            dfs_detail(step + 1, configs, new_trans)
            configs.pop()

# Just try a few starting configs
for start in itertools.product(*[range(m) for m in ms]):
    if detail_count[0] >= 3: break
    dfs_detail(0, [list(start)], {})

print("\n" + "="*70)
print("MECHANISM SUMMARY")
print("="*70)
print()
print("The EC witness structure:")
print("- Binary proc b with fc=2 fires at steps a1 and a2")
print("- Between a1 and a2, b is a non-mover at every step")
print("- b's value S is preserved (0 fires = even → binary state returns)")
print("- At mover step a2, b sees context (L, S, R)")
print("- At some non-mover step k in (a1, a2), b sees same (L, S, R)")
print("- WHY L and R match: neighbors fire even times (or don't fire) in [k, a2)")
print()
print("This is exactly palindromic_step_pair_caseA from ZeroWinding.lean!")
print("The sorry just needs to show that such b and k EXIST.")
