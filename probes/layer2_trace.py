#!/usr/bin/env python3
"""
Trace the phase-length EC argument in detail.

For a sandwiched ternary t with both binary neighbors:
Phase = interval (a, s] where step a is the previous t-fire, step s is this t-fire.
Interior steps = a+1, a+2, ..., s-1.

NormalForm + tight => exactly one binary neighbor fires, at step a+1.
No second-neighbor fires in the phase (from the tight argument in AllNormalFormFalse2).

If phase length > 2 (step a+2 exists):
  Between step a+1 (binary fire) and step s (t-fire):
  - bL doesn't fire again (J=1 for left, 0 for right; or J=0, K=1)
  - bR doesn't fire again
  - t doesn't fire (by phase definition)
  So c[bL], c[t], c[bR] are all constant from step a+2 to step s.
  => boundary triple at t is the same at steps a+2 and s.
  step s: t-mover. step a+2: not t-mover.
  => EC at t.

BUT WAIT: does step a+2 necessarily have word[a+2] != t?
YES: t only fires at step s within this phase.

The question: is the "tight" constraint (binary fires at step a+1) actually correct?
Let me re-read the AllNormalFormFalse2 proof structure.

The tight constraint comes from within_phase_ec_left/right:
IF second-neighbor doesn't fire in the phase AND first-neighbor fires after step a+1,
THEN EC.
So "not tight" + "no second-neighbor" => EC.
Contrapositive: no EC => either tight or second-neighbor fires.

So the FULL phase structure is:
Case A: second-neighbor fires in the phase (LL or RR fires).
Case B: second-neighbor doesn't fire, binary fires at step a+1 (tight).

The proof needs to handle BOTH cases. Let me focus on what the data shows.
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


def is_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True


# Examine the ALL-normalForm cycles and check if the argument applies
n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

print(f"n={n}, ms={ms}, sandwiched={sandwiched}")

words = enumerate_mover_words(ms, n, max_len)
print(f"Total mover words: {len(words)}")

# Find an all-normalForm cycle at a sandwiched t and trace in detail
count = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    for t in sandwiched:
        ell = len(word)
        bL = (t - 1) % n
        bR = (t + 1) % n
        LL = (t - 2) % n
        RR = (t + 2) % n

        t_fires = [i for i in range(ell) if word[i] == t]
        if not t_fires:
            continue

        all_nf = True
        phases_data = []
        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                interior = list(range(a + 1, s))
            else:
                interior = list(range(a + 1, ell)) + list(range(0, s))
            J = sum(1 for st in interior if word[st] == bL)
            K = sum(1 for st in interior if word[st] == bR)
            if not is_normal_form(J, K):
                all_nf = False
                break

            # Check what fires in interior
            fires = Counter(word[st] for st in interior)
            # Check if LL or RR fires
            ll_fires = fires.get(LL, 0)
            rr_fires = fires.get(RR, 0)

            # Check if binary fire is tight (at step a+1)
            first_step = interior[0] if interior else None
            tight = first_step is not None and (word[first_step] == bL or word[first_step] == bR)

            phases_data.append({
                'a': a, 's': s, 'J': J, 'K': K,
                'len': len(interior) + 1,
                'interior_fires': dict(fires),
                'LL_fires': ll_fires, 'RR_fires': rr_fires,
                'tight': tight,
                'first_mover': word[first_step] if first_step is not None else None,
            })

        if not all_nf:
            continue

        count += 1
        if count <= 3:
            print(f"\n--- Cycle {count} at t={t} ---")
            print(f"  word = {word}")
            print(f"  len = {ell}")
            print(f"  bL={bL}, bR={bR}, LL={LL}, RR={RR}")
            fc = Counter(word)
            print(f"  fire counts: {dict(fc)}")
            for idx, ph in enumerate(phases_data):
                print(f"  Phase {idx}: a={ph['a']}, s={ph['s']}, J={ph['J']}, K={ph['K']}, "
                      f"len={ph['len']}, tight={ph['tight']}, first={ph['first_mover']}")
                print(f"    Interior fires: {ph['interior_fires']}")
                print(f"    LL fires: {ph['LL_fires']}, RR fires: {ph['RR_fires']}")

            # Check EC at t
            for sv in range(ms[t]):
                mover = set()
                nonmover = set()
                for i in range(ell):
                    if cycle[i][t] == sv:
                        lr = (cycle[i][bL], cycle[i][bR])
                        if word[i] == t:
                            mover.add(lr)
                        else:
                            nonmover.add(lr)
                overlap = mover & nonmover
                if overlap:
                    print(f"  EC at t={t}, S={sv}: mover {mover} & nonmover {nonmover} = {overlap}")

print(f"\nTotal all-normalForm instances: {count}")
