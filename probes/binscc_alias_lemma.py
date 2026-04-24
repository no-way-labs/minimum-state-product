#!/usr/bin/env python3
"""binscc_alias_lemma.py — The Alias Lemma approach to universal entry conflict.

KEY IDEA: For binary proc b, mover context (L,s,R) determines a set of
"alias configs" — all configs c with c[b-1]=L, c[b]=s, c[b+1]=R.
Size of alias set = prod_{i not in {b-1,b,b+1}} m_i.

If the good cycle contains ≥2 configs from the alias set:
  - At most 1 is the mover step
  - The rest are nonmover steps with same context
  → ENTRY CONFLICT at b.

So: if for EVERY binary b, at least one of UP/DOWN mover contexts has
≥2 cycle configs in its alias set → conflict.

CHECK: How often does this alias mechanism explain the conflict?
"""

import sys
from collections import Counter, defaultdict
import time
from math import prod


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
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


def main():
    print("=" * 70)
    print("ALIAS LEMMA: MOVER CONTEXT ALIAS COUNTING")
    print("=" * 70)

    configs = [
        (5, [2, 3, 2, 3, 2], 21),
        (6, [2, 3, 2, 3, 2, 3], 24),
    ]

    for n, ms, max_len in configs:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms}")
        bin_procs = [i for i in range(n) if ms[i] == 2]
        product = 1
        for m in ms:
            product *= m
        print(f"  Binary procs: {bin_procs}, product={product}")

        # Compute alias set sizes for each binary
        for b in bin_procs:
            mL = (b-1) % n
            mR = (b+1) % n
            rest = [i for i in range(n) if i not in {mL, b, mR}]
            n_rest = 1
            for i in rest:
                n_rest *= ms[i]
            ctx_space = ms[mL] * ms[b] * ms[mR]
            print(f"  P{b}: ctx_space={ctx_space}, "
                  f"alias_size={n_rest} (rest procs: {rest})")

        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} words ({t1-t0:.1f}s)")

        total = 0
        alias_conflict = 0      # conflict via ≥2 aliases
        non_alias_conflict = 0   # conflict but max 1 alias per mover ctx
        no_conflict = 0

        # Track alias counts
        alias_count_dist = Counter()  # max alias count across all mover ctxs

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1
            ell = len(cycle)
            config_set = set(cycle)

            found_alias = False
            found_conflict = False
            max_alias = 0

            for b in bin_procs:
                mL = (b-1) % n
                mR = (b+1) % n
                rest = [i for i in range(n) if i not in {mL, b, mR}]

                # Find mover contexts at b
                mover_ctxs = set()
                nonmover_ctxs = set()
                for step in range(ell):
                    c = cycle[step]
                    ctx = (c[mL], c[b], c[mR])
                    if word[step] == b:
                        mover_ctxs.add(ctx)
                    else:
                        nonmover_ctxs.add(ctx)

                if mover_ctxs & nonmover_ctxs:
                    found_conflict = True

                # For each mover context: count how many cycle configs
                # share that context at b
                for ctx in mover_ctxs:
                    L, S, R = ctx
                    # Count configs in cycle with this context
                    alias_count = sum(1 for c in cycle
                                      if c[mL] == L and c[b] == S
                                      and c[mR] == R)
                    if alias_count >= 2:
                        found_alias = True
                    max_alias = max(max_alias, alias_count)

            alias_count_dist[max_alias] += 1

            if found_alias:
                alias_conflict += 1
            elif found_conflict:
                non_alias_conflict += 1
            else:
                no_conflict += 1

        elapsed = time.time() - t0
        print(f"\n  Total valid: {total} ({elapsed:.1f}s)")
        print(f"  Alias conflict (≥2 aliases): "
              f"{alias_conflict}/{total} ({100*alias_conflict/total:.1f}%)")
        print(f"  Non-alias conflict: "
              f"{non_alias_conflict}/{total} ({100*non_alias_conflict/total:.1f}%)")
        print(f"  No conflict: {no_conflict}/{total}")
        print(f"  Max alias count distribution: "
              f"{dict(sorted(alias_count_dist.items()))}")

        # Now check: for cycles WITH alias conflict, which binary has it?
        if total > 0:
            per_b_alias = {b: 0 for b in bin_procs}
            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                for b in bin_procs:
                    mL = (b-1) % n
                    mR = (b+1) % n
                    for step in range(len(cycle)):
                        if word[step] == b:
                            c = cycle[step]
                            L, S, R = c[mL], c[b], c[mR]
                            cnt = sum(1 for cc in cycle
                                      if cc[mL] == L and cc[b] == S
                                      and cc[mR] == R)
                            if cnt >= 2:
                                per_b_alias[b] += 1
                                break
            print(f"  Per-binary alias count: {per_b_alias}")

    # PART 2: For non-alias conflicts, what's happening?
    print(f"\n\n{'='*70}")
    print("PART 2: NON-ALIAS CONFLICTS (each mover ctx unique in cycle)")
    print("=" * 70)
    print()
    print("If max alias = 1 for all mover ctxs, conflict comes from a")
    print("DIFFERENT config having the same context at b.")
    print("This means: two different steps with same (L,S,R) at b,")
    print("one mover and one nonmover, but from DIFFERENT configs.")
    print()
    print("Wait — that's still an alias! Different configs, same context.")
    print("Let me recheck...")
    print()

    # Actually: if two configs have same (L,S,R) at b, they ARE aliases.
    # So alias count ≥ 2 ↔ entry conflict. These SHOULD be identical.

    n, ms = 5, [2, 3, 2, 3, 2]
    words = enumerate_mover_words(ms, n, 21)

    mismatch = 0
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for b in [0, 2, 4]:
            mL = (b-1) % n
            mR = (b+1) % n
            mover_ctxs = set()
            nonmover_ctxs = set()
            for step in range(ell):
                c = cycle[step]
                ctx = (c[mL], c[b], c[mR])
                if word[step] == b:
                    mover_ctxs.add(ctx)
                else:
                    nonmover_ctxs.add(ctx)

            has_conflict = bool(mover_ctxs & nonmover_ctxs)

            # Check alias
            has_alias = False
            for ctx in mover_ctxs:
                L, S, R = ctx
                cnt = sum(1 for c in cycle
                          if c[mL] == L and c[b] == S and c[mR] == R)
                if cnt >= 2:
                    has_alias = True
                    break

            if has_conflict != has_alias:
                mismatch += 1

    print(f"  Mismatch between alias≥2 and entry conflict at proc: "
          f"{mismatch}")
    if mismatch == 0:
        print(f"  ★ PERFECT MATCH: alias≥2 ↔ entry conflict (per proc)")
        print()
        print("  This means: entry conflict at proc b ↔ ")
        print("  cycle contains ≥2 configs with same (L,S,R) at b")
        print("  where one is mover and at least one is nonmover.")
        print()
        print("  Equivalently: the mover config's context at b has")
        print("  an 'alias' (different config, same local context)")
        print("  that also appears in the cycle.")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
