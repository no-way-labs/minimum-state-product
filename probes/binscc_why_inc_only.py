#!/usr/bin/env python3
"""binscc_why_inc_only.py — Why is incrementing the only valid assignment?

For overlap-free P1-free cycles at n=5 ms=(2,2,2,3,3):
- 4 valid transition combos per word (inc/dec for P3, inc/dec for P4)
- Only (inc,inc) produces distinct configs
- WHY do (inc,dec), (dec,inc), (dec,dec) create duplicates?

Find the structural reason. This is key to proving Case 3a analytically.
"""

from itertools import product as iproduct
import sys


def enumerate_mover_words_smart(ms, n, max_length):
    ring_adj = {}
    for p in range(n):
        ring_adj[p] = [(p-1) % n, (p+1) % n]
    results = []
    start_config = tuple(0 for _ in range(n))
    def dfs(word, fire_counts, current_config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and current_config == start_config:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0
                       for p in range(n))
            if fair:
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fire_counts[p]) for p in range(n)
                     if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            new_config = list(current_config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1
            word.append(nxt)
            dfs(word, new_counts, new_config)
            word.pop()
    for p in range(n):
        first = list(start_config)
        first[p] = (first[p] + 1) % ms[p]
        first = tuple(first)
        dfs([p], [1 if i == p else 0 for i in range(n)], first)
    return results


def main():
    n = 5
    ms = [2, 2, 2, 3, 3]

    print("=" * 70)
    print("WHY IS INCREMENTING THE ONLY VALID ASSIGNMENT?")
    print("=" * 70)

    max_len = 3 * n + 6
    words = enumerate_mover_words_smart(ms, n, max_len)

    # Find overlap-free P1-free cycles
    target_words = []
    for word in words:
        ell = len(word)
        configs = [tuple(0 for _ in range(n))]
        valid = True
        for i in range(ell):
            p = word[i]
            c = list(configs[-1])
            c[p] = (c[p] + 1) % ms[p]
            configs.append(tuple(c))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:ell])) != ell:
            continue
        fire_counts = [0] * n
        for p in word:
            fire_counts[p] += 1
        for p in range(n):
            if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
                valid = False
                break
        if not valid:
            continue
        for i in range(ell):
            p1 = word[i]
            p2 = word[(i+1) % ell]
            diff = abs(p1 - p2)
            if diff != 1 and diff != n - 1:
                valid = False
                break
        if not valid:
            continue

        # P1 overlap
        p1_mover = set()
        p1_nonmover = set()
        for i in range(ell):
            v = (configs[i][0], configs[i][1], configs[i][2])
            if word[i] == 1:
                p1_mover.add(v)
            else:
                p1_nonmover.add(v)
        if p1_mover & p1_nonmover:
            continue

        # Full overlap
        any_overlap = False
        for p in range(n):
            mover_ctx = set()
            nonmover_ctx = set()
            for i in range(ell):
                c = configs[i]
                ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
                if word[i] == p:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if mover_ctx & nonmover_ctx:
                any_overlap = True
                break
        if any_overlap:
            continue

        target_words.append((word, configs[:ell]))

    print(f"\n{len(target_words)} overlap-free P1-free cycles")

    # For each, try all 4 ternary assignments (inc/dec for P3, inc/dec for P4)
    for word_idx, (word, configs_inc) in enumerate(target_words[:6]):
        ell = len(word)

        # Find ternary firing steps and their current values
        p3_steps = [(i, configs_inc[i][3]) for i in range(ell) if word[i] == 3]
        p4_steps = [(i, configs_inc[i][4]) for i in range(ell) if word[i] == 4]

        print(f"\nCycle {word_idx}: {word}")
        print(f"  P3 fires at steps {[s for s,_ in p3_steps]} with values {[v for _,v in p3_steps]}")
        print(f"  P4 fires at steps {[s for s,_ in p4_steps]} with values {[v for _,v in p4_steps]}")

        for p3_mode, p4_mode in [('inc','inc'), ('inc','dec'), ('dec','inc'), ('dec','dec')]:
            # Build config sequence
            configs = [tuple(0 for _ in range(n))]
            for i in range(ell):
                p = word[i]
                c = list(configs[-1])
                if ms[p] == 2:
                    c[p] = 1 - c[p]
                elif p == 3:
                    current = c[p]
                    if p3_mode == 'inc':
                        c[p] = (current + 1) % 3
                    else:
                        c[p] = (current - 1) % 3
                elif p == 4:
                    current = c[p]
                    if p4_mode == 'inc':
                        c[p] = (current + 1) % 3
                    else:
                        c[p] = (current - 1) % 3
                configs.append(tuple(c))

            closes = configs[-1] == configs[0]
            distinct = len(set(configs[:ell])) == ell if closes else False

            if not closes:
                print(f"  ({p3_mode},{p4_mode}): doesn't close, final={configs[-1]}")
            elif not distinct:
                # Find the duplicate
                seen = {}
                dup_info = None
                for i in range(ell):
                    c = configs[i]
                    if c in seen:
                        dup_info = (seen[c], i, c)
                        break
                    seen[c] = i
                if dup_info:
                    j, k, c = dup_info
                    print(f"  ({p3_mode},{p4_mode}): duplicate at steps {j} and {k}: {c}")
                    # What's different between incrementing and this?
                    print(f"    inc configs[{j}] = {configs_inc[j]}")
                    print(f"    inc configs[{k}] = {configs_inc[k]}")
                    # Binary components
                    bin_j = configs[j][:3]
                    bin_k = configs[k][:3]
                    print(f"    binary: [{j}]={bin_j}, [{k}]={bin_k} (same={bin_j==bin_k})")
            else:
                print(f"  ({p3_mode},{p4_mode}): ★ VALID (closes, distinct)")

        # Detailed: why do the duplicates occur?
        # The binary components are the same regardless of ternary transitions.
        # If two steps have the same binary triple (c0,c1,c2), they can only
        # be distinguished by (c3,c4). With inc: all (c3,c4) pairs distinct.
        # With dec: some (c3,c4) pairs collide.

        # Count how many binary triples repeat
        bin_triples = [configs_inc[i][:3] for i in range(ell)]
        from collections import Counter
        bin_counts = Counter(bin_triples)
        repeats = {k: v for k, v in bin_counts.items() if v > 1}
        print(f"\n  Binary triple repeats: {repeats}")

        # For each repeated binary triple, show what (c3,c4) values appear
        for bt, count in sorted(repeats.items()):
            steps = [i for i in range(ell) if configs_inc[i][:3] == bt]
            inc_vals = [(configs_inc[i][3], configs_inc[i][4]) for i in steps]
            print(f"    binary={bt}: steps={steps}, inc (c3,c4)={inc_vals}")
            # With dec: same steps but different (c3,c4) values
            for p3_mode, p4_mode in [('dec','dec'), ('inc','dec'), ('dec','inc')]:
                configs_alt = [tuple(0 for _ in range(n))]
                for i in range(ell):
                    p = word[i]
                    c = list(configs_alt[-1])
                    if ms[p] == 2:
                        c[p] = 1 - c[p]
                    elif p == 3:
                        c[p] = (c[p] + 1) % 3 if p3_mode == 'inc' else (c[p] - 1) % 3
                    elif p == 4:
                        c[p] = (c[p] + 1) % 3 if p4_mode == 'inc' else (c[p] - 1) % 3
                    configs_alt.append(tuple(c))
                alt_vals = [(configs_alt[i][3], configs_alt[i][4]) for i in steps]
                collision = len(alt_vals) != len(set(alt_vals))
                print(f"    ({p3_mode},{p4_mode}) (c3,c4)={alt_vals} {'COLLISION!' if collision else 'ok'}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
