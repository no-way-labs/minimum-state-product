#!/usr/bin/env python3
"""
RA12 Part 9: WHY does the entry conflict arise for CL > 2n?

From Part 8: At step 2, proc 3 fires with context (0,0,1).
At step 10, proc 3 is non-mover with THE SAME context (0,0,1).
This forces f_3(0,0,1) = 1 (fires to 1) AND f_3(0,0,1) = 0 (stable).

The entry conflict happens because:
1. Proc 3 fires at step 2 with context (left=c[2], self=c[3], right=c[4]).
2. Later, proc 3 has the SAME context at a non-mover step.

The walk is: 0, 4, 3, 2, 1, 0, 1, 2, 3, 3, 4
The "back-and-forth" structure means the walker traverses the ring CW and CCW.
During the CW pass, proc 3 fires at step 2 with some context.
After the CCW pass + re-traversal, at step 10 the walker is at proc 4,
and proc 3's context has returned to its original value.

KEY INSIGHT: In a palindromic (back-and-forth) walk with fc=2,
the proc's context during the CW pass and CCW pass would be different
(because the mover is approaching from different directions).
But with fc=3 at the TERNARY proc, the extra firing creates a step
where the context matches a non-mover step.

The essential argument:
- In a ZW walk, the mover traverses CW and then CCW (or vice versa).
- After the full traversal, configs tend to "reverse" back.
- With fc=2 for all procs: contexts at the two firing steps differ.
- With fc≥3: extra firings create additional "visits" to a neighborhood,
  and one of these visits may see the same context as a non-mover step.

Let me verify this for ALL L>2n walks systematically.

The question: is the entry conflict UNIVERSAL for CL > 2n walks with
≥3 binary, ZW, fc≥2?

If yes: CL > 2n → entry conflict → False. So CL ≤ 2n.
The proof would be: if CL > 2n, then some proc has fc ≥ 3, and
entry conflict at that proc gives a contradiction.

But we need to show the entry conflict ALWAYS happens, not just in examples.
"""

from itertools import product as cprod
from collections import defaultdict, Counter

def get_value_at_step(p, step, fires, seq):
    count = sum(1 for s in fires if s < step)
    if count >= len(seq):
        return seq[0]
    return seq[count]

def generate_fire_sequences(m, fc):
    results = []
    def backtrack(seq):
        if len(seq) == fc + 1:
            if seq[-1] == seq[0]:
                results.append(tuple(seq[:-1]))
            return
        for v in range(m):
            if v != seq[-1]:
                backtrack(seq + [v])
    for v0 in range(m):
        backtrack([v0])
    return results

def enumerate_closed_walks(n, target_len, binary_positions, max_ternary_run=2):
    results = []
    def dfs(pos_seq, step_idx):
        if len(results) > 50000:
            return
        curr = pos_seq[-1]
        if step_idx == target_len:
            if curr != pos_seq[0]:
                return
            cw = sum(1 for i in range(target_len)
                     if (pos_seq[i+1] - pos_seq[i]) % n == 1)
            ccw = sum(1 for i in range(target_len)
                      if (pos_seq[i+1] - pos_seq[i]) % n == n-1)
            if cw != ccw:
                return
            fc = Counter(pos_seq[:-1])
            if any(fc[p] < 2 for p in range(n)):
                return
            results.append(list(pos_seq[:-1]))
            return
        for delta in [-1, 0, 1]:
            nxt = (curr + delta) % n
            new_seq = pos_seq + [nxt]
            run_len = 1
            for j in range(len(new_seq) - 2, -1, -1):
                if new_seq[j] == nxt:
                    run_len += 1
                else:
                    break
            if nxt in binary_positions and run_len > 1:
                continue
            if nxt not in binary_positions and run_len > max_ternary_run:
                continue
            if delta == 0 and curr in binary_positions:
                continue
            dfs(new_seq, step_idx + 1)
    dfs([0], 0)
    return results

def check_all_walks_for_ec(n, ms, binary_positions, max_len):
    """For each walk length, check if entry conflict is universal."""
    print(f"n={n}, ms={ms}, binary at {binary_positions}")
    print()

    for L in range(2*n, max_len + 1):
        walks = enumerate_closed_walks(n, L, binary_positions)
        if not walks:
            print(f"  L={L}: 0 walks")
            continue

        all_ec = True  # Do ALL distinct-config assignments have EC?
        total_distinct = 0
        total_consistent = 0
        total_ec = 0

        for walk in walks:
            fire_steps_map = {p: [] for p in range(n)}
            for i, p in enumerate(walk):
                fire_steps_map[p].append(i)

            proc_choices = []
            for p in range(n):
                fc_p = len(fire_steps_map[p])
                m = ms[p]
                if fc_p == 0:
                    proc_choices.append([(v,) for v in range(m)])
                else:
                    proc_choices.append(generate_fire_sequences(m, fc_p))

            total_combos = 1
            for ch in proc_choices:
                total_combos *= len(ch)
            if total_combos > 10000:
                continue

            for combo in cprod(*proc_choices):
                configs = []
                for i in range(L):
                    cfg = []
                    for p in range(n):
                        fc_p = len(fire_steps_map[p])
                        if fc_p == 0:
                            cfg.append(combo[p][0])
                        else:
                            val = get_value_at_step(p, i, fire_steps_map[p], combo[p])
                            cfg.append(val)
                    configs.append(tuple(cfg))

                if len(set(configs)) != L:
                    continue

                total_distinct += 1

                # Check transition consistency (no EC)
                constraints = defaultdict(set)
                has_ec = False
                for k in range(L):
                    c = configs[k]
                    c_next = configs[(k + 1) % L]
                    mover = walk[k]
                    for p in range(n):
                        left_val = c[(p - 1) % n]
                        self_val = c[p]
                        right_val = c[(p + 1) % n]
                        key = (p, left_val, self_val, right_val)
                        if p == mover:
                            constraints[key].add(c_next[p])
                        else:
                            constraints[key].add(self_val)

                for key, outputs in constraints.items():
                    if len(outputs) > 1:
                        has_ec = True
                        break

                if has_ec:
                    total_ec += 1
                else:
                    total_consistent += 1
                    all_ec = False

        ec_rate = total_ec / total_distinct * 100 if total_distinct > 0 else 0
        print(f"  L={L}: {len(walks)} walks, {total_distinct} distinct-config combos, "
              f"{total_ec} have EC ({ec_rate:.1f}%), {total_consistent} consistent")

        if not all_ec and total_consistent > 0:
            print(f"    *** CONSISTENT GOOD CYCLES EXIST AT L={L}! ***")

# Test n=5 with 3 binary
print("="*70)
print("TEST 1: n=5, ms=(2,2,2,3,3), binary at {0,1,2}")
print("="*70)
check_all_walks_for_ec(5, [2,2,2,3,3], {0,1,2}, 14)

# Test n=5 with non-consecutive binary
print()
print("="*70)
print("TEST 2: n=5, ms=(2,3,2,3,2), binary at {0,2,4}")
print("="*70)
check_all_walks_for_ec(5, [2,3,2,3,2], {0,2,4}, 14)

# Test n=5 with 4 binary
print()
print("="*70)
print("TEST 3: n=5, ms=(2,2,2,2,3), binary at {0,1,2,3}")
print("="*70)
check_all_walks_for_ec(5, [2,2,2,2,3], {0,1,2,3}, 14)

# Test n=6
print()
print("="*70)
print("TEST 4: n=6, ms=(2,2,2,3,3,3), binary at {0,1,2}")
print("="*70)
check_all_walks_for_ec(6, [2,2,2,3,3,3], {0,1,2}, 14)
