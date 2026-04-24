#!/usr/bin/env python3
"""
RA12: Context return mechanism — why fc≥3 forces entry conflict.

The mechanism:
1. In a ZW walk, binary procs fire exactly twice (fc=2), toggling back.
2. After the full CW+CCW traversal, binary values RETURN to original.
3. If a ternary proc fires 3 times (all distinct values, returns to original),
   its neighbors (which are binary or ternary with fc=2) also return.
4. So the ternary proc's context at step AFTER 3rd firing = context at 1st firing.
5. At 1st firing: proc fires. After 3rd firing: proc is NOT the mover.
6. Same context, different behavior → entry conflict.

VERIFY: Does this context return happen for ALL value assignments?
"""

from itertools import product as cprod
from collections import Counter

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

n = 5
ms = [2, 2, 2, 3, 3]
binary_positions = {0, 1, 2}

# Check ALL L=11 walks
walks_11 = enumerate_closed_walks(5, 11, binary_positions)
print(f"Total L=11 walks: {len(walks_11)}")

total_check = 0
total_ec_at_fc3 = 0
total_no_ec_at_fc3 = 0

for walk in walks_11:
    L = len(walk)
    fire_steps = {p: [] for p in range(n)}
    for i, p in enumerate(walk):
        fire_steps[p].append(i)

    # Find fc=3 proc
    fc3_proc = None
    for p in range(n):
        if len(fire_steps[p]) == 3:
            fc3_proc = p
            break
    if fc3_proc is None:
        continue

    q = fc3_proc
    proc_choices = []
    for p in range(n):
        fc_p = len(fire_steps[p])
        m = ms[p]
        if fc_p == 0:
            proc_choices.append([(v,) for v in range(m)])
        else:
            proc_choices.append(generate_fire_sequences(m, fc_p))

    for combo in cprod(*proc_choices):
        configs = []
        for i in range(L):
            cfg = []
            for p in range(n):
                fc_p = len(fire_steps[p])
                if fc_p == 0:
                    cfg.append(combo[p][0])
                else:
                    val = get_value_at_step(p, i, fire_steps[p], combo[p])
                    cfg.append(val)
            configs.append(tuple(cfg))

        if len(set(configs)) != L:
            continue

        total_check += 1

        # Check EC at the fc=3 proc specifically
        left_q = (q - 1) % n
        right_q = (q + 1) % n

        # Gather mover and non-mover contexts at q
        mover_contexts = {}  # context -> fire_output
        nonmover_contexts = {}  # context -> stable_output
        has_ec_at_q = False

        for k in range(L):
            c = configs[k]
            c_next = configs[(k + 1) % L]
            ctx = (c[left_q], c[q], c[right_q])

            if walk[k] == q:
                mover_contexts[ctx] = c_next[q]
            else:
                nonmover_contexts[ctx] = c[q]  # stable

            if ctx in mover_contexts and ctx in nonmover_contexts:
                if mover_contexts[ctx] != nonmover_contexts[ctx]:
                    has_ec_at_q = True

        if has_ec_at_q:
            total_ec_at_fc3 += 1
        else:
            total_no_ec_at_fc3 += 1
            if total_no_ec_at_fc3 <= 3:
                print(f"\nNO EC at fc=3 proc {q}!")
                print(f"  Walk: {walk}")
                print(f"  Combo: {combo}")
                for k in range(L):
                    c = configs[k]
                    ctx = (c[left_q], c[q], c[right_q])
                    role = "MOVER" if walk[k] == q else "nonmover"
                    print(f"  Step {k}: config={c}, mover={walk[k]}, q_ctx={ctx} [{role}]")

print(f"\nResults:")
print(f"  Total distinct-config assignments: {total_check}")
print(f"  EC at fc=3 proc: {total_ec_at_fc3} ({total_ec_at_fc3/total_check*100:.1f}%)")
print(f"  No EC at fc=3 proc: {total_no_ec_at_fc3}")
print()

# CRITICAL: Also check if EC happens at OTHER procs (not the fc=3 one)
# when there's no EC at the fc=3 proc.
if total_no_ec_at_fc3 > 0:
    print("Checking if EC happens at OTHER procs when not at fc=3 proc...")

    total_any_ec = 0
    for walk in walks_11:
        L = len(walk)
        fire_steps = {p: [] for p in range(n)}
        for i, p in enumerate(walk):
            fire_steps[p].append(i)

        q = None
        for p in range(n):
            if len(fire_steps[p]) == 3:
                q = p
                break
        if q is None:
            continue

        proc_choices = []
        for p in range(n):
            fc_p = len(fire_steps[p])
            m = ms[p]
            if fc_p == 0:
                proc_choices.append([(v,) for v in range(m)])
            else:
                proc_choices.append(generate_fire_sequences(m, fc_p))

        for combo in cprod(*proc_choices):
            configs = []
            for i in range(L):
                cfg = []
                for p in range(n):
                    fc_p = len(fire_steps[p])
                    if fc_p == 0:
                        cfg.append(combo[p][0])
                    else:
                        val = get_value_at_step(p, i, fire_steps[p], combo[p])
                        cfg.append(val)
                configs.append(tuple(cfg))

            if len(set(configs)) != L:
                continue

            # Check EC at fc=3 proc
            left_q = (q - 1) % n
            right_q = (q + 1) % n
            mover_ctxs = {}
            nonmover_ctxs = {}
            has_ec_q = False
            for k in range(L):
                c = configs[k]
                c_next = configs[(k + 1) % L]
                ctx = (c[left_q], c[q], c[right_q])
                if walk[k] == q:
                    mover_ctxs[ctx] = c_next[q]
                else:
                    nonmover_ctxs[ctx] = c[q]
                if ctx in mover_ctxs and ctx in nonmover_ctxs:
                    if mover_ctxs[ctx] != nonmover_ctxs[ctx]:
                        has_ec_q = True

            if not has_ec_q:
                # Check ALL procs for EC
                has_any_ec = False
                ec_at_proc = None
                for p_check in range(n):
                    lp = (p_check - 1) % n
                    rp = (p_check + 1) % n
                    mc = {}
                    nc = {}
                    for k in range(L):
                        c = configs[k]
                        c_next = configs[(k + 1) % L]
                        ctx = (c[lp], c[p_check], c[rp])
                        if walk[k] == p_check:
                            mc[ctx] = c_next[p_check]
                        else:
                            nc[ctx] = c[p_check]
                        if ctx in mc and ctx in nc and mc[ctx] != nc[ctx]:
                            has_any_ec = True
                            ec_at_proc = p_check
                            break
                    if has_any_ec:
                        break

                if has_any_ec:
                    total_any_ec += 1

    print(f"  Cases where no EC at fc=3 but EC at other proc: {total_any_ec}")
    print(f"  Cases with NO EC at ANY proc: {total_no_ec_at_fc3 - total_any_ec}")
