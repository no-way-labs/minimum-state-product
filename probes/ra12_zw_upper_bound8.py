#!/usr/bin/env python3
"""
RA12 Part 8: WHY are L>2n good cycles transition-inconsistent?

From Part 7: 0 out of 49 L=11 walks and 0 out of 208 L=12 walks have
transition-consistent value assignments. Let's understand the contradiction.

The key is: when a ternary proc fires 3 times (fc=3), it creates a
transition function contradiction. Let me trace through.
"""

from itertools import product as cprod
from collections import defaultdict

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

def analyze_contradiction(n, ms, walk, configs):
    """Find and explain the transition contradiction."""
    L = len(walk)
    constraints = defaultdict(set)

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
                output = c_next[p]
                constraints[key].add(('FIRE', output, k))
            else:
                constraints[key].add(('STABLE', self_val, k))

    for key, entries in constraints.items():
        outputs = set()
        details = []
        for entry_type, output, step in entries:
            outputs.add(output)
            details.append((entry_type, output, step))
        if len(outputs) > 1:
            p, l, s, r = key
            print(f"  CONTRADICTION at proc {p}, context ({l},{s},{r}):")
            for entry_type, output, step in sorted(details, key=lambda x: x[2]):
                print(f"    Step {step}: {entry_type} → {output}")
            return key, details
    return None, None

n = 5
ms = [2, 2, 2, 3, 3]

# Take the first L=11 walk and trace the contradiction
walk = [0, 4, 3, 2, 1, 0, 1, 2, 3, 3, 4]
L = len(walk)

fire_steps = {p: [] for p in range(n)}
for i, p in enumerate(walk):
    fire_steps[p].append(i)

print("="*70)
print(f"Walk: {walk}")
print(f"Movers: {' '.join(str(walk[i]) for i in range(L))}")
print()

# Show the walk structure
for i in range(L):
    nxt = (i + 1) % L
    diff = (walk[nxt] - walk[i]) % n
    if diff == 1:
        direction = "CW"
    elif diff == n - 1:
        direction = "CCW"
    elif diff == 0:
        direction = "STAY"
    else:
        direction = f"JUMP({diff})"
    print(f"  Step {i}: mover={walk[i]} → mover={walk[nxt]} [{direction}]")

print()
print("Fire counts:", [len(fire_steps[p]) for p in range(n)])
print("Proc 3 fires at steps:", fire_steps[3], "(fc=3, ternary)")
print()

# Try the first value assignment that gives distinct configs
proc_choices = []
for p in range(n):
    fc_p = len(fire_steps[p])
    m = ms[p]
    if fc_p == 0:
        proc_choices.append([(v,) for v in range(m)])
    else:
        proc_choices.append(generate_fire_sequences(m, fc_p))

print("="*70)
print("Analyzing ALL value assignments")
print("="*70)

contradiction_types = defaultdict(int)

for combo_idx, combo in enumerate(cprod(*proc_choices)):
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

    # Find contradiction
    constraints = defaultdict(list)
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
                constraints[key].append(('FIRE', c_next[p], k))
            else:
                constraints[key].append(('STABLE', self_val, k))

    for key, entries in constraints.items():
        outputs = set(e[1] for e in entries)
        types = set(e[0] for e in entries)
        if len(outputs) > 1:
            p = key[0]
            if 'FIRE' in types and 'STABLE' in types:
                contradiction_types[f'proc{p}_fire_vs_stable'] += 1
            elif 'FIRE' in types:
                contradiction_types[f'proc{p}_fire_vs_fire'] += 1
            else:
                contradiction_types[f'proc{p}_stable_vs_stable'] += 1

            if combo_idx == 0 or (combo_idx < 5 and contradiction_types[f'proc{p}_fire_vs_stable'] <= 2):
                print(f"\nCombo {combo_idx}: {combo}")
                print(f"Configs:")
                for i, c in enumerate(configs):
                    print(f"  Step {i}: {c} (mover={walk[i]})")
                print(f"Contradiction at proc {key[0]}, context {key[1:]}: {entries}")
            break

print()
print("="*70)
print("Contradiction type summary:")
print("="*70)
for ct, count in sorted(contradiction_types.items()):
    print(f"  {ct}: {count}")

# THE KEY INSIGHT: Let me look specifically at what happens with the ternary stay.
# Walk: [0, 4, 3, 2, 1, 0, 1, 2, 3, 3, 4]
# At steps 8 and 9, proc 3 fires twice consecutively (stay at 3).
# Step 8: mover=3, step 9: mover=3.
#
# At step 8: config[8] has proc 3 = v. Fires to v'.
# At step 9: config[9] has proc 3 = v'. Fires to v''.
# config[8] and config[9] differ only at proc 3.
# So context of proc 3 at step 8 = (c[2], v, c[4]).
# Context of proc 3 at step 9 = (c[2], v', c[4]). Different (v ≠ v').
#
# But what about the NEIGHBORS of proc 3?
# At step 8: proc 2's value is fixed (proc 2 doesn't fire at step 8).
# At step 9: proc 2's value is still the same (proc 2 doesn't fire at step 9).
# At step 7: proc 2 fires (mover=2). So config[8][2] ≠ config[7][2].
# At step 10: proc 4 fires. So config[10][4] changed.
#
# Now: proc 3 fires at steps 2, 8, 9.
# At step 2: proc 3 fires. Context = (c[2]_2, c[3]_2, c[4]_2).
# Between step 2 and step 8: procs 1, 0, 1, 2 fire (steps 3,4,5,6,7).
#   Proc 2 fires at step 7. So c[2] changes between step 2 and step 8.
# At step 8: context = (c[2]_8, c[3]_8, c[4]_8).
# At step 9: context = (c[2]_9, c[3]_9, c[4]_9) = (c[2]_8, c[3]_9, c[4]_8).
#   c[3]_9 ≠ c[3]_8 (proc 3 just fired).
#
# The contradiction likely comes from a NON-MOVER step where proc 3 has the
# same context as at one of its firing steps.

# Let me trace a specific example.
print()
print("="*70)
print("DETAILED TRACE: first distinct-config assignment")
print("="*70)

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

    print(f"Value assignment: {combo}")
    print()

    # Show all contexts for each proc
    for p in range(n):
        print(f"Proc {p} (m={ms[p]}, fc={len(fire_steps[p])}):")
        for k in range(L):
            c = configs[k]
            left_val = c[(p - 1) % n]
            self_val = c[p]
            right_val = c[(p + 1) % n]
            is_mover = (walk[k] == p)
            c_next = configs[(k + 1) % L]
            output = c_next[p] if is_mover else self_val
            marker = " <-- MOVER" if is_mover else ""
            fire_marker = f" → {c_next[p]}" if is_mover else ""
            print(f"  Step {k}: ctx=({left_val},{self_val},{right_val}) f→{output}{fire_marker}{marker}")
        print()

    # Identify the specific contradiction
    print("CONTRADICTIONS:")
    analyze_contradiction(n, ms, walk, configs)
    break
