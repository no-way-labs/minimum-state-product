"""Exhaustive enumeration: do fc=2 ZW cw>0 good cycles exist in the no-pivot
n=9 family ms=(2,3,3,2,3,3,2,3,3)?

If NO: the palindromic (fc=2) theorem only needs to cover 3CB layouts, and the
provider/clustering route (Theorem A) handles everything else.

If YES: Theorem B must be extended to non-3CB, which is a real math gap.
"""
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 2 * N  # fc=2 for all ⇒ CL = 2n = 18

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

# Enumerate fc=2 good cycle mover words with DFS.
# Start with proc 0 (fire count distributed: 2 per proc).
# Constraints:
#  - locality: word[k+1] ∈ {word[k], left(word[k]), right(word[k])}
#  - each proc fires exactly ms[p] = 2 times if ms[p]==2, and 2 times if ms[p]==3 (fc=2 hypothesis)
#    Actually fc=2 for ALL procs (including ternary), and ternary fc divisible by ms means fc % 3 == 0.
#    fc=2 is NOT divisible by 3! So ternary procs CANNOT have fc=2. CONTRADICTION.
#
# Wait — actually for a "good cycle" in the Lean sense, each proc fires fc[p] times
# where fc[p] must be such that after fc[p] fires, the state returns.
# For a binary proc, each fire flips 0↔1, so fc even.
# For a ternary proc, each fire goes 0→1→2→0, so fc divisible by 3.
# "All fc = 2" then requires 2 divisible by 3 for ternary, which is FALSE.
#
# So fc=2 for all procs is ONLY possible when all procs are binary.
# In ms=(2,3,3,2,3,3,2,3,3), there are 6 ternary procs, so fc=2 for all is IMPOSSIBLE.

print(f"ms = {MS}")
binary_count = sum(1 for m in MS if m == 2)
ternary_count = sum(1 for m in MS if m == 3)
print(f"binary: {binary_count}, ternary: {ternary_count}")
print()
print("fc=2 constraint per proc:")
print("  binary proc: 2 divisible by 2 → OK")
print("  ternary proc: 2 divisible by 3 → FALSE")
print()
print(f"CONCLUSION: fc=2 for ALL procs is impossible when any proc is ternary.")
print(f"So in {MS} with 6 ternary procs, no fc=2 good cycle exists.")
print(f"Minimum ternary fc is 3. Minimum CL = 2*3 + 6*3 = 24.")
print()

# But wait — "palindromic" in the math refers to fc=2 for BINARY and fc=3 for TERNARY
# (the actual minimum-CL case). Let me check that regime.
min_cl = 2 * binary_count + 3 * ternary_count
print(f"Minimum CL (fc=2 binary, fc=3 ternary) = 2*{binary_count} + 3*{ternary_count} = {min_cl}")

# Enumerate good cycles at this minimum CL.
# Good cycle: (a) locality, (b) each proc fires required count, (c) state returns to start,
# (d) all configs distinct, (e) ZW and cw > 0 for our question.

fire_target = [2 if MS[p] == 2 else 3 for p in range(N)]
print(f"Target fire counts (minimum): {fire_target}")
print(f"Sum check: {sum(fire_target)} == CL={min_cl}? {sum(fire_target) == min_cl}")
print()

found_cycles = []
count_checked = 0

def dfs(word, fc, config, start_config):
    global count_checked
    if len(word) == min_cl:
        count_checked += 1
        if config != start_config:
            return
        if fc != fire_target:
            return
        # Valid closed cycle. Check uniqueness of configs.
        cfg = list(start_config)
        seen_configs = {tuple(cfg)}
        for m in word:
            cfg[m] = (cfg[m] + 1) % MS[m]
            t = tuple(cfg)
            if t in seen_configs and t != start_config:
                return  # not a simple cycle
            seen_configs.add(t)
        if tuple(cfg) != start_config:
            return
        # ZW and cw > 0
        cw = sum(1 for k in range(min_cl) if word[(k + 1) % min_cl] == right(word[k]))
        ccw = sum(1 for k in range(min_cl) if word[(k + 1) % min_cl] == left(word[k]))
        if cw != ccw:
            return
        if cw == 0:
            return
        found_cycles.append(tuple(word))
        return
    # Pruning: fc cannot exceed target
    remaining = min_cl - len(word)
    needed = sum(max(0, fire_target[p] - fc[p]) for p in range(N))
    if needed > remaining:
        return
    last = word[-1]
    for nxt in (left(last), last, right(last)):
        if fc[nxt] + 1 > fire_target[nxt]:
            continue
        new_config = list(config)
        new_config[nxt] = (new_config[nxt] + 1) % MS[nxt]
        word.append(nxt)
        fc[nxt] += 1
        dfs(word, fc, tuple(new_config), start_config)
        word.pop()
        fc[nxt] -= 1

start = tuple([0] * N)
for p_start in range(N):
    if fire_target[p_start] == 0:
        continue
    c = list(start)
    c[p_start] = (c[p_start] + 1) % MS[p_start]
    fc = [0] * N
    fc[p_start] = 1
    dfs([p_start], fc, tuple(c), start)

print(f"Checked {count_checked} closed mover words at CL={min_cl}")
print(f"Valid good cycles with ZW cw>0 in {MS}: {len(found_cycles)}")
if found_cycles:
    print(f"First few: {found_cycles[:3]}")
