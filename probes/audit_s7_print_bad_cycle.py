"""Print the full bad cycle for sample residual cycle 1."""
from itertools import product
import sys
sys.setrecursionlimit(20000)

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

SAMPLE = (0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1)

def build_rule(word, ms, n):
    CL = len(word)
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    configs = configs[:-1]
    rule = {p: {} for p in range(n)}
    for k in range(CL):
        cfg_k = configs[k]
        mover = word[k]
        for p in range(n):
            lp = left(p, n); rp = right(p, n)
            ctx = (cfg_k[lp], cfg_k[p], cfg_k[rp])
            if p == mover:
                rule[p][ctx] = (cfg_k[p] + 1) % ms[p]
            else:
                if ctx not in rule[p]:
                    rule[p][ctx] = cfg_k[p]
    return rule, configs

def get_priv(rule, cfg, n):
    privs = []
    for p in range(n):
        lp = left(p, n); rp = right(p, n)
        ctx = (cfg[lp], cfg[p], cfg[rp])
        if ctx in rule[p] and rule[p][ctx] != cfg[p]:
            privs.append(p)
    return privs

def step_with(rule, cfg, p, n):
    lp = left(p, n); rp = right(p, n)
    ctx = (cfg[lp], cfg[p], cfg[rp])
    new = list(cfg)
    new[p] = rule[p][ctx]
    return tuple(new)

rule, gc_configs = build_rule(list(SAMPLE), MS, N)
gc_set = set(gc_configs)

print(f"GC mover word: {SAMPLE}")
print(f"GC configs (first 5):")
for i, c in enumerate(gc_configs[:5]):
    print(f"  [{i}] {c}  mover={SAMPLE[i]}")
print()

# Find the bad cycle by walking from (0,0,0,0,0,0,0,0,1)
start = (0,0,0,0,0,0,0,0,1)
print(f"Walking bad cycle from {start}...")
cur = start
path = []
seen = {}
while cur not in seen:
    seen[cur] = len(path)
    privs = get_priv(rule, cur, N)
    if not privs:
        print(f"  STUCK at {cur}")
        break
    if len(privs) > 1:
        print(f"  AMBIGUOUS at {cur}, privs={privs}")
        # Pick first
    p = privs[0]
    path.append((cur, p))
    cur = step_with(rule, cur, p, N)
    if cur in gc_set:
        print(f"  HIT GC at {cur}")
        break
    if len(path) > 50:
        print("  too long, stopping")
        break

if cur in seen:
    cycle_start = seen[cur]
    cycle = path[cycle_start:]
    print(f"\nBad cycle (length {len(cycle)}):")
    bad_word = []
    for i, (c, p) in enumerate(cycle):
        bad_word.append(p)
        print(f"  bad[{i:2d}] {c}  mover={p}")
    print(f"\nBad mover word: {tuple(bad_word)}")

    # Compare bad word and gc word
    print(f"\nGC mover word:  {SAMPLE}")
    print(f"Bad word:       {tuple(bad_word)}")

    # Fire count in bad cycle
    from collections import Counter
    bad_fc = Counter(bad_word)
    gc_fc = Counter(SAMPLE)
    print(f"\nBad fc: {dict(bad_fc)}")
    print(f"GC fc:  {dict(gc_fc)}")

    # Winding
    cw_bad = sum(1 for k in range(len(bad_word)) if bad_word[(k+1)%len(bad_word)] == right(bad_word[k]))
    ccw_bad = sum(1 for k in range(len(bad_word)) if bad_word[(k+1)%len(bad_word)] == left(bad_word[k]))
    print(f"\nBad winding: cw={cw_bad}, ccw={ccw_bad}, diff={cw_bad - ccw_bad}")

    # Compare bad config[k] to gc config[k+δ] for various δ
    print("\nLooking for shift relationship to gc:")
    for delta in range(24):
        match = True
        # Check if shifting gc by delta and forcing some proc to a value gives bad
        # Try forcing each proc to each value
        for force_proc in range(N):
            for force_val in range(MS[force_proc]):
                ok = True
                for i in range(min(len(cycle), 5)):
                    bad_c = cycle[i][0]
                    gc_c = list(gc_configs[(i + delta) % 24])
                    gc_c[force_proc] = force_val
                    if bad_c != tuple(gc_c):
                        ok = False
                        break
                if ok:
                    print(f"  bad[k] = gc[(k+{delta})%24] with proc {force_proc} forced to {force_val}")
                    break
