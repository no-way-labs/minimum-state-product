"""Deep analysis of the shift-based bad cycle construction.

Hypothesis: For a residual good cycle gc with |disp|=2n=18 and some structural
properties, the shift-with-force construction
  bad[k] = gc[(k+delta) mod CL], with proc pivot forced to some fixed value
produces a valid bad cycle, where specific k-steps need special treatment at
the pivot.

Step 1: Test the bad[k] = gc[(k+2) % 24], proc 0 -> 0 hypothesis.
  Walk each bad config and check: at bad[k], is mover_k (from bad word) priv?
  Compare the actual bad configs (from deterministic DFS) to shifted gc.
"""
from collections import Counter
N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

SAMPLE = (0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1)

def build_rule_and_configs(word, ms):
    CL = len(word)
    cfg = [0]*N
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    configs = configs[:-1]
    rule = {p: {} for p in range(N)}
    for k in range(CL):
        cfg_k = configs[k]
        mover = word[k]
        for p in range(N):
            lp = left(p); rp = right(p)
            ctx = (cfg_k[lp], cfg_k[p], cfg_k[rp])
            if p == mover:
                rule[p][ctx] = (cfg_k[p] + 1) % ms[p]
            else:
                if ctx not in rule[p]:
                    rule[p][ctx] = cfg_k[p]
    return rule, configs

rule, gc_configs = build_rule_and_configs(list(SAMPLE), MS)
gc_set = set(gc_configs)

# The bad cycle from audit_s7_print_bad_cycle.py
BAD_WORD = (7, 6, 5, 4, 3, 2, 8, 7, 8, 0, 1, 7, 6, 5, 4, 5, 4, 3, 2, 8, 0, 1, 2, 1)
BAD_START = (0, 0, 0, 0, 0, 0, 0, 0, 1)

# Reconstruct bad cycle
bad_cfg = list(BAD_START)
bad_configs = [tuple(bad_cfg)]
for m in BAD_WORD:
    bad_cfg[m] = (bad_cfg[m] + 1) % MS[m]
    bad_configs.append(tuple(bad_cfg))
assert bad_configs[-1] == BAD_START, "bad cycle doesn't close"
bad_configs = bad_configs[:-1]

# Test: does bad[k] correspond to gc[(k+δ) % CL] with proc pivot forced?
for delta in range(24):
    matches = []
    for k in range(24):
        bk = bad_configs[k]
        gc_k = list(gc_configs[(k + delta) % 24])
        # compute the "forced proc" = procs where they differ
        diffs = [p for p in range(N) if bk[p] != gc_k[p]]
        matches.append(tuple(diffs))
    cnt = Counter(matches)
    if len(cnt) <= 5:
        print(f"delta={delta}: diffs by k: {cnt}")

print()
# Detailed match: try delta=2
print("Delta=2 detail:")
for k in range(24):
    gc_k = gc_configs[(k + 2) % 24]
    bk = bad_configs[k]
    diffs = [(p, gc_k[p], bk[p]) for p in range(N) if bk[p] != gc_k[p]]
    matches_all_zero = all(bk[p] == 0 for p in range(N) if bk[p] != gc_k[p])
    diff_str = ",".join(f"p{p}:{g}->{b}" for p, g, b in diffs) if diffs else "IDENTICAL"
    print(f"  k={k:2d}: gc[{(k+2)%24:2d}]={gc_k}, bad[{k:2d}]={bk}  diffs: {diff_str}")
