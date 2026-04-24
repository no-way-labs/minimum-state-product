"""Check if all fair Q4 cycles are TF-blocked."""

def getBit(cfg, j):
    return (cfg >> j) & 1

def flipBit(cfg, j):
    return cfg ^ (1 << j)

def leftP(j):
    return (j + 3) % 4

def rightP(j):
    return (j + 1) % 4

def tfKeyNat(cfg, proc):
    return proc * 8 + getBit(cfg, leftP(proc)) * 4 + getBit(cfg, proc) * 2 + getBit(cfg, rightP(proc))

def collectTF(cycle):
    result = []
    for cfg, proc in cycle:
        mc = (tfKeyNat(cfg, proc), 1 - getBit(cfg, proc))
        result.append(mc)
        for p in range(4):
            if p != proc:
                result.append((tfKeyNat(cfg, p), getBit(cfg, p)))
    return result

def hasTFConflict(constraints):
    d = {}
    for k, v in constraints:
        if k in d and d[k] != v:
            return True
        d[k] = v
    return False

def buildTF(constraints):
    d = {}
    for k, v in constraints:
        if k in d:
            if d[k] != v:
                return None
        else:
            d[k] = v
    return d

def hasForcedKernel(cycle):
    tf = buildTF(collectTF(cycle))
    if tf is None:
        return True
    cycleMask = 0
    for cfg, _ in cycle:
        cycleMask |= (1 << cfg)
    forcedTargets = []
    for cfg in range(16):
        if (cycleMask >> cfg) & 1 == 1:
            forcedTargets.append(0)
        else:
            mask = 0
            for proc in range(4):
                key = tfKeyNat(cfg, proc)
                if key in tf:
                    val = tf[key]
                    if val != getBit(cfg, proc):
                        target = flipBit(cfg, proc)
                        if (cycleMask >> target) & 1 == 0:
                            mask |= (1 << target)
            forcedTargets.append(mask)
    allMask = 65535
    initRemaining = allMask & (allMask ^ cycleMask)
    remaining = initRemaining
    for _ in range(16):
        sinks = 0
        for cfg in range(16):
            if (remaining >> cfg) & 1 == 0:
                continue
            if forcedTargets[cfg] & remaining == 0:
                sinks |= (1 << cfg)
        if sinks == 0:
            return remaining != 0
        remaining = remaining & (allMask ^ sinks)
    return remaining != 0

count_total = 0
count_tf = 0
count_kernel = 0
count_both = 0
not_tf_examples = []

def dfs(start, cur, visited, path, fairMask):
    global count_total, count_tf, count_kernel, count_both
    for proc in range(4):
        nxt = flipBit(cur, proc)
        newFair = fairMask | (1 << proc)
        newPath = path + [(cur, proc)]
        if nxt == start:
            if newFair == 15:
                count_total += 1
                is_tf = hasTFConflict(collectTF(newPath))
                is_kern = hasForcedKernel(newPath)
                if is_tf:
                    count_tf += 1
                if is_kern:
                    count_kernel += 1
                if is_tf and is_kern:
                    count_both += 1
                if not is_tf and not is_kern:
                    print(f"ERROR: cycle not blocked at all! path={newPath}")
                if not is_tf:
                    not_tf_examples.append(newPath)
        elif not (visited >> nxt) & 1:
            dfs(start, nxt, visited | (1 << nxt), newPath, newFair)

for s in range(16):
    dfs(s, s, 1 << s, [], 0)

print(f"Total fair cycles: {count_total}")
print(f"TF-blocked: {count_tf}")
print(f"Kernel-blocked: {count_kernel}")
print(f"Both: {count_both}")
print(f"Not TF-blocked: {count_total - count_tf}")
print(f"Only kernel-blocked: {count_kernel - count_both}")
if not_tf_examples:
    print(f"\nFirst 3 non-TF-blocked examples:")
    for ex in not_tf_examples[:3]:
        print(f"  {ex}")
