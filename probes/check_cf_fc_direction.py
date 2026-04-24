#!/usr/bin/env python3
"""Check whether constant-FutureFc bad steps can decrease fc.

If every CF step is fc-nondecreasing, then CF ⊆ nonneg and
cup2BadConstFutureStep_wf follows directly from cup2BadStepNonneg_wf.
"""

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def get_ms(n):
    """State counts for CUP-2: (2,3,...,3,2)"""
    ms = [3]*n
    ms[0] = 2
    ms[n-1] = 2
    return ms

def get_trans(n, i, L, S, R):
    """CUP-2 transition for position i with context (L, S, R)"""
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

def frontier_bit(L, S, R):
    """1 if S != L and S != R, else 0"""
    return 1 if (S != L and S != R) else 0

def fc(config, n):
    """Frontier count"""
    total = 0
    ms = get_ms(n)
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        total += frontier_bit(L, S, R)
    return total

def is_good(config, n, good_set):
    return tuple(config) in good_set

def fire(config, n, i):
    """Fire position i, return new config or None if not privileged"""
    ms = get_ms(n)
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S:
        return None  # not privileged
    new_config = list(config)
    new_config[i] = new_S
    return tuple(new_config)

def build_good_set(n):
    """Build good cycle configs for CUP-2"""
    # Good configs are those where all frontier bits are 0 (fc=0)
    # Actually, good cycle is more complex. Let me compute it properly.
    # From the memory: good configs = (n+2)(n+3)/2 - 5
    # But we need the actual set. Let me use the cycle construction.
    # For our purposes, we just need to know which configs are good.
    # Good = configs on the good cycle. For now, approximate: config with fc=0 is good.
    # Actually, fc=0 means no frontier bits, meaning every S equals L or R.
    # That's the "legitimate" configs. But the good cycle includes more.

    # Let me compute good configs properly via the cycle.
    # From memory: good cycle length 3n-2, good configs (n+2)(n+3)/2 - 5
    # But computing the exact good set is complex. Let me just check ALL bad steps.
    # A config is "bad" if it's not in the good cycle.
    # For our analysis, what matters is: among BAD configs, can a step decrease fc?

    # Actually we don't need the good set to check fc direction.
    # ANY privileged step (not just bad steps) - does it ever decrease fc?
    pass

def check_all_steps(n):
    """Check all privileged steps: does firing ever decrease fc?"""
    ms = get_ms(n)
    fc_decrease_count = 0
    fc_increase_count = 0
    fc_preserve_count = 0
    total_priv = 0

    # Enumerate all configs
    from itertools import product
    ranges = [range(m) for m in ms]

    for config in product(*ranges):
        old_fc = fc(config, n)
        for i in range(n):
            new_config = fire(config, n, i)
            if new_config is None:
                continue
            total_priv += 1
            new_fc = fc(new_config, n)
            if new_fc < old_fc:
                fc_decrease_count += 1
                if fc_decrease_count <= 5:
                    print(f"  FC DECREASE: config={config}, fire pos {i}, fc {old_fc} -> {new_fc}")
            elif new_fc > old_fc:
                fc_increase_count += 1
            else:
                fc_preserve_count += 1

    print(f"\nn={n}: {total_priv} privileged steps")
    print(f"  fc increase: {fc_increase_count}")
    print(f"  fc preserve: {fc_preserve_count}")
    print(f"  fc decrease: {fc_decrease_count}")
    return fc_decrease_count

for n in [5, 6, 7, 8, 9]:
    print(f"\n{'='*50}")
    print(f"Checking n={n}")
    check_all_steps(n)
