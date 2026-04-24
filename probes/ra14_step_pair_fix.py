#!/usr/bin/env python3
"""
RA14b: Fix the step pair — the Lean approach uses cwSteps[right(b)] but right(b)
fires AT that step, so right(b) changes value. The correct approach is to find
a pair where b is non-mover at BOTH steps, or use a different step pair.

Key discovery from RA14: The Lean pair (cwSteps[rb], ccwSteps[b]) ALWAYS has
right(b) firing between the steps (because right(b) fires AT cwSteps[rb], then
fires again in CCW). Yet the context still matches. WHY?

Hypothesis: The match comes from using config BEFORE the step fires. At step
cwSteps[rb], the config is the one BEFORE right(b) fires. And right(b) has its
CW-pre-fire value. Between cwSteps[rb]+1 and ccwSteps[b]-1, right(b) fires
in the CCW phase (its second firing), which toggles it back.

So the argument is:
  config[cwSteps[rb]] has right(b) at its CW-pre-fire value = v_0
  After cwSteps[rb], right(b) fires CW: becomes v_1
  Later, right(b) fires CCW: becomes v_2
  Then at ccwSteps[b], right(b) has value v_2.
  For binary: v_0 -> v_1 -> v_0 (toggle twice), so v_2 = v_0.
  BUT: this only works if right(b) fires EXACTLY ONCE between the steps
  (the CCW firing), plus the CW firing AT the step doesn't count since we
  read config BEFORE the step.

Wait, the CW firing IS at step cwSteps[rb]. The config at step cwSteps[rb]
is the pre-fire config. So config[cwSteps[rb]](right(b)) = pre-CW-fire value.
Then right(b) fires CW (changes to something else), then later fires CCW.
At ccwSteps[b], right(b) has fired twice since cwSteps[rb].
For binary: 2 firings = toggle twice = identity. So value returns to original.

This is the KEY: config[cwSteps[rb]](right(b)) = pre-CW-fire value.
                 config[ccwSteps[b]](right(b)) = post-2-firings value.
For binary, toggle twice = identity, so they're equal.

For left(b) and b: they may fire 0 or 1 times between the two steps.
Let me trace exactly.
"""

from itertools import product as iproduct
from collections import defaultdict


def enumerate_fc2_walks(n):
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == 2 * n:
            nxt = path[0]
            if abs(pos - nxt) == 1 or abs(pos - nxt) == n - 1:
                if all(f == 2 for f in fc):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < 2:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    unique = set()
    result = []
    for w in walks:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def step_dir(word, t, n):
    L = len(word)
    curr = word[t]
    nxt = word[(t + 1) % L]
    d = (nxt - curr) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0


def winding_number(word, n):
    return sum(step_dir(word, t, n) for t in range(len(word)))


def is_sweep(word, n):
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    return all(d == 1 for d in dirs) or all(d == n - 1 for d in dirs)


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def build_configs(word, n, ms, combo):
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    return configs


def main():
    print("=" * 72)
    print("RA14b: Correct step pair analysis")
    print("=" * 72)

    # KEY QUESTION: What is the RIGHT step pair?
    # The Lean code uses: k1 = ccwSteps[b], k2 = cwSteps[right(b)]
    # At k2: right(b) fires CW, so config[k2] has right(b) PRE-CW value
    # At k1: b fires CCW, so config[k1] has b PRE-CCW value
    #
    # Between k2 and k1 (inclusive of k2 firing, exclusive of k1):
    # right(b) fires exactly ONCE more (its CCW firing)
    # So right(b) has been toggled 2 times total from config[k2] to config[k1]
    #
    # Wait no. Between step k2 and step k1, the sequence of events is:
    # Step k2: right(b) fires CW. config[k2+1] has right(b) at new value.
    # ...intermediate steps...
    # Step (ccwSteps[right(b)]): right(b) fires CCW.
    # ...more steps...
    # Step k1: b fires CCW. config[k1] has everything frozen since last fire.
    #
    # From config[k2] to config[k1], right(b) fires 0, 1, or 2 times STRICTLY
    # between k2 and k1 (not counting the k2 firing itself).

    # Let me count PRECISELY: fires of each proc from step k2+1 to step k1-1
    # (the steps STRICTLY between k2 and k1)

    print("\n--- Detailed firing trace for the LEAN step pair ---")

    for n in [5, 7]:
        print(f"\n=== n = {n} ===")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                k2 = cw_fire[rb]   # right(b) fires CW
                k1 = ccw_fire[b]   # b fires CCW

                # Steps strictly between k2 and k1 (exclusive both endpoints)
                if k2 < k1:
                    between = list(range(k2 + 1, k1))
                else:
                    between = list(range(k2 + 1, L)) + list(range(0, k1))

                movers = [w[t] for t in between]
                f_lb = movers.count(lb)
                f_b = movers.count(b)
                f_rb = movers.count(rb)

                # Fires INCLUDING the k2 step (right(b) fires at k2)
                # But config[k2] is the PRE-fire config, so we DON'T count k2
                # The fires affecting config between config[k2] and config[k1] are:
                # steps k2, k2+1, ..., k1-1 (these are the steps whose firing
                # transforms config[k2] → config[k2+1] → ... → config[k1])
                # Step k2 fires right(b). Steps k2+1..k1-1 fire the 'between' movers.
                total_rb_fires_affecting = 1 + f_rb  # 1 for step k2 + between

                # For the config equality config[k2](p) = config[k1](p):
                # We need p to fire an even number of times in steps k2..k1-1
                # For p = right(b): fires 1 (at k2) + f_rb (between)
                # For p = b: fires f_b (between)
                # For p = left(b): fires f_lb (between)
                # For binary: even fires → same value

                lb_total = f_lb
                b_total = f_b
                rb_total = 1 + f_rb  # includes the k2 firing

                if n <= 7 and len(nonsweep_zw) <= 10:
                    pass  # will print below

    # Now the CORRECT approach: we need a DIFFERENT step pair.
    # Instead of cwSteps[right(b)] and ccwSteps[b], what about:
    # k2' = step AFTER cwSteps[right(b)], i.e., the step where config has
    # right(b) at its POST-CW-fire value?
    #
    # OR: use cwSteps[left(b)] and ccwSteps[b] (left(b) fires CW, b non-mover)
    # OR: use the REVERSED pair: ccwSteps[right(b)] and cwSteps[b]

    print("\n" + "=" * 72)
    print("APPROACH A: Use (cwSteps[b+1]+1, ccwSteps[b]) — shift k2 by 1")
    print("  This uses the config AFTER right(b) has fired CW.")
    print("  Between config[k2+1] and config[k1]:")
    print("  - right(b) fires: f_rb times (just the CCW firing)")
    print("  - left(b) fires: f_lb times")
    print("  - b fires: f_b times")
    print("=" * 72)

    # But this doesn't give us the right non-mover step! At step k2,
    # right(b) IS the mover. At step k2+1, b might or might not be non-mover.
    # The EC witness needs: at k2, b is non-mover (right(b) is mover) — YES.
    # At k1, b IS the mover — YES.
    # So we use config[k2] and config[k1] for the EC, and we need
    # config[k2](p) = config[k1](p) for p in {lb, b, rb}.

    # Between config[k2] and config[k1], the firing steps are k2, k2+1, ..., k1-1.
    # These include the k2 step where right(b) fires.
    # So right(b) fires 1 + f_rb times total.

    # For binary right(b): need 1 + f_rb to be EVEN, i.e., f_rb is ODD.
    # From the data: f_rb is 1 in most cases, which is ODD → 1+1=2 → EVEN.

    print("\n" + "=" * 72)
    print("APPROACH B: The CORRECT argument for the Lean pair")
    print("  Between config[k2] and config[k1], the total fires of each proc")
    print("  (steps k2, k2+1, ..., k1-1) are:")
    print("  - right(b): 1 + f_rb (1 for the CW firing at k2, f_rb for between)")
    print("  - b: f_b")
    print("  - left(b): f_lb")
    print("  For binary, need even total fires for each.")
    print("=" * 72)

    all_ok = True
    all_data = []

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                # Steps k2, k2+1, ..., k1-1 (the steps that transform config[k2] to config[k1])
                if k2 < k1:
                    firing_steps = list(range(k2, k1))
                else:
                    firing_steps = list(range(k2, L)) + list(range(0, k1))

                firing_movers = [w[t] for t in firing_steps]
                lb_total = firing_movers.count(lb)
                b_total = firing_movers.count(b)
                rb_total = firing_movers.count(rb)

                lb_even = lb_total % 2 == 0
                b_even = b_total % 2 == 0
                rb_even = rb_total % 2 == 0

                # For binary procs, need even fires
                lb_is_binary = ms[lb] == 2
                b_is_binary = ms[b] == 2  # always True
                rb_is_binary = ms[rb] == 2

                # For non-binary, we need 0 fires (can't use parity argument)
                lb_ok = (lb_is_binary and lb_even) or (lb_total == 0)
                b_ok = (b_is_binary and b_even) or (b_total == 0)
                rb_ok = (rb_is_binary and rb_even) or (rb_total == 0)

                all_data.append({
                    'n': n, 'w': list(w), 'b': b, 'lb': lb, 'rb': rb,
                    'k2': k2, 'k1': k1,
                    'lb_total': lb_total, 'b_total': b_total, 'rb_total': rb_total,
                    'lb_is_binary': lb_is_binary, 'rb_is_binary': rb_is_binary,
                    'lb_ok': lb_ok, 'b_ok': b_ok, 'rb_ok': rb_ok,
                })

                if not (lb_ok and b_ok and rb_ok):
                    all_ok = False
                    print(f"  FAIL: w={list(w)}, b={b}")
                    print(f"    lb={lb}(m={ms[lb]}): {lb_total} fires {'EVEN' if lb_even else 'ODD'}")
                    print(f"    b={b}(m={ms[b]}): {b_total} fires {'EVEN' if b_even else 'ODD'}")
                    print(f"    rb={rb}(m={ms[rb]}): {rb_total} fires {'EVEN' if rb_even else 'ODD'}")

    if all_ok:
        print("\n  ALL GOOD — every (walk, b) has even fires for binary, 0 fires for ternary")
    else:
        print("\n  SOME FAILURES")

    # Detailed summary
    print("\n" + "=" * 72)
    print("DETAILED SUMMARY of total fires (steps k2..k1-1)")
    print("=" * 72)

    fire_patterns = defaultdict(int)
    for d in all_data:
        key = (d['lb_total'], d['b_total'], d['rb_total'],
               d['lb_is_binary'], d['rb_is_binary'])
        fire_patterns[key] += 1

    for (fl, fb, fr, lbin, rbin), count in sorted(fire_patterns.items()):
        lb_par = "E" if fl % 2 == 0 else "O"
        b_par = "E" if fb % 2 == 0 else "O"
        rb_par = "E" if fr % 2 == 0 else "O"
        lb_type = "bin" if lbin else "ter"
        rb_type = "bin" if rbin else "ter"
        ok = ((lbin and fl % 2 == 0) or fl == 0) and \
             (fb % 2 == 0) and \
             ((rbin and fr % 2 == 0) or fr == 0)
        print(f"  lb({lb_type})={fl}[{lb_par}], b(bin)={fb}[{b_par}], rb({rb_type})={fr}[{rb_par}]: {count} cases {'OK' if ok else 'FAIL'}")

    # ==================================================================
    # APPROACH C: Use a DIFFERENT step pair — the REVERSED one
    # Instead of (cwSteps[rb], ccwSteps[b]), use (ccwSteps[lb], cwSteps[b])
    # ==================================================================
    print("\n" + "=" * 72)
    print("APPROACH C: Reversed pair — (ccwSteps[left(b)], cwSteps[b])")
    print("  At ccwSteps[lb]: left(b) fires CCW, b is non-mover")
    print("  At cwSteps[b]: b fires CW, b is mover")
    print("=" * 72)

    all_ok_c = True
    all_data_c = []

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if lb not in ccw_fire or b not in cw_fire:
                    continue

                k_nm = ccw_fire[lb]  # left(b) fires CCW, b non-mover
                k_m = cw_fire[b]     # b fires CW, b is mover

                # Steps k_nm, ..., k_m-1
                if k_nm < k_m:
                    firing_steps = list(range(k_nm, k_m))
                else:
                    firing_steps = list(range(k_nm, L)) + list(range(0, k_m))

                firing_movers = [w[t] for t in firing_steps]
                lb_total = firing_movers.count(lb)
                b_total = firing_movers.count(b)
                rb_total = firing_movers.count(rb)

                lb_is_binary = ms[lb] == 2
                rb_is_binary = ms[rb] == 2

                lb_ok = (lb_is_binary and lb_total % 2 == 0) or (lb_total == 0)
                b_ok = b_total % 2 == 0 or b_total == 0
                rb_ok = (rb_is_binary and rb_total % 2 == 0) or (rb_total == 0)

                all_data_c.append({
                    'n': n, 'b': b,
                    'lb_total': lb_total, 'b_total': b_total, 'rb_total': rb_total,
                })

                if not (lb_ok and b_ok and rb_ok):
                    all_ok_c = False
                    print(f"  FAIL: w={list(w)}, b={b}, fires: lb={lb_total}, b={b_total}, rb={rb_total}")

    if all_ok_c:
        print("\n  ALL GOOD for reversed pair")
    else:
        print("\n  Some failures for reversed pair too")

    # ==================================================================
    # APPROACH D: For EACH walk, find the binary b that works
    # ==================================================================
    print("\n" + "=" * 72)
    print("APPROACH D: For each walk, is there SOME binary b where the")
    print("  Lean pair has even binary fires and 0 ternary fires?")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        all_walks_have_good_b = True

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            found_good_b = False
            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                if k2 < k1:
                    firing_steps = list(range(k2, k1))
                else:
                    firing_steps = list(range(k2, L)) + list(range(0, k1))

                firing_movers = [w[t] for t in firing_steps]
                lb_total = firing_movers.count(lb)
                b_total = firing_movers.count(b)
                rb_total = firing_movers.count(rb)

                lb_is_binary = ms[lb] == 2
                rb_is_binary = ms[rb] == 2

                lb_ok = (lb_is_binary and lb_total % 2 == 0) or (lb_total == 0)
                b_ok = b_total % 2 == 0 or b_total == 0
                rb_ok = (rb_is_binary and rb_total % 2 == 0) or (rb_total == 0)

                if lb_ok and b_ok and rb_ok:
                    found_good_b = True
                    break

            if not found_good_b:
                all_walks_have_good_b = False
                print(f"  NO good b for walk {w}")
                # Show all binary procs and their fire counts
                for b in binary_pos:
                    rb = (b + 1) % n
                    lb = (b - 1) % n
                    if b not in ccw_fire or rb not in cw_fire:
                        print(f"    b={b}: missing steps")
                        continue
                    k2 = cw_fire[rb]
                    k1 = ccw_fire[b]
                    if k2 < k1:
                        firing_steps = list(range(k2, k1))
                    else:
                        firing_steps = list(range(k2, L)) + list(range(0, k1))
                    firing_movers = [w[t] for t in firing_steps]
                    lb_t = firing_movers.count(lb)
                    b_t = firing_movers.count(b)
                    rb_t = firing_movers.count(rb)
                    print(f"    b={b}: lb({lb},m={ms[lb]})={lb_t}, b={b_t}, rb({rb},m={ms[rb]})={rb_t}")

        if all_walks_have_good_b:
            print(f"  ALL walks have a good binary b!")

    # ==================================================================
    # APPROACH E: The proper characterization — for binary neighbors,
    # even fires suffice. For ternary neighbors, need 0 fires.
    # What if we allow ternary neighbors to fire with the right pattern?
    # ==================================================================
    print("\n" + "=" * 72)
    print("APPROACH E: Can we VERIFY context match directly for ALL combos?")
    print("  For each walk and each b, check if config[k2](p) = config[k1](p)")
    print("  for ALL state-sequence combos, not just using parity.")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            fc = [0] * n
            for p in w:
                fc[p] += 1
            proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
            sl = [proc_seqs[p] for p in range(n)]

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                total_valid = 0
                lb_match = 0
                b_match = 0
                rb_match = 0
                all3_match = 0

                for combo in iproduct(*sl):
                    configs = build_configs(w, n, ms, combo)
                    if configs[-1] != configs[0]:
                        continue
                    if len(set(configs[:L])) != L:
                        continue
                    total_valid += 1

                    c_k2 = configs[k2]
                    c_k1 = configs[k1]

                    lb_eq = c_k2[lb] == c_k1[lb]
                    b_eq = c_k2[b] == c_k1[b]
                    rb_eq = c_k2[rb] == c_k1[rb]

                    if lb_eq: lb_match += 1
                    if b_eq: b_match += 1
                    if rb_eq: rb_match += 1
                    if lb_eq and b_eq and rb_eq:
                        all3_match += 1

                if total_valid > 0:
                    if all3_match < total_valid:
                        print(f"  Walk {w}, b={b}: all3_match={all3_match}/{total_valid}")
                        print(f"    lb_match={lb_match}, b_match={b_match}, rb_match={rb_match}")
                    # Count this walk-b pair
                    pass

        # Summary: for each walk, does SOME b have all3_match = total_valid?
        print(f"\n  Checking: for each walk, SOME b has universal context match...")
        walk_results = []
        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            fc = [0] * n
            for p in w:
                fc[p] += 1
            proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
            sl = [proc_seqs[p] for p in range(n)]

            best_b = None
            best_rate = 0

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                total_valid = 0
                all3_match = 0

                for combo in iproduct(*sl):
                    configs = build_configs(w, n, ms, combo)
                    if configs[-1] != configs[0]:
                        continue
                    if len(set(configs[:L])) != L:
                        continue
                    total_valid += 1

                    c_k2 = configs[k2]
                    c_k1 = configs[k1]

                    if c_k2[lb] == c_k1[lb] and c_k2[b] == c_k1[b] and c_k2[rb] == c_k1[rb]:
                        all3_match += 1

                if total_valid > 0:
                    rate = all3_match / total_valid
                    if rate > best_rate:
                        best_rate = rate
                        best_b = b

            walk_results.append((list(w), best_b, best_rate))
            if best_rate < 1.0:
                print(f"  Walk {w}: best b={best_b}, match rate={best_rate:.3f}")
            else:
                print(f"  Walk {w}: b={best_b} gives 100% match")

    # ==================================================================
    # FINAL: The right approach for ternary right(b)
    # ==================================================================
    print("\n" + "=" * 72)
    print("FINAL: Analysis of ternary neighbor firing")
    print("=" * 72)
    print("""
    Key finding: For the Lean pair (cwSteps[rb], ccwSteps[b]):
    - right(b) ALWAYS fires between the two steps (its CW firing IS at k2,
      and then it fires CCW later).
    - Total fires of right(b) from config[k2] to config[k1] = 1 + f_rb.

    For BINARY right(b): need 1 + f_rb EVEN, i.e., f_rb ODD.
    For TERNARY right(b): need state to return to original after total fires.
      With fc=2, ternary fires 0→v1→0. The two firings are (CW, CCW).
      If right(b) fires BOTH times between k2 and k1:
        total fires = 2, state: s0 → s1 → s0 (returns to original).
      This is exactly the ODD case f_rb = 1 (between is 1, total is 2).

    So for BOTH binary and ternary right(b), the condition is the same:
    right(b) fires EXACTLY 2 times total between config[k2] and config[k1].
    For fc=2, this means BOTH firings happen between k2 and k1.
    That is: the CW firing (at k2) and the CCW firing both happen in [k2, k1).

    This is always true when k2 = cwSteps[rb] < ccwSteps[rb] < k1 = ccwSteps[b].
    i.e., right(b)'s CCW firing comes before b's CCW firing.

    For the palindromic walk, CCW firings happen in REVERSE order of CW firings.
    If CW order is: ..., b, b+1, ..., turnaround, and
    CCW order is: turnaround-1, ..., b+1, b, ...,
    then right(b) = b+1 fires CCW BEFORE b fires CCW.

    So ccwSteps[rb] < ccwSteps[b] (in the linear ordering of steps within the
    CCW phase). Combined with cwSteps[rb] being in the CW phase:
    both firings of right(b) are within [k2, k1).

    This means: right(b) fires exactly 2 times → returns to original value.
    For binary: toggle twice = identity.
    For ternary: v0 → v1 → v0 (fc=2 sequence always returns to start).

    CONCLUSION: The 3 sorrys can be discharged by proving:

    1. b fires 0 times between k2 and k1 (b doesn't fire between its
       non-mover step and its CCW mover step) → config_val_eq_of_no_move_between

    2. right(b) fires exactly 2 times between k2 and k1 (both CW and CCW
       firings happen in this interval) → state returns to original
       (needs a NEW lemma: config_val_eq_of_full_cycle_between)

    3. left(b) fires 0 times between k2 and k1 (need to verify this!)
       OR left(b) fires 2 times (both CW and CCW) → same argument as right(b)
    """)

    # Verify claim about left(b)
    print("Verifying left(b) fires between k2 and k1:")
    for n in [5, 7]:
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]
        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]
            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n
                if b not in ccw_fire or rb not in cw_fire:
                    continue
                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                # Total fires of each in [k2, k1)
                if k2 < k1:
                    firing_steps = list(range(k2, k1))
                else:
                    firing_steps = list(range(k2, L)) + list(range(0, k1))

                firing_movers = [w[t] for t in firing_steps]
                lb_t = firing_movers.count(lb)
                b_t = firing_movers.count(b)
                rb_t = firing_movers.count(rb)

                # Check: is ccwSteps[rb] in [k2+1, k1)?
                ccw_rb = ccw_fire.get(rb)
                if ccw_rb is not None:
                    if k2 < k1:
                        rb_ccw_between = k2 < ccw_rb < k1
                    else:
                        rb_ccw_between = ccw_rb > k2 or ccw_rb < k1

                print(f"  n={n} w={w} b={b}: lb_fires={lb_t}, b_fires={b_t}, rb_fires={rb_t}, rb_ccw_in_range={rb_ccw_between}")


if __name__ == "__main__":
    main()
