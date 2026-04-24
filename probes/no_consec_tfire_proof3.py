"""
PROOF: No consecutive t-fires at sandwiched ternary.

The proof works through TWO independent mechanisms:

MECHANISM 1 (even fc(t)): Direct parity contradiction.
  With one empty phase: fc(bL)+fc(bR) = fc(t)-1 (from counting).
  Binary parity: fc(bL)+fc(bR) even.
  fc(t)-1 even iff fc(t) odd. So if fc(t) even: contradiction.

MECHANISM 2 (odd fc(t)): The wrap-around phase argument.

  With fc(t) odd phases, one empty, fc(t)-1 non-empty with J+K=1 each:
  fc(bL)+fc(bR) = fc(t)-1.

  But we need to account for the WRAP-AROUND phase more carefully.

  The fc(t) phases decompose into:
  - fc(t)-1 "interior" pairs (between consecutive t-fire positions in the linear order)
  - 1 "wrap-around" pair (last t-fire to first t-fire)

  The empty phase (consecutive fires at k, k+1) is one of the interior pairs.

  Interior pair counting: fc(t)-1 interior pairs, one empty, fc(t)-2 with J+K >= 1.
  So interior contribution >= fc(t)-2.

  Wrap-around pair: the gap from the last t-fire p_{fc(t)-1} to the first t-fire p_0 + CL.
  This wraps around the cycle. The J+K contribution from this gap >= 1 if it's a valid
  TernaryPhase (which it is, since fc(t) < CL means there's room).

  Wait: does normalForm apply to the wrap-around phase? The all-normalForm hypothesis
  says ALL TernaryPhases are normalForm. The wrap-around phase IS a TernaryPhase
  (it has a < s structure if we think of the cycle linearly). But the TernaryPhase
  structure requires a.val < s.val (linear ordering). For the wrap-around: the "start"
  is at position p_{fc(t)-1}+1 and the "end" is at position p_0 (wrapping around).
  This doesn't fit the a.val < s.val requirement unless we linearize the cycle.

  Actually, looking at the Lean code: `hno_cyclic_consec` is a SEPARATE hypothesis
  that handles the cyclic case. The linear `hno_consec` handles a.val < s.val with
  a+1 < s (non-consecutive). The cyclic case: moverAt(CL-1) = t implies
  moverAt(0) != t.

  The cyclic wrap is handled separately in sparse_phase_sum_ge.

  But we're not inside sparse_phase_sum_ge; we're PROVING hno_consec and hno_cyclic_consec
  as inputs to it. So we need an independent argument.

  Let me reconsider the whole approach.

  THE SIMPLEST PROOF:

  Suppose t fires at consecutive steps k, k+1.
  Config C_{k+2} has t=v+2. f_t(c_L, v+2, c_R) = v+2 (Step 1).
  Exactly one of bL, bR fires at step k+2 (Step 2).

  NOW: the three configs C_k, C_{k+1}, C_{k+2} are:
    C_k   = B + (t=v)
    C_{k+1} = B + (t=v+1)
    C_{k+2} = B + (t=v+2)
  where B is the "background" (all positions except t).

  ALL THREE share the same background B. They differ only at t.
  They're all distinct good configs (in the cycle).

  Now: the cycle visits these 3 configs in order, at steps k, k+1, k+2.
  The cycle also visits all other good configs.

  CONSIDER: does the cycle visit any OTHER config with background B?
  A config with background B and t=w is a good config iff it has exactly one privileged proc.
  We've shown the cycle visits B+(t=v), B+(t=v+1), B+(t=v+2). That's all 3 possible
  t-values with this background. So ALL configs with background B are in the cycle.

  This means: the 3 configs form a "complete fiber" over the background B.

  Among these 3 configs:
  - At B+(t=v):   mover = t (fires, v->v+1).
  - At B+(t=v+1): mover = t (fires, v+1->v+2).
  - At B+(t=v+2): mover = bL or bR (t doesn't fire).

  The mover at B+(t=v+2) determines what happens next. Let's say it's bL.
  Then the successor of B+(t=v+2) is B'+(t=v+2) where B' differs from B only at bL.

  Now: does B'+(t=v+2) appear in the cycle? Yes (it's the config at step k+3).
  What about B'+(t=v) and B'+(t=v+1)?

  For B'+(t=v): if this is a good config and in the cycle, what's the mover?
  Config B'+(t=v) differs from B+(t=v) only at bL. It's a potentially new config.

  Actually, this line of reasoning gets complex. Let me try a completely different approach.

  THE DIRECT CONTRADICITON APPROACH:

  At C_{k+2} = B+(t=v+2): the unique privileged proc is bL (say).
  After bL fires: C_{k+3} = B'+(t=v+2) where B'[bL] = 1-c_L.

  The cycle continues from C_{k+3}. At some point, it must return to C_k = B+(t=v).
  For this to happen: bL must return to c_L, and t must return to v.

  Since bL fires even times: an even number of bL-fires in the full cycle.
  bL fires at step k+2 (from c_L to 1-c_L). Eventually fires again to return.

  Since t must return to v from v+2: t fires at least once more.

  THE KEY: at C_{k+2}, t has value v+2 and context (c_L, v+2, c_R).
  f_t(c_L, v+2, c_R) = v+2. t does NOT fire.
  At C_{k+3} = (..., 1-c_L, v+2, c_R, ...). t context is (1-c_L, v+2, c_R).
  f_t(1-c_L, v+2, c_R) = ? Could fire or not.

  If t fires at C_{k+3}: then mover at step k+3 is t.
  But we already said mover at k+2 is bL. So k+3 is the step after bL fires.
  At C_{k+3}: t privileged means f_t(1-c_L, v+2, c_R) != v+2.
  If so: t fires at k+3 also? That's fine (t didn't fire at k+2, so not 3-consec).

  Actually wait. Let me reconsider. Can t fire at k+3? Yes, if t is privileged at C_{k+3}.
  Not 3-consec: k, k+1, k+3 (gap at k+2).

  OK let me just go full computational. The analytical proof seems to require tracking
  global cycle structure, which is hard in closed form. Let me exhaustively verify
  for small n with COMPLETE system enumeration, then find the pattern.
"""

import itertools
from collections import Counter


def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))


def privileged_set(config, fs, n):
    priv = []
    for i in range(n):
        L = config[(i - 1) % n]
        S = config[i]
        R = config[(i + 1) % n]
        if fs[i][(L, S, R)] != S:
            priv.append(i)
    return priv


def find_good_cycle_dict(ms, fs):
    n = len(ms)
    configs = all_configs(ms)
    good = {}
    for c in configs:
        priv = privileged_set(c, fs, n)
        if len(priv) == 1:
            good[c] = priv[0]

    if not good:
        return None, None

    # Build successor
    succ = {}
    for c, mover in good.items():
        lst = list(c)
        L = c[(mover - 1) % n]
        S = c[mover]
        R = c[(mover + 1) % n]
        lst[mover] = fs[mover][(L, S, R)]
        nxt = tuple(lst)
        if nxt in good:
            succ[c] = (nxt, mover)

    if not succ:
        return None, None

    # Find cycle
    start = next(iter(succ))
    visited = {}
    current = start
    step = 0
    while current not in visited:
        if current not in succ:
            return None, None
        visited[current] = step
        current, _ = succ[current]
        step += 1

    cs = visited[current]
    cyc_configs = []
    cyc_movers = []
    c = current
    for _ in range(step - cs):
        if c not in succ:
            return None, None
        nxt, m = succ[c]
        cyc_configs.append(c)
        cyc_movers.append(m)
        c = nxt

    return cyc_configs, cyc_movers


def check_validity_full(ms, fs):
    """Full validity check including convergence (SCC-based)."""
    n = len(ms)
    configs = all_configs(ms)

    good_configs = set()
    priv_map = {}
    for c in configs:
        priv = privileged_set(c, fs, n)
        priv_map[c] = priv
        if len(priv) == 0:
            return False
        if len(priv) == 1:
            good_configs.add(c)

    if not good_configs:
        return False

    # Closure
    for c in good_configs:
        mover = priv_map[c][0]
        lst = list(c)
        L, S, R = c[(mover-1)%n], c[mover], c[(mover+1)%n]
        lst[mover] = fs[mover][(L, S, R)]
        nxt = tuple(lst)
        if nxt not in good_configs:
            return False

    # Convergence: check no bad cycle (simple path following for small state spaces)
    bad_set = set(c for c in configs if c not in good_configs)
    visited = set()
    for c in bad_set:
        if c in visited:
            continue
        path = []
        path_set = set()
        cur = c
        while cur not in visited and cur in bad_set:
            if cur in path_set:
                return False  # bad cycle
            path.append(cur)
            path_set.add(cur)
            priv = priv_map[cur]
            mover = priv[0]
            lst = list(cur)
            L, S, R = cur[(mover-1)%n], cur[mover], cur[(mover+1)%n]
            lst[mover] = fs[mover][(L, S, R)]
            cur = tuple(lst)
        visited.update(path_set)

    return True


def has_ec(cyc_configs, cyc_movers, n):
    CL = len(cyc_configs)
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for k in range(CL):
            c = cyc_configs[k]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if cyc_movers[k] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True
    return False


def exhaustive_n3():
    """Exhaustive at n=3, ms=(2,3,2). t=1 sandwich."""
    ms = [2, 3, 2]
    n = 3

    # Enumerate ALL transition tables
    domains = []
    for i in range(n):
        m_L = ms[(i-1)%n]
        m_S = ms[i]
        m_R = ms[(i+1)%n]
        dom = list(itertools.product(range(m_L), range(m_S), range(m_R)))
        domains.append((dom, m_S))

    # Proc 0: domain size 3*2*3=18? No: m_L=ms[2]=2, m_S=ms[0]=2, m_R=ms[1]=3 -> 2*2*3=12 entries.
    # Proc 1: m_L=ms[0]=2, m_S=ms[1]=3, m_R=ms[2]=2 -> 2*3*2=12 entries.
    # Proc 2: m_L=ms[1]=3, m_S=ms[2]=2, m_R=ms[0]=2 -> 3*2*2=12 entries.
    # Tables: 2^12 * 3^12 * 2^12 ≈ 8.9 * 10^12. Too many.

    print(f"Exhaustive n=3 infeasible ({2**12} * {3**12} * {2**12} tables).")
    print("Using focused search instead.")
    print()


def focused_n3():
    """
    At n=3, ms=(2,3,2), t=1 is the sandwich.
    The complete product has 2*3*2 = 12 configs.
    A good cycle visits some of these (those with exactly 1 privileged proc).

    Let's enumerate transition tables for just the ternary proc (position 1),
    and constrain the binary procs to make the system valid.
    """
    ms = [2, 3, 2]
    n = 3
    t = 1

    print("=== n=3, ms=(2,3,2), t=1 ===")
    print()

    total_valid = 0
    total_consec_raw = 0
    total_consec_good = 0  # with fc(t) < CL and fairness

    # Enumerate all possible transition tables
    # Table for proc i: maps (L, S, R) -> output in [0, ms[i])
    # We do the loop over proc 1 first (ternary: 3^12 options - manageable in batches)
    # Then proc 0 and 2 (binary: 2^12 each = 4096 each)

    dom0 = list(itertools.product(range(ms[2]), range(ms[0]), range(ms[1])))  # (L,S,R) for proc 0
    dom1 = list(itertools.product(range(ms[0]), range(ms[1]), range(ms[2])))  # (L,S,R) for proc 1
    dom2 = list(itertools.product(range(ms[1]), range(ms[2]), range(ms[0])))  # (L,S,R) for proc 2

    print(f"Domain sizes: proc0={len(dom0)}, proc1={len(dom1)}, proc2={len(dom2)}")
    print(f"Tables: proc0={2**len(dom0)}, proc1={3**len(dom1)}, proc2={2**len(dom2)}")
    print("Total: too large for full enumeration. Using sampling.")
    print()

    import random
    random.seed(42)

    for trial in range(2000000):
        # Random tables
        f0 = {k: random.randint(0, 1) for k in dom0}
        f1 = {k: random.randint(0, 2) for k in dom1}
        f2 = {k: random.randint(0, 1) for k in dom2}
        fs = [f0, f1, f2]

        if not check_validity_full(ms, fs):
            continue
        total_valid += 1

        cyc_configs, cyc_movers = find_good_cycle_dict(ms, fs)
        if cyc_configs is None:
            continue

        CL = len(cyc_movers)
        fc_t = sum(1 for m in cyc_movers if m == t)

        # Check consecutive
        has_consec = False
        for k in range(CL):
            if cyc_movers[k] == t and cyc_movers[(k+1) % CL] == t:
                has_consec = True
                break

        if has_consec:
            total_consec_raw += 1

            # Check preconditions
            if fc_t < CL and fc_t >= 2:
                ec = has_ec(cyc_configs, cyc_movers, n)
                if not ec:
                    all_fire = all(sum(1 for m in cyc_movers if m == p) > 0 for p in range(n))
                    if all_fire:
                        total_consec_good += 1
                        print(f"  FOUND: trial {trial}, CL={CL}")
                        print(f"    Movers: {cyc_movers}")
                        for k in range(CL):
                            if cyc_movers[k] == t and cyc_movers[(k+1) % CL] == t:
                                print(f"    Configs {k},{k+1}: {cyc_configs[k]}, {cyc_configs[(k+1)%CL]}")

    print(f"Results: {total_valid} valid, {total_consec_raw} raw consec, {total_consec_good} with preconditions")
    print()


def focused_n4():
    """n=4, ms=(2,3,2,2), t=1."""
    ms = [2, 3, 2, 2]
    n = 4
    t = 1

    print(f"=== n={n}, ms={ms}, t={t} ===")

    import random
    random.seed(42)

    total_valid = 0
    total_consec_raw = 0
    total_consec_good = 0

    domains = []
    for i in range(n):
        m_L = ms[(i-1)%n]
        m_S = ms[i]
        m_R = ms[(i+1)%n]
        dom = list(itertools.product(range(m_L), range(m_S), range(m_R)))
        domains.append((dom, m_S))

    for trial in range(1000000):
        fs = []
        for dom, m_S in domains:
            f = {k: random.randint(0, m_S - 1) for k in dom}
            fs.append(f)

        if not check_validity_full(ms, fs):
            continue
        total_valid += 1

        cyc_configs, cyc_movers = find_good_cycle_dict(ms, fs)
        if cyc_configs is None:
            continue

        CL = len(cyc_movers)
        fc_t = sum(1 for m in cyc_movers if m == t)

        has_consec = False
        for k in range(CL):
            if cyc_movers[k] == t and cyc_movers[(k+1) % CL] == t:
                has_consec = True
                break

        if has_consec:
            total_consec_raw += 1
            if fc_t < CL and fc_t >= 2:
                ec = has_ec(cyc_configs, cyc_movers, n)
                if not ec:
                    all_fire = all(sum(1 for m in cyc_movers if m == p) > 0 for p in range(n))
                    if all_fire:
                        total_consec_good += 1
                        print(f"  FOUND: trial {trial}, CL={CL}, fc(t)={fc_t}")
                        print(f"    Movers: {cyc_movers}")

    print(f"Results: {total_valid} valid, {total_consec_raw} raw consec, {total_consec_good} with preconditions")
    print()


def focused_n5():
    """n=5 with various ms."""
    import random
    random.seed(42)

    for ms in [[2,3,2,2,2], [2,3,2,3,2], [2,2,3,2,2], [2,3,2,2,3]]:
        n = len(ms)
        t_candidates = [i for i in range(n) if ms[i] >= 3 and ms[(i-1)%n] == 2 and ms[(i+1)%n] == 2]
        if not t_candidates:
            continue

        threshold = 4 * 3 ** (n - 2)
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        print(f"=== n={n}, ms={ms}, sandwiches={t_candidates}, prod={prod}, threshold={threshold} ===")

        total_valid = 0
        total_consec_raw = 0
        total_consec_good = 0

        domains = []
        for i in range(n):
            m_L = ms[(i-1)%n]
            m_S = ms[i]
            m_R = ms[(i+1)%n]
            dom = list(itertools.product(range(m_L), range(m_S), range(m_R)))
            domains.append((dom, m_S))

        for trial in range(500000):
            fs = []
            for dom, m_S in domains:
                f = {k: random.randint(0, m_S - 1) for k in dom}
                fs.append(f)

            if not check_validity_full(ms, fs):
                continue
            total_valid += 1

            cyc_configs, cyc_movers = find_good_cycle_dict(ms, fs)
            if cyc_configs is None:
                continue

            CL = len(cyc_movers)

            for t in t_candidates:
                fc_t = sum(1 for m in cyc_movers if m == t)

                has_consec = False
                for k in range(CL):
                    if cyc_movers[k] == t and cyc_movers[(k+1) % CL] == t:
                        has_consec = True
                        break

                if has_consec:
                    total_consec_raw += 1
                    if fc_t < CL and fc_t >= 2:
                        ec = has_ec(cyc_configs, cyc_movers, n)
                        if not ec:
                            all_fire = all(sum(1 for m in cyc_movers if m == p) > 0 for p in range(n))
                            if all_fire:
                                total_consec_good += 1
                                print(f"  FOUND: trial {trial}, t={t}, CL={CL}, fc(t)={fc_t}")
                                print(f"    Fire counts: {[sum(1 for m in cyc_movers if m == p) for p in range(n)]}")
                                print(f"    Movers: {cyc_movers[:30]}...")

        print(f"Results: {total_valid} valid, {total_consec_raw} raw consec, {total_consec_good} with preconditions")
        print()


def main():
    print("=" * 70)
    print("NO CONSECUTIVE T-FIRES: Exhaustive + Focused Search")
    print("=" * 70)
    print()

    focused_n3()
    focused_n4()
    focused_n5()

    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)


if __name__ == "__main__":
    main()
