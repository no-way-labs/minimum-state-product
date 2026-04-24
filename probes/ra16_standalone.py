#!/usr/bin/env python3
"""
RA16j: Standalone adjacent-step argument (no disjointness check needed).

The adjacent-step argument says:
  For binary proc b with fc=2, firing at steps s1, s2:
  At step s1: b fires with context (L, S, R), transition f_b(L,S,R) = 1-S
  At step s1+1: b is non-mover with context (L, 1-S, R), f_b(L,1-S,R) = 1-S (stay)

  Now imagine ANY system that realizes this good cycle. The transition
  function f_b must satisfy:
    f_b(L, S, R) = 1-S    (mover at step s1)
    f_b(L, 1-S, R) = 1-S  (non-mover at step s1+1)

  These are two different entries: (L,S,R) and (L,1-S,R).
  No conflict yet!

  But now consider: could another step in the good cycle also require
  f_b at context (L, 1-S, R) with a DIFFERENT output?

  At step s1+1: f_b(L, 1-S, R) = 1-S (non-mover, stay)
  Could a MOVER step at b also see (L, 1-S, R)?
    b fires twice: steps s1 and s2.
    At s1: ctx = (L, S, R). At s2: ctx = (L', S', R').
    If (L', S', R') = (L, 1-S, R): then f_b(L, 1-S, R) = 1-(1-S) = S (fire)
    But non-mover needs f_b(L, 1-S, R) = 1-S. S != 1-S (for binary, S in {0,1}).
    CONFLICT!

    So: if the second fire at b sees the SAME (L, R) as the step after
    the first fire, we get an EC within the good cycle itself.

    This IS what EC checks: mover context = non-mover context at same proc.

  Wait -- the above argument shows that if s2's context = s1+1's context,
  we get direct EC. But we showed NO direct EC exists! So s2's (L',R') must
  differ from s1's (L,R). The adjacent-step mechanism then uses the
  shadow to MANUFACTURE a conflict that doesn't exist in the good cycle alone.

  The full argument needs both:
  (1) The good cycle's entries at b: no conflict (MNU holds at b)
  (2) The shadow entries at b: flipped mover at s sees (L, 1-S, R),
      which equals good non-mover at s+1 -> CONFLICT.

  So the shadow IS needed, but not as a separate "disjoint set" check.
  The conflict is: f_b(L, 1-S, R) must be both 1-S (good non-mover stays)
  and S (shadow mover fires back to S). Since 1-S != S, contradiction.

  Wait, but this doesn't use disjointness AT ALL. It just says:
  IF a system realizes the good cycle, THEN f_b(L, 1-S, R) = 1-S.
  IF the same system also has the shadow cycle, THEN f_b(L, 1-S, R) = S.
  Contradiction.

  But does the system HAVE to have the shadow cycle? The shadow cycle is
  hypothetical -- the system just has the good cycle.

  The argument is about showing the good cycle can't be completed to a
  valid system. The shadow adds EXTRA constraints. If the shadow cycle
  uses configs not in the good cycle, and those configs must also converge
  to the good cycle, then the transition function must handle those shadow
  configs. The conflict means: the shadow configs can't be handled consistently.

  Actually, the argument is simpler than that:
  From the good cycle alone, f_b(L, 1-S, R) = 1-S (non-mover at s+1).
  From the good cycle alone, f_b(L, S, R) = 1-S (mover at s).
  These are DIFFERENT inputs, so no conflict yet.

  The shadow adds: f_b(L, 1-S, R) = S (hypothetical mover at shadow step s).
  This conflicts with f_b(L, 1-S, R) = 1-S from the good cycle.

  But WHY must the system handle f_b(L, 1-S, R) = S?
  Because the shadow config at step s is a VALID config in the state space
  (just not in the good cycle). If this config reaches the good cycle,
  there must be a path. But f_b at this config is ALREADY determined
  by the good cycle (non-mover entry). So the shadow config can reach
  good cycle just fine -- but the "shadow mover" interpretation is wrong.

  Actually, the shadow mover isn't forced. The shadow config might have
  MULTIPLE privileged procs (not just b). So b might not even fire at
  the shadow config. The daemon could choose a different proc.

  Hmm, this complicates things. Let me reconsider.

  THE CORRECT ARGUMENT IS:
  1. Good cycle forces f_b(L, 1-S, R) = 1-S at step s+1 (non-mover, stays).
  2. Shadow config c' at step s has b's context = (L, 1-S, R).
     At c', f_b(L, 1-S, R) = 1-S (from step 1), so b is NOT privileged at c'
     (f_b returns 1-S = current value, so b doesn't want to fire).
  3. But if b WERE the only privileged proc at c', it would need to fire.
     Since f_b(L, 1-S, R) = 1-S = current value, b is NOT privileged.
     So c' either has 0 privileged procs (deadlock) or >1 (not in good cycle).
  4. If c' has 0 privileged procs: liveness fails!
  5. If c' has k >= 2 privileged procs: c' is a bad config, and its transitions
     must eventually lead to the good cycle.

  Hmm, this doesn't directly give a contradiction. The shadow config c'
  might just be a bad config that eventually reaches good.

  THE REAL OBSTRUCTION requires showing the shadow configs form a CYCLE
  among bad configs, violating convergence. Or showing a counting argument
  (2L > product, so can't have 2L distinct configs).

  Let me reconsider. Maybe the counting argument IS the key.

  Counting argument:
  - Good cycle has L configs (all distinct, all good)
  - Shadow has L configs (disjoint from good, all distinct)
  - Total: 2L distinct configs needed
  - Product of ms = total configs in state space
  - If 2L > product: contradiction (can't have 2L distinct configs)

  L = sum(ms) (cycle length for fc = m_i at each proc)
  product = prod(ms)

  For ms = [2, 2, 3, 3, 2, 3, 3] (n=7):
    L = 2+2+3+3+2+3+3 = 18
    2L = 36
    product = 648
    2L = 36 < 648. NO contradiction from counting!

  So the counting argument alone doesn't work. The shadow EC
  (transition table conflict) is ESSENTIAL.

  OK so let me re-examine: the shadow EC says that the transition table
  entries from the good cycle CONFLICT with entries needed if the shadow
  cycle were also a good cycle. This means the shadow can't be a second
  good cycle. But why does that matter?

  It matters because: if the shadow cycle existed as a second good cycle
  under the same transition functions, the system would fail convergence
  (two separate good cycles, some configs would cycle in one forever).
  The shadow EC prevents this. But we need to show that NO transition
  functions can support the good cycle while also ensuring convergence.

  Actually, the shadow EC doesn't directly block the good cycle. It blocks
  the good cycle + shadow from coexisting. But the good cycle alone is fine.

  WAIT. Let me re-read what was found: the "shadow EC" is a conflict
  between good-cycle entries and shadow-cycle entries AT THE SAME proc and
  context. This means: if a system has the good cycle, its transition
  function f_b(L, 1-S, R) = 1-S. At the shadow config, b's value is 1-S,
  neighbors are L, R (unchanged because they're not shifted). So at the
  shadow config, b is NOT privileged (f_b returns current value). This
  is not a contradiction -- it just means b doesn't fire at the shadow config.

  So what IS the obstruction?

  Let me go back to basics. The obstruction needs to show that no valid
  system (satisfying all 5 Dijkstra properties) can have THIS good cycle
  with THESE state counts. Let me check directly: can a system with
  ms=[2,2,3,3,2,3,3] have a sweep good cycle with non-consecutive binary?
"""
from itertools import combinations, product as iproduct
from collections import Counter
import time
import sys
sys.path.insert(0, '.')
from verifier import verify_system, all_configs, privileged_set, apply_move


def total_displacement(word, n):
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None
    return disp


def enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=120):
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    def dfs(word, fc):
        if time.time() - t0 > timeout: return
        if len(results) >= max_results: return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n-1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results: break
        fc = [0]*n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)
    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def build_configs_all_trans(word, ms, n):
    L = len(word)
    wl = list(word)
    bins = {p for p in range(n) if ms[p] == 2}
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)
    results = []
    for trans_bits in range(1 << n_tern):
        trans_dir = {}
        for p in bins:
            trans_dir[p] = 1
        for idx, p in enumerate(ternary):
            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1
        configs = [[0]*n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + trans_dir[p]) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        config_set = set(tuple(c) for c in configs[:L])
        if len(config_set) != L:
            continue
        results.append((trans_dir.copy(), [tuple(c) for c in configs[:L]]))
    return results


def try_complete_system(word, configs, ms, n, trans_dir):
    """Try to build a valid system that has the given good cycle.

    Approach: the good cycle determines some entries of the transition tables.
    Try to complete the tables and verify convergence.
    """
    L = len(word)

    # Build partial transition tables from the good cycle
    tables = {}
    for p in range(n):
        tables[p] = {}  # (L,S,R) -> output

    for t in range(L):
        p = word[t]
        c = configs[t]
        c_next = configs[(t+1)%L]
        lsr = (c[(p-1)%n], c[p], c[(p+1)%n])
        tables[p][lsr] = c_next[p]  # mover: output is new value

        # Non-mover: output is current value
        for j in range(n):
            if j == p:
                continue
            lsr_j = (c[(j-1)%n], c[j], c[(j+1)%n])
            tables[j][lsr_j] = c[j]  # stays same

    # Count forced entries
    total_possible = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
    forced = sum(len(tables[p]) for p in range(n))

    # For unforced entries: try all completions via exhaustive search
    # This is only feasible for small state spaces
    total_configs = 1
    for m in ms:
        total_configs *= m

    if total_configs > 2000:
        return None, forced, total_possible, "too large"

    # Identify unforced entries
    unforced = []
    for p in range(n):
        for L_val in range(ms[(p-1)%n]):
            for S_val in range(ms[p]):
                for R_val in range(ms[(p+1)%n]):
                    lsr = (L_val, S_val, R_val)
                    if lsr not in tables[p]:
                        # Possible outputs for this entry
                        possible = list(range(ms[p]))
                        unforced.append((p, lsr, possible))

    print(f"    Forced: {forced}/{total_possible}, "
          f"Unforced: {len(unforced)}")

    if len(unforced) > 20:
        return None, forced, total_possible, "too many unforced"

    # Try random completions
    import random
    for attempt in range(1000):
        # Random completion
        test_tables = {p: dict(tables[p]) for p in range(n)}
        for p, lsr, possible in unforced:
            test_tables[p][lsr] = random.choice(possible)

        # Build transition functions
        fs = []
        for p in range(n):
            table = test_tables[p]
            def make_f(tab):
                def f(L, S, R):
                    return tab[(L, S, R)]
                return f
            fs.append(make_f(table))

        # Verify
        result = verify_system(ms, fs, verbose=False)
        if result['valid']:
            return True, forced, total_possible, "valid system found!"

    return False, forced, total_possible, "no valid completion in 1000 tries"


def main():
    print("RA16j: Standalone Analysis — Can the good cycle be realized?")
    print("="*70)

    # Test at n=7 with the specific no-EC sweep
    n = 7
    ms = [2, 2, 3, 3, 2, 3, 3]
    print(f"\nn={n}, ms={ms}")

    words = enumerate_words_dfs(n, ms, sum(ms), max_results=50000, timeout=60)
    unique_words = {}
    for w in words:
        c = canonicalize(w)
        if c not in unique_words:
            unique_words[c] = w

    sweep_words = [w for w in unique_words.values()
                   if total_displacement(list(w), n) is not None
                   and abs(total_displacement(list(w), n)) >= 2*n]

    print(f"Sweep words: {len(sweep_words)}")

    for w in sweep_words[:1]:
        print(f"\n  word = {list(w)}")
        cycles = build_configs_all_trans(w, ms, n)
        for trans_dir, configs in cycles[:4]:  # first 4 transition combos
            print(f"\n  trans_dir = {trans_dir}")
            found, forced, total, msg = try_complete_system(
                w, configs, ms, n, trans_dir)
            print(f"  Result: {msg}")
            if found:
                print(f"  *** SYSTEM FOUND! This good cycle CAN be realized! ***")
            elif found is False:
                print(f"  No valid completion found — good cycle likely unrealizable")


if __name__ == '__main__':
    main()
