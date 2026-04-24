#!/usr/bin/env python3
"""
ra14_turnaround_proof.py — Prove EC via turnaround structure.

KEY INSIGHT: An odd-winding non-uniform word has both CW and CCW steps.
A "turnaround" is where the walk reverses direction: ...p-1, p, p-1... or ...p+1, p, p+1...
At a turnaround at position p: word[t-1] = p-1, word[t] = p, word[t+1] = p-1 (or symmetric).

At a turnaround: the walk visits p and then immediately returns to the neighbor it came from.
This means p fires at step t, and at step t+1 the walk is at the same neighbor as step t-1.

CLAIM: At a turnaround at binary p (fires at step t):
- pfc_p(t) = some value v
- pfc_p(t+1) = v+1 (just fired)
- The walk next visits p-1 (or p+1), so pfc_{p-1}(t+1) increments.
- Later, p fires again at step t'. Between t and t': the walk goes away and comes back.

The non-uniform + odd-winding constraint means turnarounds exist.
At a turnaround at p: the walk creates a specific pfc pattern.

Let me check: does every OW-NU word have a turnaround at a BINARY processor?
And does that turnaround create a forced EC?
"""
import time
from itertools import combinations
from collections import Counter


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def gen_words(n, fc_target, max_results=500, timeout_s=15):
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
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


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def check_structural_ec(word, n, ms):
    L = len(word)
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        pfc_lp = [0] * (L + 1)
        pfc_p = [0] * (L + 1)
        pfc_rp = [0] * (L + 1)
        for t in range(L):
            pfc_lp[t + 1] = pfc_lp[t] + (1 if word[t] == lp else 0)
            pfc_p[t + 1] = pfc_p[t] + (1 if word[t] == p else 0)
            pfc_rp[t + 1] = pfc_rp[t] + (1 if word[t] == rp else 0)
        mover_steps = [t for t in range(L) if word[t] == p]
        nonmover_steps = [t for t in range(L) if word[t] != p]
        for s1 in mover_steps:
            for s2 in nonmover_steps:
                if (pfc_lp[s1] % ms[lp] == pfc_lp[s2] % ms[lp] and
                    pfc_p[s1] % ms[p] == pfc_p[s2] % ms[p] and
                    pfc_rp[s1] % ms[rp] == pfc_rp[s2] % ms[rp]):
                    return True, p, s1, s2
    return False, -1, -1, -1


def find_turnarounds(word, n):
    """Find all turnaround positions (where walk reverses direction)."""
    L = len(word)
    turnarounds = []
    for t in range(L):
        prev = word[(t - 1) % L]
        curr = word[t]
        nxt = word[(t + 1) % L]
        # Turnaround: came from one side, go back to same side
        if prev == nxt and prev != curr:
            turnarounds.append(t)
    return turnarounds


def main():
    print("RA14: Turnaround-based EC Proof")
    print("=" * 70)

    # Analysis 1: Do all OW-NU words have turnarounds? Where?
    print("\nAnalysis 1: Turnaround existence and location")
    print("-" * 50)

    for n in [5, 7]:
        threshold = 4 * (3 ** (n - 2))
        total = 0
        has_binary_ta = 0
        has_ternary_ta = 0
        has_any_ta = 0
        ta_at_binary_counter = Counter()

        for bins in combinations(range(n), 3):
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            fc_target = list(ms)
            words = gen_words(n, fc_target, max_results=300, timeout_s=8)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue

                total += 1
                tas = find_turnarounds(wl, n)
                if tas:
                    has_any_ta += 1
                binary_tas = [t for t in tas if ms[wl[t]] == 2]
                ternary_tas = [t for t in tas if ms[wl[t]] == 3]
                if binary_tas:
                    has_binary_ta += 1
                if ternary_tas:
                    has_ternary_ta += 1
                ta_at_binary_counter[len(binary_tas)] += 1

        print(f"\n  n={n}: {total} OW-NU words")
        print(f"  With any turnaround: {has_any_ta} ({100*has_any_ta/total:.1f}%)")
        print(f"  With binary turnaround: {has_binary_ta} ({100*has_binary_ta/total:.1f}%)")
        print(f"  With ternary turnaround: {has_ternary_ta} ({100*has_ternary_ta/total:.1f}%)")
        print(f"  Binary turnaround count distribution: {sorted(ta_at_binary_counter.items())}")

    # Analysis 2: At turnarounds, what's the EC structure?
    # Turnaround at binary p at step t: word[t]=p, word[t-1]=word[t+1]=neighbor.
    # The neighbor is visited immediately before AND after p fires.
    # So at step t-1 and t+1: the walk is at the SAME position (neighbor of p).
    # pfc_p(t-1) = pfc_p(t) - 0 = v (p hasn't fired yet at t-1 or has already been counted)
    # Wait, let me be precise:
    # pfc_p(t) = number of times p appears in word[0..t-1].
    # At step t: word[t]=p, so p fires. pfc_p(t+1) = pfc_p(t) + 1.
    # At step t-1: word[t-1]=neighbor != p. pfc_p(t-1) = pfc_p(t) (no p-fire between t-1 and t).
    # Actually pfc_p(t) counts word[0],...,word[t-1]. So pfc_p(t) is the count BEFORE step t.
    # pfc_p(t-1) counts word[0],...,word[t-2].
    # If word[t-1] != p: pfc_p(t) = pfc_p(t-1). (No p appeared at position t-1.)
    # Wait: pfc_p(t) = sum of (1 if word[s]==p else 0) for s in 0..t-1.
    # pfc_p(t) = pfc_p(t-1) + (1 if word[t-1]==p else 0).
    # Since word[t-1] = neighbor != p: pfc_p(t) = pfc_p(t-1).
    #
    # Also: word[t+1] = neighbor = word[t-1].
    # pfc_p(t+1) = pfc_p(t) + (1 if word[t]==p else 0) = pfc_p(t) + 1.
    #
    # So at step t (mover for p): pfc_p = v.
    # At step t-1 (non-mover for p): pfc_p = v. SAME pfc_p!
    # At step t+1 (non-mover for p): pfc_p = v+1. DIFFERENT pfc_p.
    #
    # For EC at (p, t vs t-1): need pfc_p(t) mod m_p == pfc_p(t-1) mod m_p. YES (both = v mod m_p).
    # Also need pfc_L(t) mod m_L == pfc_L(t-1) mod m_L.
    # pfc_L(t) = pfc_L(t-1) + (1 if word[t-1]==L else 0).
    # word[t-1] = neighbor of p. If neighbor = L: pfc_L(t) = pfc_L(t-1) + 1. DIFFERENT.
    # If neighbor = R: pfc_L(t) = pfc_L(t-1). SAME.
    #
    # Similarly for R: pfc_R(t) = pfc_R(t-1) + (1 if word[t-1]==R else 0).
    # If neighbor = L: pfc_R(t) = pfc_R(t-1). SAME.
    # If neighbor = R: pfc_R(t) = pfc_R(t-1) + 1. DIFFERENT.
    #
    # CASE 1: Turnaround from L (word[t-1]=word[t+1]=L).
    #   pfc_p: same (v). pfc_L: different (+1). pfc_R: same.
    #   EC iff pfc_L(t) mod m_L == pfc_L(t-1) mod m_L, i.e., (pfc_L(t-1)+1) mod m_L == pfc_L(t-1) mod m_L.
    #   This requires 1 mod m_L == 0, i.e., m_L divides 1. IMPOSSIBLE for m_L >= 2.
    #   So turnaround t vs t-1 does NOT give EC!
    #
    # CASE 2: Turnaround from R (word[t-1]=word[t+1]=R).
    #   Similarly: pfc_R differs by 1 -> no EC for t vs t-1.
    #
    # So the ADJACENT step pair at a turnaround never gives EC.
    # But the turnaround creates a specific structure that may force EC elsewhere.

    print(f"\n{'='*70}")
    print("Analysis 2: Turnaround vs EC location")
    print("At turnarounds: t-1 can't match t (neighbor pfc differs by 1).")
    print("But: does the turnaround structure force EC at SOME other pair?")
    print("-" * 50)

    # New idea: look at the SECOND fire at the turnaround processor.
    # If binary p has turnaround at t1 (first fire) and fires again at t2:
    # The walk left p, went away, came back at t2.
    # Between t1 and t2: left neighbor L was visited delta_L times, R visited delta_R times.
    # At t1 (mover): pfc = (a_L, v, a_R)
    # At t2 (mover): pfc = (a_L + delta_L, v+1, a_R + delta_R)
    # Residues: (a_L mod m_L, v mod 2, a_R mod m_R) vs ((a_L+dL) mod m_L, (v+1) mod 2, (a_R+dR) mod m_R)
    #
    # For EC between t1 and t2: need all 3 to match.
    # v mod 2 vs (v+1) mod 2: DIFFERENT. So t1 and t2 can't match (both movers anyway).
    #
    # What about matching t1 (mover) with some non-mover step at pfc_p = v mod 2?
    # Need to find a non-mover step with same (pfc_L mod m_L, v mod 2, pfc_R mod m_R).

    # The key: how many non-mover steps have pfc_p mod 2 = v mod 2?
    # And what (pfc_L, pfc_R) mod (m_L, m_R) values do they cover?

    # Alternative approach: consider the turnaround step t and step t+1 (both non-movers for p, wait
    # step t is a mover for p). Let me reconsider.

    # Actually, at the turnaround: word[t-1] = word[t+1] = neighbor.
    # So t+1 is a non-mover step for p (word[t+1] = neighbor != p).
    # Compare t (mover) with t+1 (non-mover):
    # pfc_p(t) = v, pfc_p(t+1) = v+1. Different mod 2. No match.
    #
    # Compare t (mover) with t-1 (non-mover):
    # pfc_p(t) = pfc_p(t-1) = v. SAME. But neighbor pfc differs by 1.
    #
    # Compare t (mover) with t+2 (non-mover, where word[t+2]=p or next position):
    # word[t+1] = neighbor = L or R.
    # word[t+2] = ?: could be back to p (if walk oscillates) or continue further.
    #
    # If word[t+2] = p: that's the SECOND fire at p! Then:
    # pfc_p(t+2) = v+1. Different from v. No match at pfc_p.
    #
    # Hmm. Adjacent-step matching seems hard.

    # KEY REALIZATION: We should look at GLOBAL structure, not just near turnarounds.
    # The turnaround creates a specific constraint on the PFC trajectory.
    # The OW-NU constraint (|winding|=n, mixed directions) imposes a GLOBAL constraint.

    # Let me try a different decomposition: think about the walk as a sequence of
    # "runs" (maximal CW or CCW segments). Non-uniform means >= 2 runs.
    # Odd winding means net displacement = +-n.

    # Each run visits a consecutive sequence of positions.
    # The total CW displacement - total CCW displacement = +-n.
    # With CL = 3n-3 steps and net = n: CW = (3n-3+n)/2 = (4n-3)/2 steps CW,
    # CCW = (3n-3-n)/2 = (2n-3)/2 steps CCW. For n=5: CW=8.5... not integer!
    # Actually n is odd: (4*5-3)/2 = 17/2 = 8.5. Not integer.
    # But CL = 12 and net = +-5. So CW+CCW=12, CW-CCW=+-5.
    # CW=(12+5)/2=8.5 or CW=(12-5)/2=3.5. Not integer!

    # Wait, that can't be right. Let me recount.
    # For n=5, ms=[2,2,3,2,3]: CL = 2+2+3+2+3 = 12. Net displacement = +-5.
    # Each CW step adds +1, each CCW step adds -1.
    # CW - CCW = +-5, CW + CCW = 12.
    # For net=+5: CW=8.5. IMPOSSIBLE.
    # For net=-5: CW=3.5. IMPOSSIBLE.

    # This means: with 12 steps and net +-5, it's IMPOSSIBLE?!
    # But RA13 found words! Let me check...

    # Oh wait: "displacement" for a ring walk isn't just +-1 per step counted linearly.
    # On a ring of size n, the displacement wraps around.
    # total_displacement measures the WINDING number, not just sum of steps.
    # A step from position n-1 to 0 is CW (+1), not a jump of -(n-1).

    # So the signed step is always +1 or -1 (CW/CCW), and the WINDING is
    # W = sum of signed steps. But on a ring: walking CW n steps = one full loop = winding n.
    # Odd winding: W = +-n.

    # CW+CCW = CL = 12. |CW-CCW| = |W| = 5. CW = (12+5)/2 = 8.5???
    # That's not an integer. So W can't be exactly 5 with CL=12.

    # BUT: the displacement function in the code is more nuanced. Let me check.
    # Actually my mistake: the "winding" is W = n, but the walk is on positions 0..n-1
    # with +-1 steps mod n. The "total displacement" as computed in the code
    # sums signed differences. A CW step from p to p+1 counts as +1.
    # A CCW step from p to p-1 counts as -1.
    # After CL steps returning to start: W = sum of signed steps = multiple of n.
    # Odd winding = |W| = n (exactly one loop).

    # With CL = 12, n = 5: CW - CCW = +-5. CW + CCW = 12.
    # CW = (12+5)/2 = 8.5 or (12-5)/2 = 3.5. NOT INTEGER.

    # So... OW-NU words with CL=12 and n=5 should NOT EXIST?
    # But RA13 found 280 of them. Let me re-examine.

    print(f"\n{'='*70}")
    print("SANITY CHECK: CW/CCW step counts")
    for n in [5]:
        threshold = 4 * (3 ** (n - 2))
        for bins in list(combinations(range(n), 3))[:1]:
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            fc_target = list(ms)
            words = gen_words(n, fc_target, max_results=50, timeout_s=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            count = 0
            for w in list(unique.values()):
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue
                count += 1
                if count > 5:
                    break

                cw = sum(1 for d in dirs if d == 1)
                ccw = sum(1 for d in dirs if d == -1)
                stay = sum(1 for d in dirs if d == 0)
                print(f"  word={wl}, W={W}, CW={cw}, CCW={ccw}, stay={stay}, dirs={dirs}")


if __name__ == '__main__':
    main()
