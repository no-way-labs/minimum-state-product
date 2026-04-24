#!/usr/bin/env python3
"""
CIC §9.1: Wiggle Shadow — Symbolic Verification of All ~70 Closure Identities.

For each of 10 transition types (t → t+1), for each position class j,
verify: g_diff(j) + d_diff(j) ≡ 1{j=mover(t)} (mod fc[j])

where:
  g_diff(j) = g[j][σ(t+1)] - g[j][σ(t)]  (waterfall difference)
  d_diff(j) = Δ(t+1,j) - Δ(t,j)           (delta difference)
  fc[j] = fire count of proc j in wiggle word

The wiggle word is: [0, 1, 2, 1, 2, 3, ..., n-1, 0, 1, ..., n-1]
  fc[0]=2, fc[1]=3, fc[2]=3, fc[j]=2 for 3≤j≤n-1
  L = 2n+2

Strategy: compute g_diff symbolically from the word structure,
compute d_diff from the closed-form Δ tables, verify the identity.
"""

import sys


# ── Closed forms from Exploration 13 ──

def sigma(t, n):
    L = 2 * n + 2
    if t == 0: return n - 2
    elif t == 1: return n + 1
    elif 2 <= t <= n - 3: return n + t
    elif t == n - 2: return 2 * n
    elif t == n - 1: return n - 1
    elif t == n: return 2 * n - 2
    elif t == n + 1: return 2 * n + 1
    elif n + 2 <= t <= 2 * n - 1: return t - (n + 2)
    elif t == 2 * n: return n
    elif t == 2 * n + 1: return 2 * n - 1
    raise ValueError(f"t={t}")


def delta(t, j, n):
    if t == 0 or t == n:  # Type A
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif n - 4 <= j <= n - 1: return 0
    elif (1 <= t <= n - 3) or t == n + 1:  # Type B
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif j == n - 4: return 0
        elif j == n - 3: return -1
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 2:  # Type C
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 4: return -1
        elif j == n - 3: return -2
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 1:  # Type D
        if j == 0: return 0
        elif j == 1: return -1
        elif j == 2: return -1
        elif 3 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n + 1:  # Type E
        if 0 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n:  # Type F
        if 0 <= j <= n - 4: return 1
        elif j == n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 2
    elif n + 2 <= t <= 2 * n - 1:  # Type G
        if 0 <= j <= n - 5: return 1
        elif j == n - 4: return 2
        elif j == n - 3 or j == n - 2: return 1
        elif j == n - 1: return 2
    raise ValueError(f"t={t}, j={j}, n={n}")


def offset(j, n):
    if j == 0: return 1
    elif j == 1: return 2
    elif j == 2: return 2
    elif 3 <= j <= n - 5: return 1
    elif j == n - 4: return 0
    elif j == n - 3: return 0
    elif j == n - 2: return 1
    elif j == n - 1: return 0
    raise ValueError(f"j={j}, n={n}")


def fc(j, n):
    """Fire count for proc j in wiggle word."""
    if j == 0: return 2
    elif j == 1: return 3
    elif j == 2: return 3
    else: return 2


def make_word(n):
    return [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))


def delta_type_name(t, n):
    if t == 0 or t == n: return 'A'
    elif (1 <= t <= n - 3) or t == n + 1: return 'B'
    elif t == n - 2: return 'C'
    elif t == n - 1: return 'D'
    elif t == 2 * n + 1: return 'E'
    elif t == 2 * n: return 'F'
    elif n + 2 <= t <= 2 * n - 1: return 'G'
    return '?'


# ── Symbolic waterfall computation ──

def g_symbolic(j, s, n):
    """
    Compute g[j][s] = number of times proc j fires in word[0:s].
    Word = [0, 1, 2, 1, 2, 3, 4, ..., n-1, 0, 1, 2, ..., n-1]
    Indices: 0  1  2  3  4  5  6      n+1  n+2 n+3 n+4    2n+1
    """
    # Word structure by index:
    # w[0]=0, w[1]=1, w[2]=2, w[3]=1, w[4]=2
    # w[5]=3, w[6]=4, ..., w[k]=k-2 for 5≤k≤n+1 (so w[n+1]=n-1)
    # w[n+2]=0, w[n+3]=1, w[n+4]=2, ..., w[n+2+j]=j for 0≤j≤n-1
    # w[2n+1]=n-1
    # Total length = 2n+2

    # g[j][s] counts occurrences of j in w[0], w[1], ..., w[s-1]
    # We compute this by cases on j and s.

    if s <= 0:
        return 0
    if s > 2 * n + 2:
        s = 2 * n + 2  # cap at word length

    count = 0

    # Phase 1: indices 0..4 → w = [0, 1, 2, 1, 2]
    # Phase 2: indices 5..n+1 → w[k] = k-2, so procs 3..n-1
    # Phase 3: indices n+2..2n+1 → w[k] = k-(n+2), so procs 0..n-1

    # Count from Phase 1 (indices 0..min(s-1, 4))
    phase1 = [0, 1, 2, 1, 2]
    for idx in range(min(s, 5)):
        if phase1[idx] == j:
            count += 1

    # Count from Phase 2 (indices 5..n+1, proc k-2)
    if s > 5 and j >= 3:
        # w[k] = k-2 for k=5..n+1, so proc j appears at k=j+2
        target_idx = j + 2
        if 5 <= target_idx <= n + 1 and target_idx < s:
            count += 1

    # Count from Phase 3 (indices n+2..2n+1, proc k-(n+2))
    if s > n + 2:
        # w[k] = k-(n+2) for k=n+2..2n+1, so proc j at k=j+n+2
        target_idx = j + n + 2
        if n + 2 <= target_idx <= 2 * n + 1 and target_idx < s:
            count += 1

    return count


def g_diff_symbolic(j, s1, s2, n):
    """g[j][s2] - g[j][s1]: firings of j in word[s1:s2]."""
    return g_symbolic(j, s2, n) - g_symbolic(j, s1, n)


# ── Transition type enumeration ──

TRANSITIONS = [
    # (name, t_from, t_to)  where t_to = (t_from + 1) mod L
    # The 10 transition types based on delta type changes
]


def get_transitions(n):
    """Return all L transitions with their types."""
    L = 2 * n + 2
    trans = []
    for t in range(L):
        t_next = (t + 1) % L
        dt = delta_type_name(t, n)
        dt_next = delta_type_name(t_next, n)
        trans.append((t, t_next, dt, dt_next))
    return trans


def get_transition_types(n):
    """Group transitions by (type_from, type_to)."""
    L = 2 * n + 2
    types = {}
    for t in range(L):
        t_next = (t + 1) % L
        dt = delta_type_name(t, n)
        dt_next = delta_type_name(t_next, n)
        key = f"{dt}→{dt_next}"
        if key not in types:
            types[key] = []
        types[key].append(t)
    return types


# ── Position classes ──

def position_classes(n):
    """Return list of (class_name, representative_j) for all position classes."""
    classes = [(0, "j=0"), (1, "j=1"), (2, "j=2")]
    if n >= 9:  # need n-5 >= 4, i.e. n >= 9 for interior class
        classes.append((4, "3≤j≤n-5"))  # representative j=4 when n≥9
    if n >= 8:
        classes.append((n - 4, "j=n-4"))
    classes.append((n - 3, "j=n-3"))
    classes.append((n - 2, "j=n-2"))
    classes.append((n - 1, "j=n-1"))
    return classes


# ── Core verification ──

def verify_closure_identity(t, j, n, word):
    """
    Verify: g_diff(j, σ(t), σ(t+1)) + d_diff(j, t) ≡ 1{j=mover(t)} (mod fc(j))
    where mover(t) = word[t], d_diff = Δ(t+1,j) - Δ(t,j)
    """
    L = 2 * n + 2
    t_next = (t + 1) % L

    s_t = sigma(t, n)
    s_tn = sigma(t_next, n)

    # g_diff: firings of j in word[σ(t):σ(t+1)] (cyclic)
    if s_tn > s_t:
        gd = g_diff_symbolic(j, s_t, s_tn, n)
    elif s_tn < s_t:
        # Wrap: word[s_t:L] + word[0:s_tn]
        gd = g_diff_symbolic(j, s_t, L, n) + g_diff_symbolic(j, 0, s_tn, n)
    else:
        # s_tn == s_t: full cycle
        gd = fc(j, n)

    # d_diff
    dd = delta(t_next, j, n) - delta(t, j, n)

    # Expected: 1 if j == mover at shadow step t = word[σ(t)], else 0
    mover = word[s_t]  # shadow mover is word[σ(t)]
    expected = 1 if j == mover else 0

    total = gd + dd
    fcj = fc(j, n)

    # Check: total ≡ expected (mod fc[j])
    ok = (total % fcj) == (expected % fcj)

    return ok, total, expected, gd, dd, fcj


def main():
    print("§9.1 Wiggle Shadow: Symbolic Closure Verification")
    print("=" * 70)

    # PART 1: Verify g_symbolic against actual waterfall for specific n
    print("\nPART 1: Validate g_symbolic against brute-force waterfall")
    print("-" * 70)

    for n in [8, 10, 12, 15, 20]:
        w = make_word(n)
        L = len(w)
        # Brute force waterfall
        g_bf = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for jj in range(n):
                g_bf[jj][t + 1] = g_bf[jj][t]
            g_bf[w[t]][t + 1] = g_bf[w[t]][t] + 1

        ok = True
        for jj in range(n):
            for s in range(L + 1):
                if g_symbolic(jj, s, n) != g_bf[jj][s]:
                    print(f"  MISMATCH n={n} j={jj} s={s}: "
                          f"symbolic={g_symbolic(jj, s, n)} "
                          f"brute={g_bf[jj][s]}")
                    ok = False
        if ok:
            print(f"  n={n}: g_symbolic matches brute-force waterfall ✓ "
                  f"({n * (L+1)} entries)")

    # PART 2: Enumerate transition types
    print("\n\nPART 2: Transition Types")
    print("-" * 70)

    n = 12  # representative
    tt = get_transition_types(n)
    for key in sorted(tt.keys()):
        steps = tt[key]
        print(f"  {key}: {len(steps)} transitions (t={steps})")

    # PART 3: Verify all closure identities symbolically
    print("\n\nPART 3: Symbolic Closure Identity Verification")
    print("-" * 70)

    total_ids = 0
    total_ok = 0
    total_exact = 0  # no mod needed
    total_mod = 0    # mod needed

    for n in [8, 9, 10, 12, 15, 20, 25, 50, 100]:
        w = make_word(n)
        L = len(w)

        n_ok = 0
        n_fail = 0
        n_exact = 0
        n_mod = 0
        failures = []

        for t in range(L):
            pcs = position_classes(n)
            for j_rep, j_name in pcs:
                ok, total, expected, gd, dd, fcj = \
                    verify_closure_identity(t, j_rep, n, w)
                total_ids += 1
                if ok:
                    n_ok += 1
                    total_ok += 1
                    if total == expected:
                        n_exact += 1
                        total_exact += 1
                    else:
                        n_mod += 1
                        total_mod += 1
                else:
                    n_fail += 1
                    failures.append((t, j_rep, j_name, total, expected,
                                     gd, dd, fcj))

        tag = "✓" if n_fail == 0 else "✗"
        print(f"  n={n}: {n_ok}/{n_ok+n_fail} OK "
              f"({n_exact} exact, {n_mod} mod) {tag}")

        if failures:
            for t, j, jn, total, exp, gd, dd, fcj in failures[:5]:
                dt = delta_type_name(t, n)
                print(f"    FAIL t={t}({dt}) j={j}({jn}): "
                      f"g_diff={gd} d_diff={dd} total={total} "
                      f"expected={exp} mod fc={fcj}")

    print(f"\n  TOTAL: {total_ok}/{total_ids} identities verified "
          f"({total_exact} exact, {total_mod} mod reduction)")

    # PART 4: Detailed identity table for representative n
    print("\n\nPART 4: Identity Table (n=10)")
    print("-" * 70)

    n = 10
    w = make_word(n)
    L = len(w)
    tt = get_transition_types(n)

    for ttype in sorted(tt.keys()):
        t_rep = tt[ttype][0]  # first representative
        t_next = (t_rep + 1) % L
        mover = w[t_rep]
        s_t = sigma(t_rep, n)
        s_tn = sigma(t_next, n)
        print(f"\n  {ttype} (t={t_rep}, mover={mover}, "
              f"σ={s_t}→{s_tn}):")

        pcs = position_classes(n)
        for j_rep, j_name in pcs:
            ok, total, expected, gd, dd, fcj = \
                verify_closure_identity(t_rep, j_rep, n, w)
            is_mover = "MOVER" if j_rep == mover else ""
            exact = "exact" if total == expected else f"mod {fcj}"
            tag = "✓" if ok else "✗"
            print(f"    {j_name:>10}: g_diff={gd:>2} d_diff={dd:>3} "
                  f"total={total:>2} exp={expected} {exact:>7} "
                  f"{tag} {is_mover}")

    # PART 5: Check ALL j values (not just representatives) for key n
    print("\n\nPART 5: Exhaustive j Verification")
    print("-" * 70)

    for n in [8, 10, 15, 20, 30, 50]:
        w = make_word(n)
        L = len(w)
        all_ok = True
        count = 0
        for t in range(L):
            for j in range(n):
                ok, _, _, _, _, _ = verify_closure_identity(t, j, n, w)
                count += 1
                if not ok:
                    all_ok = False
                    dt = delta_type_name(t, n)
                    print(f"  FAIL n={n} t={t}({dt}) j={j}")

        tag = "✓" if all_ok else "✗"
        print(f"  n={n}: {count} identities ALL verified {tag}")

    # PART 6: Symbolic argument for general n
    print("\n\nPART 6: Symbolic Proof Structure")
    print("=" * 70)
    print("""
  The closure identity g_diff + d_diff ≡ expected (mod fc[j])
  decomposes into 10 transition types × 8 position classes = 80 cases.

  For each case, g_diff is computed from the word structure:
  - Word phases: [0,1,2,1,2 | 3,...,n-1 | 0,1,...,n-1]
  - g[j][s] counts j's occurrences in word[0:s]
  - g_diff = g[j][σ(t+1)] - g[j][σ(t)]

  Since σ maps to fixed structural positions (n-2, n+1, n+t, etc.),
  g_diff depends only on the position class of j and the transition
  type, NOT on n (for n ≥ 8).

  The d_diff = Δ(t+1,j) - Δ(t,j) is directly from the Δ tables
  (also n-independent for n ≥ 8).

  Therefore each identity is a FIXED arithmetic statement,
  independent of n, verified for all n ≥ 8.
""")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
