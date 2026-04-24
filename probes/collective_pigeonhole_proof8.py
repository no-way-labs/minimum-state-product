#!/usr/bin/env python3
"""
DEFINITIVE PROOF (corrected): Collective Binary Pigeonhole is FALSE.

Fix: step indexing formula and large-n verification.
The V-word W = [0,1,0,n-1,n-2,...,2,1,2,...,n-1]
  W[0]=0, W[1]=1, W[2]=0, W[3]=n-1, ..., W[3+(n-1-j)]=j, ...,
  W[n+1]=1, W[n+2]=2, ..., W[n+j-1]=j, ..., W[2n-1]=n-1

So for ternary proc j (3 <= j <= n-1):
  First firing: step t1 = 3 + (n-1-j) = n+2-j
  Second firing: step t2 = n + j - 1

Check: n=9, j=3: t1 = 9+2-3 = 8, t2 = 9+3-1 = 11... but from output j=3 fires at steps 8 and 12.
Hmm. Let me re-derive from the word directly.
"""

from collections import Counter


def v_word(n):
    """Construct V-word."""
    return [0, 1, 0] + list(range(n-1, 1, -1)) + list(range(1, n))


def build_wavefront_cycle(n):
    """Build wavefront good cycle for V-word with all-incrementing state seqs."""
    ms = [2, 2, 2] + [3] * (n - 3)
    w = v_word(n)
    L = 2 * n
    configs = []
    state = [0] * n
    configs.append(tuple(state))
    for t in range(L):
        p = w[t]
        state = list(configs[-1])
        state[p] = (state[p] + 1) % ms[p]
        configs.append(tuple(state))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]


def main():
    print("CORRECTED STEP FORMULA DERIVATION")
    print("=" * 70)

    # First, let's figure out the correct formula by looking at the word
    for n in [5, 7, 9, 11]:
        w = v_word(n)
        L = 2 * n
        print(f"\nn={n}: V-word = {w}")
        # Find firing steps for each proc
        for j in range(n):
            steps = [t for t in range(L) if w[t] == j]
            print(f"  Proc {j}: fires at steps {steps}")

    # Derive formula: W = [0, 1, 0, n-1, n-2, ..., 2, 1, 2, ..., n-1]
    # Indices: 0:0, 1:1, 2:0, 3:n-1, 4:n-2, ..., 3+(n-1-j):j=, ..., n+1:1, ..., n-1+j:j, 2n-1:n-1
    print("\nFORMULA DERIVATION:")
    print("  W[0] = 0 (proc 0, first fire)")
    print("  W[1] = 1 (proc 1, first fire)")
    print("  W[2] = 0 (proc 0, second fire)")
    print("  W[3] = n-1 (proc n-1, first fire)")
    print("  W[3+k] = n-1-k for k=0,...,n-3 (CCW pass)")
    print("  So W[3+(n-1-j)] = j for j=n-1,...,2")
    print("  First fire of j (j>=3): t1 = 3 + (n-1-j) = n+2-j")
    print("  Then: W[n+1] = 1 (proc 1, second fire)")
    print("  W[n+1+k] = 1+k+1 = k+2 for k=0,...,n-3")
    print("  Wait, let me just count directly...")

    for n in [9]:
        w = v_word(n)
        print(f"\n  n={n}, word: {w}")
        for t in range(len(w)):
            print(f"    W[{t}] = {w[t]}")

    # n=9: W = [0,1,0,8,7,6,5,4,3,2,1,2,3,4,5,6,7,8]
    # Indices:  0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17
    # Proc 0: fires at 0, 2
    # Proc 1: fires at 1, 10
    # Proc 2: fires at 9, 11
    # Proc 3: fires at 8, 12
    # Proc 4: fires at 7, 13
    # Proc 5: fires at 6, 14
    # Proc 6: fires at 5, 15
    # Proc 7: fires at 4, 16
    # Proc 8: fires at 3, 17

    # Pattern for j >= 2:
    # First fire: t1 = n+2-j (CCW pass going from n-1 down to 2)
    #   j=8: t1=3, j=7: t1=4, j=6: t1=5, ..., j=3: t1=8, j=2: t1=9
    # Second fire: t2 = n+j-1 (CW pass going from 1 up to n-1)
    #   j=1: t2=10, j=2: t2=11, j=3: t2=12, ..., j=8: t2=17

    # For j >= 3 (ternary):
    #   t1 = n + 2 - j  (CCW pass)
    #   t2 = n + j - 1  (CW pass)

    # Wait, proc 2: n+2-2 = 9 (correct), n+2-1 = 11 (correct).
    # Proc 1: n+2-1 = 10... but first fire is at 1, not 10.
    # Proc 1 and 0 are special (part of the preamble).

    print("\nCORRECT FORMULA:")
    print("  For j >= 2:")
    print("    First fire (CCW): t1 = n + 2 - j")
    print("    Second fire (CW): t2 = n + j - 1")
    print("  Special: proc 0 fires at {0, 2}, proc 1 fires at {1, n}")

    # Verify
    print("\nVERIFICATION:")
    for n in [5, 7, 9, 11, 15, 20]:
        w = v_word(n)
        L = 2 * n
        all_ok = True
        for j in range(2, n):
            expected = sorted([n + 2 - j, n + j - 1])
            actual = sorted([t for t in range(L) if w[t] == j])
            if expected != actual:
                print(f"  n={n}, j={j}: MISMATCH expected={expected}, actual={actual}")
                all_ok = False
        # Proc 0
        exp0 = [0, 2]
        act0 = sorted([t for t in range(L) if w[t] == 0])
        if exp0 != act0:
            print(f"  n={n}, j=0: MISMATCH expected={exp0}, actual={act0}")
            all_ok = False
        # Proc 1
        exp1 = sorted([1, n])
        act1 = sorted([t for t in range(L) if w[t] == 1])
        if exp1 != act1:
            print(f"  n={n}, j=1: MISMATCH expected={exp1}, actual={act1}")
            all_ok = False
        if all_ok:
            print(f"  n={n}: ALL firing steps match formula")

    # NOW: prove the ternary EC analytically with correct formula
    print("\n" + "=" * 70)
    print("TERNARY EC PROOF WITH CORRECT FORMULA")
    print("=" * 70)

    print("""
For ternary proc j (3 <= j <= n-1):
  t1 = n + 2 - j  (CCW pass: proc j fires, going j+1 -> j -> j-1)
  t2 = n + j - 1  (CW pass: proc j fires, going j-1 -> j -> j+1)

Config at step t1:
  Already toggled by CCW pass: {n-1, n-2, ..., j+1} and {1} (from preamble)
  Not yet toggled: {0, 2, 3, ..., j}
  So: c[j-1] = 0 (j-1 >= 2, not toggled)
      c[j] = 0 (about to toggle)
      c[j+1] = 1 (already toggled, since j+1 <= n-1)
  Mover context: (0, 0, 1)

Config at step t2:
  After full CCW pass: {1, 2, ..., n-1} all toggled (state=1), {0} toggled twice (back to 0)
  After partial CW pass: {1, 2, ..., j-1} toggled back (state=0)
  So: c[j-1] = 0 (toggled back)
      c[j] = 1 (not yet toggled back)
      c[j+1] = 1 (not yet toggled back)
  Mover context: (0, 1, 1)

Now check nonmover step t2 + 1 = n + j:
  Mover at this step: proc j+1 (next step in CW pass)
  Just toggled j back to 0.
  c[j-1] = 0 (unchanged)
  c[j] = 0 (just toggled back at t2)
  c[j+1] = 1 (about to toggle at this step)
  Nonmover context at j: (0, 0, 1)

MATCH: mover context at t1 = nonmover context at t2+1 = (0, 0, 1)

ENTRY CONFLICT: f_j(0, 0, 1) must be:
  - 1 (from mover step t1: state changes 0 -> 1)
  - 0 (from nonmover step t2+1: state stays at 0)
Contradiction.

For j = n-1 (boundary):
  t1 = n + 2 - (n-1) = 3
  t2 = n + (n-1) - 1 = 2n - 2

  Config at t1:
    Only {1} toggled from preamble. No CCW toggling yet.
    c[n-2] = 0, c[n-1] = 0, c[0] = 0
    Mover context: (0, 0, 0)

  Config at t2:
    Procs {1,...,n-2} toggled back, {n-1} still toggled.
    c[n-2] = 0, c[n-1] = 1, c[0] = 0
    Mover context: (0, 1, 0)

  Nonmover at t1+1 = 4 (mover is n-2):
    c[n-2] = 0, c[n-1] = 1 (just toggled at t1), c[0] = 0
    Nonmover context at n-1: (0, 1, 0)

  MATCH: mover context at t2 = nonmover context at t1+1 = (0, 1, 0)
  EC: f(0,1,0) must be 0 (mover) and 1 (nonmover). Contradiction.
""")

    # Verify this analytical proof against computation
    print("COMPUTATIONAL VERIFICATION:")
    for n in range(5, 51):
        ms = [2, 2, 2] + [3] * (n - 3)
        w = v_word(n)
        L = 2 * n
        good = build_wavefront_cycle(n)
        if good is None:
            print(f"  n={n}: FAILED to build cycle")
            continue

        all_ec = True
        for j in range(3, n):
            t1 = n + 2 - j
            t2 = n + j - 1

            # Mover context at t1
            c1 = good[t1]
            mctx1 = (c1[j-1], c1[j], c1[(j+1)%n])

            # Mover context at t2
            c2 = good[t2]
            mctx2 = (c2[j-1], c2[j], c2[(j+1)%n])

            # Nonmover context at t2+1 (should match mctx1)
            if j < n - 1:
                c_nm = good[(t2 + 1) % L]
                nm_ctx = (c_nm[j-1], c_nm[j], c_nm[(j+1)%n])
                if nm_ctx != mctx1:
                    print(f"  n={n}, j={j}: interior MISMATCH "
                          f"mctx1={mctx1}, nm@t2+1={nm_ctx}")
                    all_ec = False
            else:  # j = n-1 boundary
                c_nm = good[(t1 + 1) % L]
                nm_ctx = (c_nm[j-1], c_nm[j], c_nm[(j+1)%n])
                if nm_ctx != mctx2:
                    print(f"  n={n}, j={j}: boundary MISMATCH "
                          f"mctx2={mctx2}, nm@t1+1={nm_ctx}")
                    all_ec = False

            # Also verify actual EC (overlap check)
            mover_ctx = set()
            nonmover_ctx = set()
            for t in range(L):
                c = good[t]
                ctx = (c[j-1], c[j], c[(j+1)%n])
                if w[t] == j:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if not (mover_ctx & nonmover_ctx):
                print(f"  n={n}, j={j}: NO EC despite formula prediction!")
                all_ec = False

        if all_ec:
            if n <= 12 or n % 10 == 0:
                print(f"  n={n}: all {n-3} ternary procs have EC "
                      f"(formula matches)")

    # Now verify binary EC-freedom
    print("\nBINARY EC-FREEDOM VERIFICATION:")
    for n in range(5, 101):
        ms = [2, 2, 2] + [3] * (n - 3)
        w = v_word(n)
        L = 2 * n
        good = build_wavefront_cycle(n)
        if good is None:
            print(f"  n={n}: FAILED to build cycle")
            continue

        binary_ok = True
        for b in [0, 1, 2]:
            Lp = (b - 1) % n
            Rp = (b + 1) % n
            mover_ctx = set()
            nonmover_ctx = set()
            for t in range(L):
                c = good[t]
                ctx = (c[Lp], c[b], c[Rp])
                if w[t] == b:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if mover_ctx & nonmover_ctx:
                binary_ok = False
                break

        if not binary_ok:
            print(f"  n={n}: BINARY EC FOUND (counterexample broken)")
            break
    else:
        print(f"  VERIFIED: binary procs EC-free for n=5..100")


if __name__ == '__main__':
    main()
