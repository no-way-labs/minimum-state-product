#!/usr/bin/env python3
"""Generate CUP-2 bad-step rank functions for Lean formalization.

Uses the EXACT table values from LeanMn/Tables.lean (TBotVal, TLowVal, TMidVal, THighVal, TTopVal).
"""

from itertools import product as cartesian
from collections import deque
import sys

# ================================================================
# CUP-2 Tables — copied exactly from LeanMn/Tables.lean
# ================================================================

def TBotVal(L, S, R):
    t = {
        (0,0,0): 1, (0,0,1): 1, (0,0,2): 0,
        (0,1,0): 1, (0,1,1): 1, (0,1,2): 1,
        (1,0,0): 0, (1,0,1): 1, (1,0,2): 0,
        (1,1,0): 0, (1,1,1): 1, (1,1,2): 0,
    }
    return t.get((L, S, R), 0)

def TLowVal(L, S, R):
    t = {
        (0,0,0): 0, (0,0,1): 0, (0,0,2): 0,
        (0,1,0): 0, (0,1,1): 1, (0,1,2): 0,
        (0,2,0): 0, (0,2,1): 2, (0,2,2): 0,
        (1,0,0): 1, (1,0,1): 1, (1,0,2): 1,
        (1,1,0): 1, (1,1,1): 1, (1,1,2): 2,
        (1,2,0): 0, (1,2,1): 1, (1,2,2): 2,
    }
    return t.get((L, S, R), 0)

def TMidVal(L, S, R):
    t = {
        (0,0,0): 0, (0,0,1): 0, (0,0,2): 0,
        (0,1,0): 0, (0,1,1): 1, (0,1,2): 0,
        (0,2,0): 0, (0,2,1): 2, (0,2,2): 0,
        (1,0,0): 1, (1,0,1): 1, (1,0,2): 1,
        (1,1,0): 1, (1,1,1): 1, (1,1,2): 2,
        (1,2,0): 0, (1,2,1): 1, (1,2,2): 2,
        (2,0,0): 0, (2,0,1): 0, (2,0,2): 2,
        (2,1,0): 1, (2,1,1): 0, (2,1,2): 2,  # liveness fix: (2,1,1) was 2 in orig table, patched to 0
        (2,2,0): 0, (2,2,1): 2, (2,2,2): 2,
    }
    return t.get((L, S, R), 0)

def THighVal(L, S, R):
    t = {
        (0,0,0): 0, (0,0,1): 0,
        (0,1,0): 0, (0,1,1): 0,
        (0,2,0): 0, (0,2,1): 0,
        (1,0,0): 1, (1,0,1): 1,
        (1,1,0): 1, (1,1,1): 2,
        (1,2,0): 0, (1,2,1): 2,
        (2,0,0): 0, (2,0,1): 2,
        (2,1,0): 0, (2,1,1): 2,
        (2,2,0): 2, (2,2,1): 2,
    }
    return t.get((L, S, R), 0)

def TTopVal(L, S, R):
    t = {
        (0,0,0): 0, (0,0,1): 0,
        (0,1,0): 0, (0,1,1): 0,
        (1,0,0): 0, (1,0,1): 1,
        (1,1,0): 1, (1,1,1): 1,
        (2,0,0): 1, (2,0,1): 1,
        (2,1,0): 1, (2,1,1): 1,
    }
    return t.get((L, S, R), 0)


def cup2_ms(n):
    """State counts for CUP-2: (2, 3, 3, ..., 3, 2)"""
    ms = [3] * n
    ms[0] = 2
    ms[n-1] = 2
    return ms


def cup2_transition(n, c, i):
    """Compute f_i(L, S, R) for config c, matching Lean's cup2TransVal."""
    ms = cup2_ms(n)
    L = c[(i - 1) % n]
    S = c[i]
    R = c[(i + 1) % n]
    if i == 0:
        return TBotVal(L, S, R)
    elif i == 1:
        return TLowVal(L, S, R)
    elif i == n - 2:
        return THighVal(L, S, R)
    elif i == n - 1:
        return TTopVal(L, S, R)
    else:
        return TMidVal(L, S, R)


def is_privileged(n, c, i):
    return cup2_transition(n, c, i) != c[i]


def move(n, c, i):
    c2 = list(c)
    c2[i] = cup2_transition(n, c, i)
    return tuple(c2)


def all_configs(n):
    ms = cup2_ms(n)
    return list(cartesian(*[range(m) for m in ms]))


def config_code(n, c):
    """Compute config code matching Lean's configCode."""
    ms = cup2_ms(n)
    code = 0
    for i in range(n):
        code = code * ms[i] + c[i]
    return code


def find_good_cycle(n):
    """Find the good cycle by stepping from all-zeros config."""
    c = tuple([0] * n)
    cycle = [c]

    for _ in range(4 * n):  # good cycle length is 3n-2
        privs = [i for i in range(n) if is_privileged(n, c, i)]
        if len(privs) != 1:
            print(f"  Config {c}: {len(privs)} privileged: {privs}")
            return None
        i = privs[0]
        c = move(n, c, i)
        if c == cycle[0]:
            return cycle  # cycle complete
        cycle.append(c)

    print(f"  Cycle didn't close after {4*n} steps")
    return None


def compute_bad_ranks(n):
    """Compute topological rank for each config in the bad-step DAG."""
    configs = all_configs(n)
    good_cycle = find_good_cycle(n)
    if good_cycle is None:
        raise ValueError(f"No good cycle found for n={n}")

    good_set = set(good_cycle)
    bad_configs = [c for c in configs if c not in good_set]

    print(f"n={n}: {len(configs)} configs, {len(good_cycle)} good, {len(bad_configs)} bad")

    # Build bad-step graph
    bad_set = set(bad_configs)
    adj = {c: [] for c in bad_configs}

    for c in bad_configs:
        for i in range(n):
            if is_privileged(n, c, i):
                c_next = move(n, c, i)
                if c_next in bad_set:
                    adj[c].append(c_next)

    # Compute rank = longest path (DFS)
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in bad_configs}
    rank = {c: 0 for c in bad_configs}

    sys.setrecursionlimit(10000)

    def dfs(u):
        color[u] = GRAY
        max_child_rank = -1
        for v in adj[u]:
            if color[v] == GRAY:
                raise ValueError(f"Cycle detected at n={n}!")
            if color[v] == WHITE:
                dfs(v)
            max_child_rank = max(max_child_rank, rank[v])
        color[u] = BLACK
        rank[u] = max_child_rank + 1

    for c in bad_configs:
        if color[c] == WHITE:
            dfs(c)

    max_rank = max(rank.values()) if rank else 0
    print(f"  Max rank: {max_rank}")

    # Build full rank array indexed by config code
    ms = cup2_ms(n)
    total = 1
    for m in ms:
        total *= m

    rank_array = [0] * total

    for c in configs:
        code = config_code(n, c)
        if c in good_set:
            rank_array[code] = 0
        elif c in rank:
            rank_array[code] = rank[c]

    return rank_array, good_cycle, max_rank


def verify_ranks(n):
    """Verify that the rank function strictly decreases on all bad steps."""
    rank_array, good_cycle, _ = compute_bad_ranks(n)
    ms = cup2_ms(n)
    configs = all_configs(n)
    good_set = set(good_cycle)

    violations = 0
    total_bad_steps = 0
    for c in configs:
        if c in good_set:
            continue
        for i in range(n):
            if is_privileged(n, c, i):
                c_next = move(n, c, i)
                if c_next in good_set:
                    continue
                total_bad_steps += 1
                c_code = config_code(n, c)
                cn_code = config_code(n, c_next)
                if rank_array[cn_code] >= rank_array[c_code]:
                    violations += 1

    print(f"  Bad steps: {total_bad_steps}, violations: {violations}")
    return violations == 0


def generate_lean_code():
    """Generate Lean code for CUP-2 convergence at small n."""

    lines = []
    lines.append("/-")
    lines.append("  SmallN/Cup2Convergence.lean — CUP-2 convergence for n = 4..10")
    lines.append("")
    lines.append("  Auto-generated by gen_cup2_ranks.py")
    lines.append("  Proves convergence of the CUP-2 system at each specific n")
    lines.append("  via a computational rank function that strictly decreases on bad steps.")
    lines.append("  For n >= 10 (>=12K configs), rank table is split into chunks to avoid")
    lines.append("  Lean elaborator stack-overflow on huge List literals.")
    lines.append("-/")
    lines.append("import LeanMn.Cycle")
    lines.append("")
    lines.append("set_option maxRecDepth 65536")
    lines.append("")
    lines.append("namespace LeanMn")
    lines.append("")
    lines.append("-- Mixed-radix config encoding (big-endian): code = ((c[0]*m[1]+c[1])*m[2]+c[2])*...")
    lines.append("private def configCode (rs : RingSpec) (c : Config rs) : Nat :=")
    lines.append("  (List.finRange rs.n).foldl (fun acc i => acc * rs.m i + (c i).val) 0")
    lines.append("")

    # Chunk threshold: for n with total >= CHUNK_THRESHOLD, split into chunks
    # to avoid stack-overflow in the Lean elaborator on large List literals.
    # n=9 has 8,748 entries and works; n=10 has 26,244 and stack-overflows.
    CHUNK_THRESHOLD = 12000  # split when total >= this
    CHUNK_SIZE = 8000         # per-chunk cap (well below n=9's 8748)

    for n in range(4, 11):
        rank_array, good_cycle, max_rank = compute_bad_ranks(n)
        ms = cup2_ms(n)
        total = len(rank_array)

        lines.append(f"/-! ### CUP-2 convergence at n = {n}, product = {total}, max rank = {max_rank} -/")
        lines.append("")

        # Named abbreviations to avoid multiple `by omega` in theorem statements
        lines.append(f"private abbrev cup2Spec{n} := cup2Spec {n} (by omega)")
        lines.append(f"private abbrev cup2Sys{n} := cup2System {n} (by omega)")
        lines.append(f"private abbrev cup2GC{n} := cup2GoodCycle {n} (by omega)")
        lines.append("")

        if total < CHUNK_THRESHOLD:
            # Single List encoding (original)
            lines.append(f"private def cup2BadRankVals{n} : List Nat :=")
            chunks = []
            for i in range(0, len(rank_array), 20):
                chunk = rank_array[i:i+20]
                chunks.append(", ".join(str(r) for r in chunk))
            if len(chunks) == 1:
                lines.append(f"  [{chunks[0]}]")
            else:
                lines.append(f"  [{chunks[0]},")
                for i in range(1, len(chunks) - 1):
                    lines.append(f"   {chunks[i]},")
                lines.append(f"   {chunks[-1]}]")
            lines.append("")

            lines.append(f"private def cup2BadRank{n} (c : Config cup2Spec{n}) : Nat :=")
            lines.append(f"  cup2BadRankVals{n}.getD (configCode cup2Spec{n} c) 0")
            lines.append("")
        else:
            # Chunked List encoding for large n
            num_chunks = (total + CHUNK_SIZE - 1) // CHUNK_SIZE
            for k in range(num_chunks):
                lo = k * CHUNK_SIZE
                hi = min(lo + CHUNK_SIZE, total)
                sub = rank_array[lo:hi]
                lines.append(f"private def cup2BadRankVals{n}_{k} : List Nat :=")
                row_chunks = []
                for i in range(0, len(sub), 20):
                    row = sub[i:i+20]
                    row_chunks.append(", ".join(str(r) for r in row))
                if len(row_chunks) == 1:
                    lines.append(f"  [{row_chunks[0]}]")
                else:
                    lines.append(f"  [{row_chunks[0]},")
                    for j in range(1, len(row_chunks) - 1):
                        lines.append(f"   {row_chunks[j]},")
                    lines.append(f"   {row_chunks[-1]}]")
                lines.append("")

            # Dispatch function
            lines.append(f"private def cup2BadRank{n} (c : Config cup2Spec{n}) : Nat :=")
            lines.append(f"  let code := configCode cup2Spec{n} c")
            for k in range(num_chunks):
                lo = k * CHUNK_SIZE
                hi = min(lo + CHUNK_SIZE, total)
                if k == 0:
                    lines.append(f"  if code < {hi} then cup2BadRankVals{n}_{k}.getD code 0")
                elif k < num_chunks - 1:
                    lines.append(f"  else if code < {hi} then cup2BadRankVals{n}_{k}.getD (code - {lo}) 0")
                else:
                    lines.append(f"  else cup2BadRankVals{n}_{k}.getD (code - {lo}) 0")
            lines.append("")

        lines.append(f"private theorem cup2BadRank{n}_decreases_from")
        lines.append(f"    (c : Config cup2Spec{n})")
        lines.append(f"    (hbad : c ∉ cup2GC{n}.configs)")
        lines.append(f"    (i : Fin {n})")
        lines.append(f"    (hpriv : privileged cup2Sys{n} c i)")
        lines.append(f"    (hnext : move cup2Sys{n} c i ∉ cup2GC{n}.configs) :")
        lines.append(f"    cup2BadRank{n} (move cup2Sys{n} c i) < cup2BadRank{n} c := by")
        lines.append(f"  native_decide +revert")
        lines.append(f"")
        lines.append(f"private theorem cup2BadRank{n}_decreases :")
        lines.append(f"    ∀ {{c' c : Config cup2Spec{n}}},")
        lines.append(f"      badStep cup2Sys{n} cup2GC{n} c' c →")
        lines.append(f"        cup2BadRank{n} c' < cup2BadRank{n} c := by")
        lines.append(f"  intro c' c hstep")
        lines.append(f"  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩")
        lines.append(f"  exact cup2BadRank{n}_decreases_from c hbad i hpriv hnext")
        lines.append("")

        lines.append(f"theorem cup2Converges{n} : converges cup2Sys{n} cup2GC{n} := by")
        lines.append(f"  let f := cup2BadRank{n}")
        lines.append(f"  let r : Config cup2Spec{n} → Config cup2Spec{n} → Prop := InvImage Nat.lt f")
        lines.append(f"  have hwf : WellFounded r := by")
        lines.append(f"    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)")
        lines.append(f"  refine Subrelation.wf (r := r) ?_ hwf")
        lines.append(f"  intro c' c hstep")
        lines.append(f"  exact cup2BadRank{n}_decreases hstep")
        lines.append("")

    lines.append("end LeanMn")
    lines.append("")

    return "\n".join(lines)


if __name__ == "__main__":
    print("Computing CUP-2 bad-step ranks (using Lean table values)...")
    print()

    all_ok = True
    for n in range(4, 11):
        ok = verify_ranks(n)
        all_ok = all_ok and ok
        print()

    if all_ok:
        print("All verifications passed! Generating Lean code...")
        lean_code = generate_lean_code()
        import os
        outpath = os.path.join(os.path.dirname(__file__),
                               "../lean/LeanMn/SmallN/Cup2Convergence.lean")
        with open(outpath, "w") as f:
            f.write(lean_code)
        print(f"Written to {outpath}")
    else:
        print("VERIFICATION FAILED — not generating Lean code")
