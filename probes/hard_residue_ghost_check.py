#!/usr/bin/env python3
"""Check whether the n=9 HardResidue branches are "ghosts".

This script does two concrete things.

1. Exhaustively enumerate every n=9 state vector ``ms`` with:
   - at least 3 binary processors,
   - product(ms) < 4 * 3^(n-2),
   - at least one sandwiched ternary pivot
     (ms[t] = 3 and ms[t-1] = ms[t+1] = 2).

2. Verify explicit n=9 mover-word witnesses for the four hard-residue branches
   against the actual mover-word-side Lean predicates:
   - local mover adjacency (``next_mover_is_local`` shape),
   - full support,
   - ``hno_safe``,
   - ``hall_normal`` / ``isNormalFormGap`` for *all* phases of a chosen pivot,
   - the relevant hard-residue subcase shape.

Important limitation:
This script does not try to complete the mover words to a total convergent
system. That is deliberate. In the Lean theorem
``allNormalForm_false``, the hypotheses and residue predicates we are testing
here are mover-word-only, and ``_hconv`` is not used in the body of the theorem.
So this script answers the colleague's implication question directly:

    does ``hall_normal`` force a sandwiched ternary pivot / hard residue
    pattern to be impossible?

If explicit mover-word witnesses exist, then the answer is "no".
"""

from __future__ import annotations

from dataclasses import dataclass
from math import prod
from typing import Iterable


N = 9
THRESHOLD = 4 * (3 ** (N - 2))


def left(i: int, n: int = N) -> int:
    return (i - 1) % n


def right(i: int, n: int = N) -> int:
    return (i + 1) % n


def rotate_word(word: list[int], delta: int, n: int = N) -> list[int]:
    return [((x + delta) % n) for x in word]


def mirror_word(word: list[int], n: int = N) -> list[int]:
    # Base witnesses are written for pivot t = 0. Mirroring sends x -> -x mod n.
    return [((-x) % n) for x in word]


def sandwiched_pivots(ms: tuple[int, ...]) -> list[int]:
    n = len(ms)
    out = []
    for t in range(n):
        if ms[t] == 3 and ms[(t - 1) % n] == 2 and ms[(t + 1) % n] == 2:
            out.append(t)
    return out


def enumerate_state_vectors(n: int = N, threshold: int = THRESHOLD) -> list[tuple[int, ...]]:
    """Enumerate all state vectors with entries >= 2 and product < threshold."""

    out: list[tuple[int, ...]] = []

    def dfs(idx: int, sofar: list[int], prod_so_far: int) -> None:
        if idx == n:
            out.append(tuple(sofar))
            return

        remaining = n - idx - 1
        # Minimal contribution from the remaining positions is 2^remaining.
        max_m = (threshold - 1) // (prod_so_far * (2 ** remaining))
        for m in range(2, max_m + 1):
            next_prod = prod_so_far * m
            if next_prod * (2 ** remaining) >= threshold:
                break
            sofar.append(m)
            dfs(idx + 1, sofar, next_prod)
            sofar.pop()

    dfs(0, [], 1)
    return out


def has_ge3_binary(ms: tuple[int, ...]) -> bool:
    return sum(1 for m in ms if m == 2) >= 3


def local_five(t: int, n: int = N) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def last_outside_index(word: list[int], t: int, n: int = N) -> int | None:
    local = local_five(t, n)
    outside = [k for k, mover in enumerate(word) if mover not in local]
    return max(outside) if outside else None


def check_local_mover_adjacency(word: list[int], n: int = N) -> bool:
    if not word:
        return False
    for a, b in zip(word, word[1:] + word[:1], strict=True):
        if b not in {left(a, n), a, right(a, n)}:
            return False
    return True


def full_support(word: list[int], n: int = N) -> bool:
    return set(word) == set(range(n))


def hno_safe(word: list[int], n: int = N) -> bool:
    seen = set(word)
    for q in range(n):
        hood = {left(q, n), q, right(q, n)}
        if seen.isdisjoint(hood):
            return False
    return True


@dataclass(frozen=True)
class Phase:
    a: int
    s: int
    j: int
    k: int


def phases(word: list[int], t: int) -> list[Phase]:
    out: list[Phase] = []
    for s, mover in enumerate(word):
        if mover != t:
            continue
        prev_t = -1
        for k in range(s - 1, -1, -1):
            if word[k] == t:
                prev_t = k
                break
        for a in range(prev_t + 1, s):
            if word[a] == t:
                continue
            j = sum(1 for x in word[a:s] if x == left(t))
            k = sum(1 for x in word[a:s] if x == right(t))
            out.append(Phase(a=a, s=s, j=j, k=k))
    return out


def is_normal_phase(j: int, k: int) -> bool:
    both_even = (j % 2 == 0) and (k % 2 == 0)
    toggle_left = (j >= 2) and (k == 0)
    toggle_right = (j == 0) and (k >= 2)
    return not (both_even or toggle_left or toggle_right)


def hall_normal(word: list[int], t: int) -> bool:
    return all(is_normal_phase(phase.j, phase.k) for phase in phases(word, t))


def fire_count(word: list[int], p: int) -> int:
    return sum(1 for x in word if x == p)


def _ls_positions(t: int, n: int = N) -> dict[str, int]:
    return {
        "left1": (t - 1) % n,
        "left2": (t - 2) % n,
        "left3": (t - 3) % n,
        "left4": (t - 4) % n,
        "right1": (t + 1) % n,
        "right2": (t + 2) % n,
        "right3": (t + 3) % n,
        "right4": (t + 4) % n,
    }


def is_left_same_noafter(word: list[int], t: int) -> bool:
    pos = _ls_positions(t)
    k_out = last_outside_index(word, t)
    if k_out is None or k_out + 1 >= len(word):
        return False
    if word[k_out] != pos["left3"] or word[k_out + 1] != pos["left2"]:
        return False
    if any(word[k] not in {pos["left2"], pos["left1"]} for k in range(k_out + 1, len(word))):
        return False

    allowed_tail = {pos["left3"], pos["left2"], pos["left1"], t, pos["right1"], pos["right2"]}
    for j in range(k_out):
        if j + 1 >= len(word):
            continue
        if word[j] != pos["left4"] or word[j + 1] != pos["left3"]:
            continue
        if any(word[k] not in allowed_tail for k in range(j + 1, len(word))):
            continue
        if any(word[s] == t for s in range(j + 2, len(word))):
            continue
        return True
    return False


def is_right_same_noafter(word: list[int], t: int) -> bool:
    pos = _ls_positions(t)
    k_out = last_outside_index(word, t)
    if k_out is None or k_out + 1 >= len(word):
        return False
    if word[k_out] != pos["right3"] or word[k_out + 1] != pos["right2"]:
        return False
    if any(word[k] not in {pos["right2"], pos["right1"]} for k in range(k_out + 1, len(word))):
        return False

    allowed_tail = {pos["left2"], pos["left1"], t, pos["right1"], pos["right2"], pos["right3"]}
    for j in range(k_out):
        if j + 1 >= len(word):
            continue
        if word[j] != pos["right4"] or word[j + 1] != pos["right3"]:
            continue
        if any(word[k] not in allowed_tail for k in range(j + 1, len(word))):
            continue
        if any(word[s] == t for s in range(j + 2, len(word))):
            continue
        return True
    return False


def is_left_cross_terminal(word: list[int], t: int) -> bool:
    pos = _ls_positions(t)
    k_out = last_outside_index(word, t)
    if k_out is None or k_out + 1 >= len(word):
        return False
    if word[k_out] != pos["left3"] or word[k_out + 1] != pos["left2"]:
        return False
    if any(word[k] not in {pos["left2"], pos["left1"]} for k in range(k_out + 1, len(word))):
        return False

    allowed_tail = {pos["left3"], pos["left2"], pos["left1"], t, pos["right1"], pos["right2"]}
    for j in range(k_out):
        if j + 1 >= len(word):
            continue
        if word[j] != pos["right3"] or word[j + 1] != pos["right2"]:
            continue
        if any(word[k] not in allowed_tail for k in range(j + 1, len(word))):
            continue
        return True
    return False


def is_right_cross_terminal(word: list[int], t: int) -> bool:
    pos = _ls_positions(t)
    k_out = last_outside_index(word, t)
    if k_out is None or k_out + 1 >= len(word):
        return False
    if word[k_out] != pos["right3"] or word[k_out + 1] != pos["right2"]:
        return False
    if any(word[k] not in {pos["right2"], pos["right1"]} for k in range(k_out + 1, len(word))):
        return False

    allowed_tail = {pos["left2"], pos["left1"], t, pos["right1"], pos["right2"], pos["right3"]}
    for j in range(k_out):
        if j + 1 >= len(word):
            continue
        if word[j] != pos["left3"] or word[j + 1] != pos["left2"]:
            continue
        if any(word[k] not in allowed_tail for k in range(j + 1, len(word))):
            continue
        return True
    return False


@dataclass(frozen=True)
class WitnessResult:
    name: str
    subcase: str
    word: tuple[int, ...]
    local: bool
    full: bool
    no_safe: bool
    hall_normal: bool
    hard: bool
    fire_t: int
    phase_data: tuple[tuple[int, int, int, int], ...]


def analyze_witness(name: str, subcase: str, base_word: list[int], checker, t: int) -> WitnessResult:
    word = rotate_word(base_word, t)
    ps = phases(word, t)
    return WitnessResult(
        name=name,
        subcase=subcase,
        word=tuple(word),
        local=check_local_mover_adjacency(word),
        full=full_support(word),
        no_safe=hno_safe(word),
        hall_normal=hall_normal(word, t),
        hard=checker(word, t),
        fire_t=fire_count(word, t),
        phase_data=tuple((p.a, p.s, p.j, p.k) for p in ps),
    )


# Canonical n=9 mover words written for pivot t = 0.
#
# These are not transition tables. They are explicit mover words used to test
# the mover-word-side predicates from Lean.
BASE_LEFT_SAME = [
    8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 6, 7, 8
]

BASE_LEFT_CROSS = [
    8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 7, 8
]

BASE_RIGHT_SAME = mirror_word(BASE_LEFT_SAME)
BASE_RIGHT_CROSS = mirror_word(BASE_LEFT_CROSS)


def unique_sandwiched_positions(vectors: Iterable[tuple[int, ...]]) -> set[int]:
    out: set[int] = set()
    for ms in vectors:
        out.update(sandwiched_pivots(ms))
    return out


def summarize_vectors(vectors: list[tuple[int, ...]]) -> str:
    bin_counts: dict[int, int] = {}
    max_entry = 0
    for ms in vectors:
        b = sum(1 for m in ms if m == 2)
        bin_counts[b] = bin_counts.get(b, 0) + 1
        max_entry = max(max_entry, max(ms))
    bits = [f"{k}bin:{bin_counts[k]}" for k in sorted(bin_counts)]
    return f"count={len(vectors)} max_entry={max_entry} " + " ".join(bits)


def main() -> None:
    all_vectors = enumerate_state_vectors()
    candidate_vectors = [
        ms for ms in all_vectors
        if has_ge3_binary(ms) and sandwiched_pivots(ms)
    ]
    total_pivots = sum(len(sandwiched_pivots(ms)) for ms in candidate_vectors)
    pivot_positions = sorted(unique_sandwiched_positions(candidate_vectors))

    print("n=9 state-vector enumeration")
    print(f"  threshold={THRESHOLD}")
    print(f"  all sub-threshold vectors: {len(all_vectors)}")
    print(f"  with >=3 binary and a sandwiched ternary: {len(candidate_vectors)}")
    print(f"  total sandwiched pivots across those vectors: {total_pivots}")
    print(f"  pivot positions that occur: {pivot_positions}")
    print(f"  summary: {summarize_vectors(candidate_vectors)}")
    print("  first 10 candidates:")
    for ms in candidate_vectors[:10]:
        print(f"    ms={ms} pivots={sandwiched_pivots(ms)} product={prod(ms)}")

    witness_specs = [
        ("LeftSame", "LeftSameNoAfterHardResidue", BASE_LEFT_SAME, is_left_same_noafter),
        ("RightSame", "RightSameNoAfterHardResidue", BASE_RIGHT_SAME, is_right_same_noafter),
        ("LeftCross", "LeftCrossTerminalHardResidue", BASE_LEFT_CROSS, is_left_cross_terminal),
        ("RightCross", "RightCrossTerminalHardResidue", BASE_RIGHT_CROSS, is_right_cross_terminal),
    ]

    print()
    print("canonical mover-word witnesses")
    all_ok = True
    for name, subcase, base_word, checker in witness_specs:
        print(f"  {name} via {subcase}")
        for t in range(N):
            result = analyze_witness(name, subcase, base_word, checker, t)
            ok = (
                result.local and
                result.full and
                result.no_safe and
                result.hall_normal and
                result.hard and
                (result.fire_t >= 2) and
                (result.fire_t < len(result.word))
            )
            all_ok = all_ok and ok
            status = "OK" if ok else "FAIL"
            print(
                f"    t={t}: {status} "
                f"local={result.local} full={result.full} no_safe={result.no_safe} "
                f"hall_normal={result.hall_normal} hard={result.hard} fire_t={result.fire_t}"
            )
        sample = analyze_witness(name, subcase, base_word, checker, 0)
        print(f"    sample word (t=0): {sample.word}")
        print(f"    sample phases (a,s,J,K): {sample.phase_data}")

    print()
    if all_ok:
        print("conclusion")
        print("  hall_normal is compatible with a sandwiched ternary pivot at n=9.")
        print(f"  The witnesses validate for every pivot position in {pivot_positions}, so they")
        print(f"  apply to all {total_pivots} sandwiched pivots across the {len(candidate_vectors)}")
        print("  enumerated candidate state vectors.")
        print("  Each of the four hard-residue branches has an explicit mover-word witness")
        print("  satisfying locality, full support, hno_safe, fireCount(t) >= 2, and")
        print("  hall_normal for all phases of the chosen pivot.")
        print("  So the hard-residue branches are not ghosts for mover-word reasons.")
    else:
        print("conclusion")
        print("  At least one canonical witness failed a required predicate.")


if __name__ == "__main__":
    main()
