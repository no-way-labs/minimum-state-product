#!/usr/bin/env python3
"""
Boundary ternary EC study near a 3-consecutive-binary block.

Setting:
- n = 9 ring
- binary block = {0, 1, 2}
- boundary ternary pivots = 8 (left of block) and 3 (right of block)

Question:
- At pivot 8, can a phase have K=1 (right/binary neighbor 0 fires once),
  J=0 (left/ternary neighbor 7 does not fire), and gap >= 3?
- Symmetrically at pivot 3, can a phase have J=1 (left/binary neighbor 2
  fires once), K=0 (right/ternary neighbor 4 does not fire), and gap >= 3?

This script does two things:
1. Exact locality-only phase analysis via a finite-state reachability graph.
2. Random tests on 10k+ locally consistent cyclic mover words with full support
   and sweep |displacement| >= 18.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from dataclasses import dataclass
import random
from typing import Dict, Iterable, List, Sequence, Tuple


N = 9
SWEEP_THRESHOLD = 2 * N
RANDOM_SEED = 20260409


def left(i: int) -> int:
    return (i - 1) % N


def right(i: int) -> int:
    return (i + 1) % N


def local_successors(i: int, forbidden: int | None = None) -> List[int]:
    out = []
    for j in ((i - 1) % N, i, (i + 1) % N):
        if j != forbidden:
            out.append(j)
    return out


def build_cyclic_word(increments: Sequence[int], start: int) -> Tuple[int, ...]:
    pos = start
    word = []
    for delta in increments:
        word.append(pos)
        pos = (pos + delta) % N
    if pos != start:
        raise ValueError("increments do not close to a cycle")
    return tuple(word)


def full_support(word: Sequence[int]) -> bool:
    return len(set(word)) == N


def cyclic_phase_interior(word: Sequence[int], start_idx: int, end_idx: int) -> Tuple[int, ...]:
    out = []
    idx = (start_idx + 1) % len(word)
    while idx != end_idx:
        out.append(word[idx])
        idx = (idx + 1) % len(word)
    return tuple(out)


def extract_phases(word: Sequence[int], pivot: int) -> List[Tuple[int, int, Tuple[int, ...]]]:
    fires = [idx for idx, mover in enumerate(word) if mover == pivot]
    if not fires:
        return []
    phases = []
    for r, start_idx in enumerate(fires):
        end_idx = fires[(r + 1) % len(fires)]
        phases.append((start_idx, end_idx, cyclic_phase_interior(word, start_idx, end_idx)))
    return phases


@dataclass(frozen=True)
class BoundaryCase:
    name: str
    pivot: int
    left_neighbor: int
    right_neighbor: int
    binary_neighbor: int
    ternary_neighbor: int
    target_left_count: int
    target_right_count: int

    @property
    def phase_endpoints(self) -> Tuple[int, int]:
        return (self.left_neighbor, self.right_neighbor)

    @property
    def target_binary_count(self) -> int:
        if self.binary_neighbor == self.left_neighbor:
            return self.target_left_count
        return self.target_right_count

    @property
    def target_ternary_count(self) -> int:
        if self.ternary_neighbor == self.left_neighbor:
            return self.target_left_count
        return self.target_right_count


CASE_LEFT_BOUNDARY = BoundaryCase(
    name="pivot 8 (left boundary ternary)",
    pivot=8,
    left_neighbor=7,
    right_neighbor=0,
    binary_neighbor=0,
    ternary_neighbor=7,
    target_left_count=0,   # J = count(7)
    target_right_count=1,  # K = count(0)
)

CASE_RIGHT_BOUNDARY = BoundaryCase(
    name="pivot 3 (right boundary ternary)",
    pivot=3,
    left_neighbor=2,
    right_neighbor=4,
    binary_neighbor=2,
    ternary_neighbor=4,
    target_left_count=1,   # J = count(2)
    target_right_count=0,  # K = count(4)
)


def initial_augmented_count(pos: int, case: BoundaryCase) -> Tuple[int, int]:
    left_count = 1 if pos == case.left_neighbor else 0
    right_count = 1 if pos == case.right_neighbor else 0
    return left_count, right_count


def step_augmented_count(
    left_count: int,
    right_count: int,
    pos: int,
    case: BoundaryCase,
) -> Tuple[int, int]:
    if pos == case.left_neighbor:
        left_count += 1
    if pos == case.right_neighbor:
        right_count += 1
    return left_count, right_count


def within_target(left_count: int, right_count: int, case: BoundaryCase) -> bool:
    return (
        left_count <= case.target_left_count
        and right_count <= case.target_right_count
    )


def build_exact_phase_graph(case: BoundaryCase):
    starts = []
    for pos in case.phase_endpoints:
        left_count, right_count = initial_augmented_count(pos, case)
        if within_target(left_count, right_count, case):
            starts.append((pos, left_count, right_count))

    graph: Dict[Tuple[int, int, int], List[Tuple[int, int, int]]] = defaultdict(list)
    queue = deque(starts)
    seen = set(starts)

    while queue:
        state = queue.popleft()
        pos, left_count, right_count = state
        for nxt in local_successors(pos, forbidden=case.pivot):
            new_left, new_right = step_augmented_count(left_count, right_count, nxt, case)
            if not within_target(new_left, new_right, case):
                continue
            nxt_state = (nxt, new_left, new_right)
            graph[state].append(nxt_state)
            if nxt_state not in seen:
                seen.add(nxt_state)
                queue.append(nxt_state)
    for state in starts:
        graph.setdefault(state, [])
    return starts, graph


def accepting_states(
    states: Iterable[Tuple[int, int, int]],
    case: BoundaryCase,
) -> List[Tuple[int, int, int]]:
    accept = []
    endpoints = set(case.phase_endpoints)
    for pos, left_count, right_count in states:
        if (
            pos in endpoints
            and left_count == case.target_left_count
            and right_count == case.target_right_count
        ):
            accept.append((pos, left_count, right_count))
    return accept


def reverse_graph(graph: Dict[Tuple[int, int, int], List[Tuple[int, int, int]]]):
    rev: Dict[Tuple[int, int, int], List[Tuple[int, int, int]]] = defaultdict(list)
    for src, dsts in graph.items():
        rev.setdefault(src, [])
        for dst in dsts:
            rev[dst].append(src)
    return rev


def reachable_from(starts: Iterable[Tuple[int, int, int]], graph) -> set[Tuple[int, int, int]]:
    queue = deque(starts)
    seen = set(starts)
    while queue:
        state = queue.popleft()
        for nxt in graph.get(state, []):
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


def has_cycle_in_subgraph(
    graph: Dict[Tuple[int, int, int], List[Tuple[int, int, int]]],
    relevant: set[Tuple[int, int, int]],
) -> bool:
    color: Dict[Tuple[int, int, int], int] = {}

    def dfs(node: Tuple[int, int, int]) -> bool:
        color[node] = 1
        for nxt in graph.get(node, []):
            if nxt not in relevant:
                continue
            if nxt == node:
                return True
            state = color.get(nxt, 0)
            if state == 1:
                return True
            if state == 0 and dfs(nxt):
                return True
        color[node] = 2
        return False

    for node in relevant:
        if color.get(node, 0) == 0 and dfs(node):
            return True
    return False


def topo_order(
    graph: Dict[Tuple[int, int, int], List[Tuple[int, int, int]]],
    relevant: set[Tuple[int, int, int]],
) -> List[Tuple[int, int, int]]:
    indegree = {node: 0 for node in relevant}
    for src in relevant:
        for dst in graph.get(src, []):
            if dst in relevant:
                indegree[dst] += 1
    queue = deque(sorted(node for node, deg in indegree.items() if deg == 0))
    order = []
    while queue:
        node = queue.popleft()
        order.append(node)
        for nxt in graph.get(node, []):
            if nxt not in relevant:
                continue
            indegree[nxt] -= 1
            if indegree[nxt] == 0:
                queue.append(nxt)
    return order


def exact_phase_analysis(case: BoundaryCase) -> Dict[str, object]:
    starts, graph = build_exact_phase_graph(case)
    all_states = set(graph)
    for dsts in graph.values():
        all_states.update(dsts)
    accept = accepting_states(all_states, case)
    forward = reachable_from(starts, graph)
    reverse = reachable_from(accept, reverse_graph(graph))
    relevant = forward & reverse
    cyclic = has_cycle_in_subgraph(graph, relevant)

    if cyclic:
        return {
            "case": case,
            "starts": starts,
            "accept": accept,
            "relevant": relevant,
            "cyclic": True,
        }

    order = topo_order(graph, relevant)
    lengths: Dict[Tuple[int, int, int], set[int]] = {node: set() for node in relevant}
    witness: Dict[Tuple[Tuple[int, int, int], int], Tuple[int, ...]] = {}
    for state in starts:
        if state in relevant:
            lengths[state].add(1)
            witness[(state, 1)] = (state[0],)

    for node in order:
        for current_len in sorted(lengths[node]):
            path = witness[(node, current_len)]
            for nxt in graph.get(node, []):
                if nxt not in relevant:
                    continue
                new_len = current_len + 1
                if new_len not in lengths[nxt]:
                    witness[(nxt, new_len)] = path + (nxt[0],)
                lengths[nxt].add(new_len)

    accepted_lengths = sorted(
        {
            accepted_len
            for state in accept
            if state in relevant
            for accepted_len in lengths[state]
        }
    )
    accepted_witnesses = {}
    for state in accept:
        if state not in relevant:
            continue
        for accepted_len in lengths[state]:
            accepted_witnesses.setdefault(accepted_len, witness[(state, accepted_len)])

    return {
        "case": case,
        "starts": starts,
        "accept": accept,
        "relevant": relevant,
        "cyclic": False,
        "accepted_lengths": accepted_lengths,
        "accepted_witnesses": accepted_witnesses,
    }


def random_increment_cycle(length: int, rng: random.Random) -> Tuple[List[int], int]:
    allowed_displacements = [d for d in range(SWEEP_THRESHOLD, length + 1, N)]
    displacement = rng.choice(allowed_displacements)
    if rng.random() < 0.5:
        displacement = -displacement

    max_extra_backtracks = (length - abs(displacement)) // 2
    extra_backtracks = rng.randint(0, max_extra_backtracks)
    nonzero_steps = abs(displacement) + 2 * extra_backtracks

    pos_steps = (nonzero_steps + displacement) // 2
    neg_steps = nonzero_steps - pos_steps
    zero_steps = length - nonzero_steps

    increments = [1] * pos_steps + [-1] * neg_steps + [0] * zero_steps
    rng.shuffle(increments)
    return increments, displacement


def generate_random_words(
    lengths: Sequence[int],
    target_total: int,
    seed: int,
) -> Tuple[List[Tuple[int, Tuple[int, ...], int]], Counter, Counter]:
    rng = random.Random(seed)
    words: List[Tuple[int, Tuple[int, ...], int]] = []
    attempts = Counter()
    accepted = Counter()

    while len(words) < target_total:
        length = rng.choice(lengths)
        attempts[length] += 1
        increments, displacement = random_increment_cycle(length, rng)
        start = rng.randrange(N)
        word = build_cyclic_word(increments, start)
        if not full_support(word):
            continue
        accepted[length] += 1
        words.append((length, word, displacement))

    return words, attempts, accepted


def scan_case_on_words(case: BoundaryCase, words: Sequence[Tuple[int, Tuple[int, ...], int]]) -> Dict[str, object]:
    target_gap_at_least_3 = []
    target_gap_eq_2 = []
    all_target_phases = 0
    total_phases = 0
    gap_hist = Counter()
    jk_hist = Counter()

    for length, word, displacement in words:
        for start_idx, end_idx, interior in extract_phases(word, case.pivot):
            total_phases += 1
            left_count = interior.count(case.left_neighbor)
            right_count = interior.count(case.right_neighbor)
            gap = len(interior) + 1
            gap_hist[gap] += 1
            jk_hist[(left_count, right_count)] += 1

            if (
                left_count == case.target_left_count
                and right_count == case.target_right_count
            ):
                all_target_phases += 1
                record = {
                    "length": length,
                    "displacement": displacement,
                    "gap": gap,
                    "interior": interior,
                    "word_prefix": word[: min(18, len(word))],
                    "phase_start": start_idx,
                    "phase_end": end_idx,
                }
                if gap >= 3:
                    target_gap_at_least_3.append(record)
                elif gap == 2:
                    target_gap_eq_2.append(record)

    return {
        "case": case,
        "total_phases": total_phases,
        "all_target_phases": all_target_phases,
        "target_gap_at_least_3": target_gap_at_least_3,
        "target_gap_eq_2": target_gap_eq_2,
        "gap_hist": gap_hist,
        "jk_hist": jk_hist,
    }


def summarize_exact(result: Dict[str, object]) -> None:
    case: BoundaryCase = result["case"]  # type: ignore[assignment]
    print(f"EXACT PHASE ANALYSIS: {case.name}")
    if result["cyclic"]:
        print("  Relevant finite-state graph still has a cycle.")
        print("  This did not occur in the boundary cases studied here.")
        print()
        return

    accepted_lengths = result["accepted_lengths"]  # type: ignore[assignment]
    accepted_witnesses = result["accepted_witnesses"]  # type: ignore[assignment]

    print(
        f"  Target counts: left={case.target_left_count}, right={case.target_right_count}"
        f"  [binary={case.binary_neighbor}, ternary={case.ternary_neighbor}]"
    )
    print(f"  Possible interior lengths exactly: {accepted_lengths}")
    print(f"  Possible time gaps exactly: {[length + 1 for length in accepted_lengths]}")
    for length in accepted_lengths:
        print(f"  Witness interior for length {length}: {accepted_witnesses[length]}")
    print()


def summarize_random(scan: Dict[str, object]) -> None:
    case: BoundaryCase = scan["case"]  # type: ignore[assignment]
    target_gap_at_least_3 = scan["target_gap_at_least_3"]  # type: ignore[assignment]
    target_gap_eq_2 = scan["target_gap_eq_2"]  # type: ignore[assignment]
    print(f"RANDOM WORD SCAN: {case.name}")
    print(f"  Total phases scanned: {scan['total_phases']}")
    print(f"  Total target phases: {scan['all_target_phases']}")
    print(f"  Target phases with gap = 2: {len(target_gap_eq_2)}")
    print(f"  Target phases with gap >= 3: {len(target_gap_at_least_3)}")
    if target_gap_eq_2:
        example = target_gap_eq_2[0]
        print(f"  Example gap-2 target phase interior: {example['interior']}")
    if target_gap_at_least_3:
        example = target_gap_at_least_3[0]
        print(f"  Example gap>=3 target phase interior: {example['interior']}")
    print()


def main() -> None:
    print("Boundary ternary phase study")
    print(f"n={N}, binary block={{0,1,2}}, random_seed={RANDOM_SEED}")
    print()

    exact_left = exact_phase_analysis(CASE_LEFT_BOUNDARY)
    exact_right = exact_phase_analysis(CASE_RIGHT_BOUNDARY)
    summarize_exact(exact_left)
    summarize_exact(exact_right)

    lengths = [18, 27, 36, 45, 54, 72]
    words, attempts, accepted = generate_random_words(
        lengths=lengths,
        target_total=15000,
        seed=RANDOM_SEED,
    )
    print("RANDOM WORD GENERATION")
    print(f"  Accepted words: {len(words)}")
    print(f"  Lengths used: {lengths}")
    print(f"  Acceptance by length: {dict(sorted(accepted.items()))}")
    print(f"  Attempts by length: {dict(sorted(attempts.items()))}")
    print()

    left_scan = scan_case_on_words(CASE_LEFT_BOUNDARY, words)
    right_scan = scan_case_on_words(CASE_RIGHT_BOUNDARY, words)
    summarize_random(left_scan)
    summarize_random(right_scan)

    left_bad = len(left_scan["target_gap_at_least_3"])  # type: ignore[arg-type]
    right_bad = len(right_scan["target_gap_at_least_3"])  # type: ignore[arg-type]

    print("CONCLUSION")
    if left_bad == 0:
        print(
            "  At pivot 8, K=1 and J=0 never produces gap >= 3."
            " Locality forces the unique target phase to be interior (0,), so gap = 2."
        )
    else:
        print(f"  At pivot 8, found {left_bad} counterexamples with gap >= 3.")

    if right_bad == 0:
        print(
            "  At pivot 3, the symmetric one-binary/zero-ternary pattern also never"
            " produces gap >= 3. The unique target phase is interior (2,), so gap = 2."
        )
    else:
        print(f"  At pivot 3, found {right_bad} counterexamples with gap >= 3.")


if __name__ == "__main__":
    main()
