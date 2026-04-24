#!/usr/bin/env python3
"""Strict entry-conflict analysis for mixed binary token-ring good cycles.

This scanner uses the same cyclic mover-word notion as the blocker scripts:
the mover word must be ring-adjacent even across the wrap from the last mover
back to the first, and the induced cycle must be globally simple and fair.

It classifies deterministic clashes forced by a candidate good cycle into:
  - mover/nonmover overlap: same `(proc, L, S, R)` seen both while moving and
    while staying put;
  - mover/mover clash: same `(proc, L, S, R)` seen as a mover with two
    different outputs.

The script can scan explicit state vectors or enumerate all dihedral classes
below the mixed lower-bound threshold `4 * 3^(n-2)` for selected `n`.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
import sys
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.binscc_mixed_nonconsec_mnu import build_cycle


Context = tuple[int, int, int]
ConflictKey = tuple[int, Context]


@dataclass(frozen=True)
class ConflictRecord:
    proc: int
    ctx: Context
    kind: str
    outputs: tuple[int, ...]
    binary_neighbors: int
    is_binary: bool


@dataclass(frozen=True)
class CleanSearchResult:
    found: bool
    word: tuple[int, ...] | None
    strict_cycles_checked: int
    nodes: int
    target_procs: tuple[int, ...]


@dataclass(frozen=True)
class CleanEnumerationResult:
    words: tuple[tuple[int, ...], ...]
    strict_cycles_checked: int
    nodes: int
    target_procs: tuple[int, ...]


def product(values: Iterable[int]) -> int:
    out = 1
    for value in values:
        out *= value
    return out


def max_binary_run(ms: tuple[int, ...]) -> int:
    n = len(ms)
    best = 0
    run = 0
    for i in range(2 * n):
        if ms[i % n] == 2:
            run += 1
            best = max(best, run)
        else:
            run = 0
    return best


def pairwise_nonadjacent_binary(ms: tuple[int, ...]) -> bool:
    n = len(ms)
    binary = [i for i, m in enumerate(ms) if m == 2]
    if len(binary) < 3:
        return False
    for i in binary:
        if ms[(i - 1) % n] == 2 or ms[(i + 1) % n] == 2:
            return False
    return True


def no_triple_binary_run(ms: tuple[int, ...]) -> bool:
    return sum(1 for m in ms if m == 2) >= 3 and max_binary_run(ms) <= 2


def dihedral_canonical(ms: tuple[int, ...]) -> tuple[int, ...]:
    n = len(ms)
    rotations = [ms[i:] + ms[:i] for i in range(n)]
    reflected = tuple(reversed(ms))
    rotations.extend(reflected[i:] + reflected[:i] for i in range(n))
    return min(rotations)


def enumerate_classes(
    n: int,
    predicate,
) -> list[tuple[int, ...]]:
    threshold = 4 * (3 ** (n - 2))
    classes: set[tuple[int, ...]] = set()

    def dfs(prefix: list[int], prod_so_far: int, has_large: bool, binary_count: int) -> None:
        remaining = n - len(prefix)
        if remaining == 0:
            ms = tuple(prefix)
            if not has_large:
                return
            if prod_so_far >= threshold:
                return
            if binary_count < 3:
                return
            if predicate(ms):
                classes.add(dihedral_canonical(ms))
            return

        min_possible = prod_so_far * (2 ** remaining)
        if min_possible >= threshold:
            return

        max_state = (threshold - 1) // prod_so_far
        for m in range(2, max_state + 1):
            next_prod = prod_so_far * m
            if next_prod >= threshold:
                break
            prefix.append(m)
            dfs(prefix, next_prod, has_large or m >= 4, binary_count + (1 if m == 2 else 0))
            prefix.pop()

    dfs([], 1, False, 0)
    return sorted(classes)


def iter_mover_words_smart(ms: tuple[int, ...], max_length: int):
    n = len(ms)
    ring_adj = {p: ((p - 1) % n, (p + 1) % n) for p in range(n)}
    start = tuple(0 for _ in range(n))

    def dfs(word: list[int], fire_counts: list[int], config: tuple[int, ...]):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0 for p in range(n))
            if fair:
                yield tuple(word)
            return

        remaining = max_length - len(word)
        needed = sum(
            max(0, ms[p] - fire_counts[p])
            for p in range(n)
            if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0
        )
        if needed > remaining:
            return

        last = word[-1]
        for nxt in ring_adj[last]:
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            fire_counts[nxt] += 1
            word.append(nxt)
            yield from dfs(word, fire_counts, tuple(new_config))
            word.pop()
            fire_counts[nxt] -= 1

    for first_proc in range(n):
        config = list(start)
        config[first_proc] = (config[first_proc] + 1) % ms[first_proc]
        fire_counts = [0] * n
        fire_counts[first_proc] = 1
        yield from dfs([first_proc], fire_counts, tuple(config))


def target_binary_neighbor_procs(
    ms: tuple[int, ...],
    required_neighbors: int = 2,
    min_neighbors: int | None = None,
) -> tuple[int, ...]:
    n = len(ms)
    out = []
    for proc in range(n):
        bn = int(ms[(proc - 1) % n] == 2) + int(ms[(proc + 1) % n] == 2)
        if min_neighbors is not None:
            if bn >= min_neighbors:
                out.append(proc)
        elif bn == required_neighbors:
            out.append(proc)
    return tuple(out)


def resolve_target_procs(
    ms: tuple[int, ...],
    required_neighbors: int = 2,
    min_neighbors: int | None = None,
    target_procs: tuple[int, ...] | None = None,
) -> tuple[int, ...]:
    if target_procs is not None:
        n = len(ms)
        return tuple(sorted({proc % n for proc in target_procs}))
    return target_binary_neighbor_procs(
        ms,
        required_neighbors=required_neighbors,
        min_neighbors=min_neighbors,
    )


def context_index_map(ms: tuple[int, ...], proc: int) -> dict[Context, int]:
    left_m = ms[(proc - 1) % len(ms)]
    self_m = ms[proc]
    right_m = ms[(proc + 1) % len(ms)]
    out = {}
    idx = 0
    for left in range(left_m):
        for self_state in range(self_m):
            for right in range(right_m):
                out[(left, self_state, right)] = idx
                idx += 1
    return out


def find_bn_clean_cycle(
    ms: tuple[int, ...],
    max_length: int,
    required_neighbors: int = 2,
    min_neighbors: int | None = None,
    target_procs: tuple[int, ...] | None = None,
) -> CleanSearchResult:
    n = len(ms)
    start = tuple(0 for _ in range(n))
    ring_adj = {p: ((p - 1) % n, (p + 1) % n) for p in range(n)}
    targets = resolve_target_procs(
        ms,
        required_neighbors=required_neighbors,
        min_neighbors=min_neighbors,
        target_procs=target_procs,
    )
    if not targets:
        return CleanSearchResult(
            found=False,
            word=None,
            strict_cycles_checked=0,
            nodes=0,
            target_procs=(),
        )

    ctx_maps = {proc: context_index_map(ms, proc) for proc in targets}
    target_index = {proc: idx for idx, proc in enumerate(targets)}
    strict_cycles_checked = 0
    nodes = 0

    def ctx_bit(proc: int, config: tuple[int, ...]) -> int:
        ctx = (config[(proc - 1) % n], config[proc], config[(proc + 1) % n])
        return 1 << ctx_maps[proc][ctx]

    def step_masks(
        config: tuple[int, ...],
        mover: int,
        mover_masks: tuple[int, ...],
        non_masks: tuple[int, ...],
    ) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
        new_mover = list(mover_masks)
        new_non = list(non_masks)
        for proc in targets:
            idx = target_index[proc]
            bit = ctx_bit(proc, config)
            if mover == proc:
                if non_masks[idx] & bit:
                    return None
                new_mover[idx] |= bit
            else:
                if mover_masks[idx] & bit:
                    return None
                new_non[idx] |= bit
        return tuple(new_mover), tuple(new_non)

    def dfs(
        first_proc: int,
        last_proc: int,
        word: list[int],
        fire_counts: list[int],
        config: tuple[int, ...],
        visited: set[tuple[int, ...]],
        mover_masks: tuple[int, ...],
        non_masks: tuple[int, ...],
    ) -> tuple[int, ...] | None:
        nonlocal strict_cycles_checked, nodes
        nodes += 1

        if len(word) > max_length:
            return None

        if len(word) >= 6 and config == start:
            if first_proc not in ring_adj[last_proc]:
                return None
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0 for p in range(n))
            if fair:
                strict_cycles_checked += 1
                return tuple(word)
            return None

        remaining = max_length - len(word)
        needed = sum(
            max(0, ms[p] - fire_counts[p])
            for p in range(n)
            if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0
        )
        if needed > remaining:
            return None

        for nxt in ring_adj[last_proc]:
            masks = step_masks(config, nxt, mover_masks, non_masks)
            if masks is None:
                continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1

            if new_config == start:
                result = dfs(
                    first_proc,
                    nxt,
                    word + [nxt],
                    new_counts,
                    new_config,
                    visited,
                    masks[0],
                    masks[1],
                )
                if result is not None:
                    return result
                continue

            if new_config in visited:
                continue

            visited.add(new_config)
            result = dfs(
                first_proc,
                nxt,
                word + [nxt],
                new_counts,
                new_config,
                visited,
                masks[0],
                masks[1],
            )
            visited.remove(new_config)
            if result is not None:
                return result
        return None

    zero_masks = tuple(0 for _ in targets)
    for first_proc in range(n):
        first_masks = step_masks(start, first_proc, zero_masks, zero_masks)
        if first_masks is None:
            continue
        config = list(start)
        config[first_proc] = (config[first_proc] + 1) % ms[first_proc]
        config = tuple(config)
        fire_counts = [0] * n
        fire_counts[first_proc] = 1
        result = dfs(
            first_proc=first_proc,
            last_proc=first_proc,
            word=[first_proc],
            fire_counts=fire_counts,
            config=config,
            visited={start, config},
            mover_masks=first_masks[0],
            non_masks=first_masks[1],
        )
        if result is not None:
            return CleanSearchResult(
                found=True,
                word=result,
                strict_cycles_checked=strict_cycles_checked,
                nodes=nodes,
                target_procs=targets,
            )

    return CleanSearchResult(
        found=False,
        word=None,
        strict_cycles_checked=strict_cycles_checked,
        nodes=nodes,
        target_procs=targets,
    )


def enumerate_bn_clean_cycles(
    ms: tuple[int, ...],
    max_length: int,
    required_neighbors: int = 2,
    min_neighbors: int | None = None,
    target_procs: tuple[int, ...] | None = None,
    max_found: int | None = None,
) -> CleanEnumerationResult:
    n = len(ms)
    start = tuple(0 for _ in range(n))
    ring_adj = {p: ((p - 1) % n, (p + 1) % n) for p in range(n)}
    targets = resolve_target_procs(
        ms,
        required_neighbors=required_neighbors,
        min_neighbors=min_neighbors,
        target_procs=target_procs,
    )
    if not targets:
        return CleanEnumerationResult(words=(), strict_cycles_checked=0, nodes=0, target_procs=())

    ctx_maps = {proc: context_index_map(ms, proc) for proc in targets}
    target_index = {proc: idx for idx, proc in enumerate(targets)}
    strict_cycles_checked = 0
    nodes = 0
    found_words: list[tuple[int, ...]] = []

    def ctx_bit(proc: int, config: tuple[int, ...]) -> int:
        ctx = (config[(proc - 1) % n], config[proc], config[(proc + 1) % n])
        return 1 << ctx_maps[proc][ctx]

    def step_masks(
        config: tuple[int, ...],
        mover: int,
        mover_masks: tuple[int, ...],
        non_masks: tuple[int, ...],
    ) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
        new_mover = list(mover_masks)
        new_non = list(non_masks)
        for proc in targets:
            idx = target_index[proc]
            bit = ctx_bit(proc, config)
            if mover == proc:
                if non_masks[idx] & bit:
                    return None
                new_mover[idx] |= bit
            else:
                if mover_masks[idx] & bit:
                    return None
                new_non[idx] |= bit
        return tuple(new_mover), tuple(new_non)

    def dfs(
        first_proc: int,
        last_proc: int,
        word: list[int],
        fire_counts: list[int],
        config: tuple[int, ...],
        visited: set[tuple[int, ...]],
        mover_masks: tuple[int, ...],
        non_masks: tuple[int, ...],
    ) -> None:
        nonlocal strict_cycles_checked, nodes
        if max_found is not None and len(found_words) >= max_found:
            return
        nodes += 1

        if len(word) > max_length:
            return

        if len(word) >= 6 and config == start:
            if first_proc not in ring_adj[last_proc]:
                return
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0 for p in range(n))
            if fair:
                strict_cycles_checked += 1
                found_words.append(tuple(word))
            return

        remaining = max_length - len(word)
        needed = sum(
            max(0, ms[p] - fire_counts[p])
            for p in range(n)
            if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0
        )
        if needed > remaining:
            return

        for nxt in ring_adj[last_proc]:
            masks = step_masks(config, nxt, mover_masks, non_masks)
            if masks is None:
                continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1

            if new_config == start:
                dfs(
                    first_proc,
                    nxt,
                    word + [nxt],
                    new_counts,
                    new_config,
                    visited,
                    masks[0],
                    masks[1],
                )
                continue

            if new_config in visited:
                continue

            visited.add(new_config)
            dfs(
                first_proc,
                nxt,
                word + [nxt],
                new_counts,
                new_config,
                visited,
                masks[0],
                masks[1],
            )
            visited.remove(new_config)

    zero_masks = tuple(0 for _ in targets)
    for first_proc in range(n):
        first_masks = step_masks(start, first_proc, zero_masks, zero_masks)
        if first_masks is None:
            continue
        config = list(start)
        config[first_proc] = (config[first_proc] + 1) % ms[first_proc]
        config = tuple(config)
        fire_counts = [0] * n
        fire_counts[first_proc] = 1
        dfs(
            first_proc=first_proc,
            last_proc=first_proc,
            word=[first_proc],
            fire_counts=fire_counts,
            config=config,
            visited={start, config},
            mover_masks=first_masks[0],
            non_masks=first_masks[1],
        )
        if max_found is not None and len(found_words) >= max_found:
            break

    return CleanEnumerationResult(
        words=tuple(found_words),
        strict_cycles_checked=strict_cycles_checked,
        nodes=nodes,
        target_procs=targets,
    )


def analyze_cycle(ms: tuple[int, ...], cycle: tuple[tuple[int, ...], ...]) -> list[ConflictRecord]:
    n = len(ms)
    binary = {i for i, m in enumerate(ms) if m == 2}
    mover_outputs: dict[ConflictKey, set[int]] = defaultdict(set)
    nonmover_seen: set[ConflictKey] = set()

    for step, config in enumerate(cycle):
        nxt = cycle[(step + 1) % len(cycle)]
        diffs = [i for i in range(n) if config[i] != nxt[i]]
        if len(diffs) != 1:
            raise ValueError("cycle is not single-move")
        mover = diffs[0]

        mover_ctx = (config[(mover - 1) % n], config[mover], config[(mover + 1) % n])
        mover_outputs[(mover, mover_ctx)].add(nxt[mover])

        for proc in range(n):
            if proc == mover:
                continue
            ctx = (config[(proc - 1) % n], config[proc], config[(proc + 1) % n])
            nonmover_seen.add((proc, ctx))

    conflicts: list[ConflictRecord] = []
    for key, outputs in mover_outputs.items():
        proc, ctx = key
        bn = int(ms[(proc - 1) % n] == 2) + int(ms[(proc + 1) % n] == 2)
        if len(outputs) > 1:
            conflicts.append(
                ConflictRecord(
                    proc=proc,
                    ctx=ctx,
                    kind="mover_mover",
                    outputs=tuple(sorted(outputs)),
                    binary_neighbors=bn,
                    is_binary=proc in binary,
                )
            )
        if key in nonmover_seen:
            conflicts.append(
                ConflictRecord(
                    proc=proc,
                    ctx=ctx,
                    kind="mover_nonmover",
                    outputs=tuple(sorted(outputs)),
                    binary_neighbors=bn,
                    is_binary=proc in binary,
                )
            )
    conflicts.sort(key=lambda rec: (rec.kind, rec.proc, rec.ctx))
    return conflicts


def summarize_state_vector(ms: tuple[int, ...], max_len: int, limit_words: int | None) -> None:
    n = len(ms)
    total_strict = 0
    clean = 0
    words_seen = 0
    kind_counts = Counter()
    proc_counts = Counter()
    bn_counts = Counter()
    example_clean: list[tuple[int, ...]] = []
    example_conflict: list[tuple[tuple[int, ...], list[ConflictRecord]]] = []

    for word in iter_mover_words_smart(ms, max_len):
        words_seen += 1
        if limit_words is not None and words_seen > limit_words:
            break
        cycle = build_cycle(list(ms), n, word)
        if cycle is None:
            continue
        total_strict += 1
        conflicts = analyze_cycle(ms, tuple(cycle))
        if conflicts:
            seen_kinds = {conf.kind for conf in conflicts}
            for kind in seen_kinds:
                kind_counts[kind] += 1
            for conf in conflicts:
                proc_counts[(conf.proc, conf.kind)] += 1
                bn_counts[(conf.binary_neighbors, conf.kind)] += 1
            if len(example_conflict) < 3:
                example_conflict.append((word, conflicts[:4]))
        else:
            clean += 1
            if len(example_clean) < 3:
                example_clean.append(word)

    print(f"\nms={list(ms)}  mover_words={words_seen}  strict_cycles={total_strict}", flush=True)
    if total_strict == 0:
        return
    print(f"  clean={clean}  conflict={total_strict - clean}", flush=True)
    print(f"  cycle-level kinds={dict(kind_counts)}", flush=True)

    print("  conflict proc/kind counts:", flush=True)
    for (proc, kind), count in sorted(proc_counts.items()):
        role = "B" if ms[proc] == 2 else f"m={ms[proc]}"
        print(f"    P{proc} {role} {kind}: {count}", flush=True)

    print("  binary-neighbor counts:", flush=True)
    for (bn, kind), count in sorted(bn_counts.items()):
        print(f"    {kind} with {bn} binary neighbors: {count}", flush=True)

    if example_conflict:
        print("  sample conflicts:", flush=True)
        for word, conflicts in example_conflict:
            print(f"    word={word}", flush=True)
            for conf in conflicts:
                print(
                    "      "
                    f"{conf.kind} at P{conf.proc} ctx={conf.ctx} outputs={conf.outputs} "
                    f"binary_neighbors={conf.binary_neighbors}",
                    flush=True,
                )

    if example_clean:
        print("  sample clean words:", flush=True)
        for word in example_clean:
            print(f"    {word}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--state-counts",
        action="append",
        help="explicit comma-separated state vector; may be passed multiple times",
    )
    parser.add_argument(
        "--n",
        type=int,
        nargs="*",
        default=[],
        help="enumerate all dihedral classes below 4*3^(n-2) for these n values",
    )
    parser.add_argument(
        "--binary-mode",
        choices=("pairwise", "no_triple_run"),
        default="pairwise",
        help="which binary-spacing constraint to enforce when enumerating classes",
    )
    parser.add_argument(
        "--max-len",
        type=int,
        default=None,
        help="override mover-word cutoff; default is 3*n+6 for each state vector",
    )
    parser.add_argument(
        "--limit-words",
        type=int,
        default=None,
        help="stop after this many mover words per state vector",
    )
    parser.add_argument(
        "--search-bn-clean",
        action="store_true",
        help="search directly for a strict cycle with no mover/nonmover conflict at processors with two binary neighbors",
    )
    parser.add_argument(
        "--required-binary-neighbors",
        type=int,
        default=2,
        help="target processors with exactly this many binary neighbors in --search-bn-clean mode unless --min-binary-neighbors is set",
    )
    parser.add_argument(
        "--min-binary-neighbors",
        type=int,
        default=None,
        help="target processors with at least this many binary neighbors in --search-bn-clean mode",
    )
    parser.add_argument(
        "--target-procs",
        default=None,
        help="comma-separated explicit target processors for --search-bn-clean; overrides binary-neighbor filtering",
    )
    args = parser.parse_args()

    vectors: list[tuple[int, ...]] = []
    if args.state_counts:
        vectors.extend(tuple(int(part) for part in spec.split(",")) for spec in args.state_counts)

    predicate = pairwise_nonadjacent_binary if args.binary_mode == "pairwise" else no_triple_binary_run
    for n in args.n:
        vectors.extend(enumerate_classes(n, predicate))

    if not vectors:
        parser.error("provide --state-counts or --n")

    seen = set()
    unique_vectors = []
    for ms in vectors:
        if ms not in seen:
            seen.add(ms)
            unique_vectors.append(ms)

    print(f"binary_mode={args.binary_mode}", flush=True)
    print(f"state_vectors={len(unique_vectors)}", flush=True)
    target_procs = None
    if args.target_procs:
        target_procs = tuple(int(part) for part in args.target_procs.split(",") if part)
    for ms in unique_vectors:
        max_len = args.max_len if args.max_len is not None else 3 * len(ms) + 6
        print(f"vector={list(ms)} product={product(ms)} max_len={max_len}", flush=True)
        if args.search_bn_clean:
            result = find_bn_clean_cycle(
                ms,
                max_length=max_len,
                required_neighbors=args.required_binary_neighbors,
                min_neighbors=args.min_binary_neighbors,
                target_procs=target_procs,
            )
            print(
                f"  target_procs={list(result.target_procs)} nodes={result.nodes} "
                f"strict_bn_clean_cycles_checked={result.strict_cycles_checked}",
                flush=True,
            )
            if result.found:
                print(f"  FOUND bn-clean strict cycle: {result.word}", flush=True)
            else:
                print("  no bn-clean strict cycle found", flush=True)
            continue
        summarize_state_vector(ms, max_len, args.limit_words)


if __name__ == "__main__":
    main()
