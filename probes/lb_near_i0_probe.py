#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
from dataclasses import dataclass
from typing import Iterable, List, Sequence, Tuple


Config = Tuple[int, ...]


TBOT = {
    (0, 0, 0): 1,
    (0, 0, 1): 1,
    (0, 0, 2): 0,
    (0, 1, 0): 1,
    (0, 1, 1): 1,
    (0, 1, 2): 1,
    (1, 0, 0): 0,
    (1, 0, 1): 1,
    (1, 0, 2): 0,
    (1, 1, 0): 0,
    (1, 1, 1): 1,
    (1, 1, 2): 0,
}

TLOW = {
    (0, 0, 0): 0,
    (0, 0, 1): 0,
    (0, 0, 2): 0,
    (0, 1, 0): 0,
    (0, 1, 1): 1,
    (0, 1, 2): 0,
    (0, 2, 0): 0,
    (0, 2, 1): 2,
    (0, 2, 2): 0,
    (1, 0, 0): 1,
    (1, 0, 1): 1,
    (1, 0, 2): 1,
    (1, 1, 0): 1,
    (1, 1, 1): 1,
    (1, 1, 2): 2,
    (1, 2, 0): 0,
    (1, 2, 1): 1,
    (1, 2, 2): 2,
}

TMID = {
    (0, 0, 0): 0,
    (0, 0, 1): 0,
    (0, 0, 2): 0,
    (0, 1, 0): 0,
    (0, 1, 1): 1,
    (0, 1, 2): 0,
    (0, 2, 0): 0,
    (0, 2, 1): 2,
    (0, 2, 2): 0,
    (1, 0, 0): 1,
    (1, 0, 1): 1,
    (1, 0, 2): 1,
    (1, 1, 0): 1,
    (1, 1, 1): 1,
    (1, 1, 2): 2,
    (1, 2, 0): 0,
    (1, 2, 1): 1,
    (1, 2, 2): 2,
    (2, 0, 0): 0,
    (2, 0, 1): 0,
    (2, 0, 2): 2,
    (2, 1, 0): 1,
    (2, 1, 1): 0,
    (2, 1, 2): 2,
    (2, 2, 0): 0,
    (2, 2, 1): 2,
    (2, 2, 2): 2,
}

THIGH = {
    (0, 0, 0): 0,
    (0, 0, 1): 0,
    (0, 1, 0): 0,
    (0, 1, 1): 0,
    (0, 2, 0): 0,
    (0, 2, 1): 0,
    (1, 0, 0): 1,
    (1, 0, 1): 1,
    (1, 1, 0): 1,
    (1, 1, 1): 2,
    (1, 2, 0): 0,
    (1, 2, 1): 2,
    (2, 0, 0): 0,
    (2, 0, 1): 2,
    (2, 1, 0): 0,
    (2, 1, 1): 2,
    (2, 2, 0): 2,
    (2, 2, 1): 2,
}

TTOP = {
    (0, 0, 0): 0,
    (0, 0, 1): 0,
    (0, 1, 0): 0,
    (0, 1, 1): 0,
    (1, 0, 0): 0,
    (1, 0, 1): 1,
    (1, 1, 0): 1,
    (1, 1, 1): 1,
    (2, 0, 0): 1,
    (2, 0, 1): 1,
    (2, 1, 0): 1,
    (2, 1, 1): 1,
}


def left(n: int, i: int) -> int:
    return (i - 1) % n


def right(n: int, i: int) -> int:
    return (i + 1) % n


def state_counts(n: int) -> Tuple[int, ...]:
    return tuple(2 if i == 0 or i == n - 1 else 3 for i in range(n))


def cup2_out(n: int, i: int, l: int, s: int, r: int) -> int:
    if i == 0:
        return TBOT.get((l, s, r), 0)
    if i == 1:
        return TLOW.get((l, s, r), 0)
    if i == n - 1:
        return TTOP.get((l, s, r), 0)
    if i == n - 2:
        return THIGH.get((l, s, r), 0)
    return TMID.get((l, s, r), 0)


def local_context(cfg: Config, i: int) -> Tuple[int, int, int]:
    n = len(cfg)
    return cfg[left(n, i)], cfg[i], cfg[right(n, i)]


def privileged(cfg: Config, i: int) -> bool:
    l, s, r = local_context(cfg, i)
    return cup2_out(len(cfg), i, l, s, r) != s


def move(cfg: Config, i: int) -> Config:
    out = list(cfg)
    l, s, r = local_context(cfg, i)
    out[i] = cup2_out(len(cfg), i, l, s, r)
    return tuple(out)


def all_configs(n: int) -> List[Config]:
    counts = state_counts(n)
    return [tuple(xs) for xs in itertools.product(*(range(m) for m in counts))]


def canonical_rotate_cycle(cycle: Sequence[Config]) -> Tuple[Config, ...]:
    rotations = [tuple(cycle[k:]) + tuple(cycle[:k]) for k in range(len(cycle))]
    return min(rotations)


@dataclass(frozen=True)
class GoodCycleData:
    configs: Tuple[Config, ...]
    movers: Tuple[int, ...]


def enumerate_good_cycles(n: int) -> List[GoodCycleData]:
    succ: dict[Config, Config] = {}
    mover_at: dict[Config, int] = {}
    for cfg in all_configs(n):
        privs = [i for i in range(n) if privileged(cfg, i)]
        if len(privs) != 1:
            continue
        p = privs[0]
        succ[cfg] = move(cfg, p)
        mover_at[cfg] = p

    seen: set[Config] = set()
    raw_cycles: List[List[Config]] = []
    for start in succ:
        if start in seen:
            continue
        path: List[Config] = []
        index: dict[Config, int] = {}
        cur = start
        while cur in succ and cur not in seen and cur not in index:
            index[cur] = len(path)
            path.append(cur)
            cur = succ[cur]
        seen.update(path)
        if cur in index:
            cyc = path[index[cur]:]
            if succ[cyc[-1]] == cyc[0]:
                raw_cycles.append(cyc)

    dedup: dict[Tuple[Config, ...], GoodCycleData] = {}
    for cycle in raw_cycles:
        movers = tuple(mover_at[cfg] for cfg in cycle)
        if len(set(movers)) != n:
            continue
        canon_cfgs = canonical_rotate_cycle(cycle)
        if canon_cfgs in dedup:
            continue
        rot = next(
            k
            for k in range(len(cycle))
            if tuple(cycle[k:]) + tuple(cycle[:k]) == canon_cfgs
        )
        canon_movers = tuple(movers[rot:]) + tuple(movers[:rot])
        dedup[canon_cfgs] = GoodCycleData(canon_cfgs, canon_movers)

    return sorted(dedup.values(), key=lambda gc: gc.configs)


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def local_three(t: int, n: int) -> set[int]:
    return {left(n, t), t, right(n, t)}


def cyclic_open_interval(word: Sequence[int], start: int, stop: int) -> Tuple[int, ...]:
    out: List[int] = []
    k = (start + 1) % len(word)
    while k != stop:
        out.append(word[k])
        k = (k + 1) % len(word)
    return tuple(out)


def mechanism_triggering(j: int, k: int) -> bool:
    return ((j % 2 == 0) and (k % 2 == 0)) or (j >= 2 and k == 0) or (j == 0 and k >= 2)


def canonical_gap_profiles(movers: Sequence[int], t: int, n: int) -> List[Tuple[int, int]]:
    fires = [idx for idx, mover in enumerate(movers) if mover == t]
    out: List[Tuple[int, int]] = []
    for idx, cur in enumerate(fires):
        nxt = fires[(idx + 1) % len(fires)]
        gap = cyclic_open_interval(movers, cur, nxt)
        j = sum(1 for mover in gap if mover == left(n, t))
        k = sum(1 for mover in gap if mover == right(n, t))
        out.append((j, k))
    return out


@dataclass(frozen=True)
class HkLastNearWitness:
    t: int
    i0: int
    k_out: int
    p_out: int
    near_role: str
    local5: Tuple[int, ...]
    local3: Tuple[int, ...]
    overlap_i0_local5: int
    union_i0_local5: int
    first_local_index: int
    first_local_mover: int
    first_local_role: str
    first_t_index: int
    same_t_triple_kout0: bool
    t_triple_changed_before_t: bool
    same_neighbor_triple_0_first: bool
    neighbor_outer_changed_before_first: bool
    wrap_prefix_to_t: Tuple[int, ...]
    canonical_gap_profiles: Tuple[Tuple[int, int], ...]
    all_canonical_gaps_normal: bool


def near_role(i0: int, p: int, n: int) -> str | None:
    if p == i0:
        return "self"
    if p == left(n, i0):
        return "left(i0)"
    if p == right(n, i0):
        return "right(i0)"
    return None


def local_role(t: int, p: int, n: int) -> str | None:
    if p == left(n, t):
        return "left(t)"
    if p == t:
        return "t"
    if p == right(n, t):
        return "right(t)"
    return None


def analyze_hk_last_near(gc: GoodCycleData, n: int) -> List[HkLastNearWitness]:
    movers = gc.movers
    configs = gc.configs
    i0 = movers[0]
    out: List[HkLastNearWitness] = []

    for t in range(n):
        outside = [k for k, mover in enumerate(movers) if mover not in local_five(t, n)]
        if not outside:
            continue
        k_out = outside[-1]
        if k_out + 1 != len(movers):
            continue
        p_out = movers[k_out]
        p_role = near_role(i0, p_out, n)
        if p_role is None:
            continue

        l3 = local_three(t, n)
        first_local_index = next(idx for idx, mover in enumerate(movers) if mover in l3)
        first_local_mover = movers[first_local_index]
        first_t_index = next(idx for idx, mover in enumerate(movers) if mover == t)
        first_local_kind = local_role(t, first_local_mover, n)
        assert first_local_kind is not None

        lt = left(n, t)
        rt = right(n, t)
        t_triple_0 = (configs[0][lt], configs[0][t], configs[0][rt])
        t_triple_kout = (configs[k_out][lt], configs[k_out][t], configs[k_out][rt])
        t_triple_first_t = (configs[first_t_index][lt], configs[first_t_index][t], configs[first_t_index][rt])

        if first_local_mover == lt:
            outer = left(n, lt)
            neighbor_triple_0 = (configs[0][outer], configs[0][lt], configs[0][t])
            neighbor_triple_first = (
                configs[first_local_index][outer],
                configs[first_local_index][lt],
                configs[first_local_index][t],
            )
        elif first_local_mover == rt:
            outer = right(n, rt)
            neighbor_triple_0 = (configs[0][t], configs[0][rt], configs[0][outer])
            neighbor_triple_first = (
                configs[first_local_index][t],
                configs[first_local_index][rt],
                configs[first_local_index][outer],
            )
        else:
            outer = -1
            neighbor_triple_0 = ()
            neighbor_triple_first = ()

        overlap = len(local_five(t, n) & {left(n, i0), i0, right(n, i0)})
        union = len(local_five(t, n) | {left(n, i0), i0, right(n, i0)})
        gap_profiles = tuple(canonical_gap_profiles(movers, t, n))

        out.append(
            HkLastNearWitness(
                t=t,
                i0=i0,
                k_out=k_out,
                p_out=p_out,
                near_role=p_role,
                local5=tuple(sorted(local_five(t, n))),
                local3=tuple(sorted(l3)),
                overlap_i0_local5=overlap,
                union_i0_local5=union,
                first_local_index=first_local_index,
                first_local_mover=first_local_mover,
                first_local_role=first_local_kind,
                first_t_index=first_t_index,
                same_t_triple_kout0=(t_triple_kout == t_triple_0),
                t_triple_changed_before_t=(t_triple_first_t != t_triple_0),
                same_neighbor_triple_0_first=(neighbor_triple_0 == neighbor_triple_first),
                neighbor_outer_changed_before_first=(
                    outer != -1 and any(movers[j] == outer for j in range(first_local_index))
                ),
                wrap_prefix_to_t=tuple(movers[: first_t_index + 1]),
                canonical_gap_profiles=gap_profiles,
                all_canonical_gaps_normal=all(
                    not mechanism_triggering(j, k) for j, k in gap_profiles
                ),
            )
        )
    return out


def summarize_cycle(n: int, cycle_idx: int, gc: GoodCycleData) -> Iterable[str]:
    yield (
        f"cycle[{cycle_idx}] len={len(gc.configs)} "
        f"movers={gc.movers}"
    )
    witnesses = analyze_hk_last_near(gc, n)
    if not witnesses:
        yield "  hk_last_near_i0: none"
        return

    yield f"  hk_last_near_i0_count={len(witnesses)}"
    for w in witnesses:
        yield (
            f"  t={w.t} i0={w.i0} k_out={w.k_out} p_out={w.p_out} "
            f"near={w.near_role} local5={w.local5} local3={w.local3}"
        )
        yield (
            f"    overlap(N5(t),N3(i0))={w.overlap_i0_local5} "
            f"union_size={w.union_i0_local5} "
            f"same_t_triple(k_out,0)={w.same_t_triple_kout0}"
        )
        yield (
            f"    wrap_prefix_to_first_t={w.wrap_prefix_to_t} "
            f"first_local=({w.first_local_index},{w.first_local_mover},{w.first_local_role}) "
            f"first_t={w.first_t_index}"
        )
        yield (
            f"    t_triple_changed_before_t={w.t_triple_changed_before_t} "
            f"same_neighbor_triple_0_first={w.same_neighbor_triple_0_first} "
            f"neighbor_outer_changed_before_first={w.neighbor_outer_changed_before_first}"
        )
        yield (
            f"    canonical_gap_profiles={w.canonical_gap_profiles} "
            f"all_canonical_gaps_normal={w.all_canonical_gaps_normal}"
        )


def diagnose(n: int, cycles: Sequence[GoodCycleData]) -> List[str]:
    lines = [
        f"n={n} state_counts={state_counts(n)} total_states={len(all_configs(n))} good_cycles={len(cycles)}"
    ]
    hit_count = 0
    transition_possible = 0
    neighbor_first = 0
    all_normal_hits = 0

    for idx, gc in enumerate(cycles):
        lines.extend(summarize_cycle(n, idx, gc))
        for w in analyze_hk_last_near(gc, n):
            hit_count += 1
            transition_possible += 1
            if w.first_local_role != "t":
                neighbor_first += 1
            if w.all_canonical_gaps_normal:
                all_normal_hits += 1

    if hit_count == 0:
        lines.append("summary: no hk_last_near_i0 witnesses")
        return lines

    lines.append(
        f"summary: hk_last_near_i0_hits={hit_count} "
        f"neighbor_first_hits={neighbor_first} "
        f"transition_realized_hits={transition_possible} "
        f"all_canonical_gaps_normal_hits={all_normal_hits}"
    )
    if all_normal_hits == 0:
        lines.append(
            "diagnosis: in these exact CUP-2 cycles the scenario exists, "
            "but every such witness already violates allNormalForm via a "
            "canonical gap with (J,K) = (0,2) or (2,0)."
        )
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Probe the hk_last + near-i0 branch on exact CUP-2 good cycles."
        )
    )
    parser.add_argument("--n", type=int, nargs="*", default=[5, 6, 7])
    args = parser.parse_args()

    for n in args.n:
        cycles = enumerate_good_cycles(n)
        for line in diagnose(n, cycles):
            print(line)


if __name__ == "__main__":
    main()
