#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Tuple


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


def mixed_radix_code(cfg: Config, radices: Sequence[int]) -> int:
    code = 0
    mul = 1
    for x, base in zip(cfg, radices):
        code += x * mul
        mul *= base
    return code


def all_configs(n: int) -> List[Config]:
    counts = state_counts(n)
    return [tuple(xs) for xs in itertools.product(*(range(m) for m in counts))]


def canonical_rotate_cycle(cycle: Sequence[Config]) -> Tuple[Config, ...]:
    if not cycle:
        return ()
    rotations = [tuple(cycle[k:]) + tuple(cycle[:k]) for k in range(len(cycle))]
    return min(rotations)


@dataclass(frozen=True)
class GoodCycleData:
    configs: Tuple[Config, ...]
    movers: Tuple[int, ...]


def enumerate_good_cycles(n: int) -> List[GoodCycleData]:
    succ: Dict[Config, Config] = {}
    mover_at: Dict[Config, int] = {}
    for cfg in all_configs(n):
        privs = [i for i in range(n) if privileged(cfg, i)]
        if len(privs) != 1:
            continue
        p = privs[0]
        nxt = move(cfg, p)
        succ[cfg] = nxt
        mover_at[cfg] = p

    seen: set[Config] = set()
    raw_cycles: List[List[Config]] = []
    for start in succ:
        if start in seen:
            continue
        path: List[Config] = []
        index: Dict[Config, int] = {}
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

    dedup: Dict[Tuple[Config, ...], GoodCycleData] = {}
    for cycle in raw_cycles:
        movers = tuple(mover_at[cfg] for cfg in cycle)
        if len(set(movers)) != n:
            continue
        canon_cfgs = canonical_rotate_cycle(cycle)
        if canon_cfgs in dedup:
            continue
        l = len(cycle)
        rot = next(k for k in range(l) if tuple(cycle[k:]) + tuple(cycle[:k]) == canon_cfgs)
        canon_movers = tuple(movers[rot:]) + tuple(movers[:rot])
        dedup[canon_cfgs] = GoodCycleData(canon_cfgs, canon_movers)

    return sorted(dedup.values(), key=lambda gc: gc.configs)


def shorter_interval(i0: int, t: int, n: int) -> Tuple[Tuple[int, ...], str]:
    dist_right = (t - i0) % n
    dist_left = (i0 - t) % n
    if dist_right <= dist_left:
        cur = i0
        out = [cur]
        while cur != t:
            cur = right(n, cur)
            out.append(cur)
        return tuple(out), "R"
    cur = i0
    out = [cur]
    while cur != t:
        cur = left(n, cur)
        out.append(cur)
    return tuple(out), "L"


def first_t_change(configs: Sequence[Config], t: int) -> int | None:
    c0 = configs[0]
    for j, cfg in enumerate(configs):
        if cfg[t] != c0[t]:
            return j
    return None


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


@dataclass(frozen=True)
class PrefixCheck:
    t: int
    i0: int
    p_last: int
    j_t: int
    k_t: int
    interval: Tuple[int, ...]
    direction: str
    hk_last: bool
    hp_near_i0: bool
    changed_support: Tuple[int, ...]
    visits_interval: bool
    changed_interval: bool
    prefix_exact: bool
    monotone_no_backtrack: bool
    per_point_unique_visit: bool
    all_hp_exists: bool
    all_hp_not_before: bool
    all_hp_not_after: bool
    contexts_before_t: Tuple[Tuple[int, Tuple[int, int, int]], ...]


def analyze_t(configs: Sequence[Config], movers: Sequence[int], t: int) -> PrefixCheck:
    n = len(movers)
    i0 = movers[0]
    p_last = movers[-1]
    interval, direction = shorter_interval(i0, t, n)
    j_t = first_t_change(configs, t)
    if j_t is None:
        raise ValueError(f"processor {t} never changes")
    if j_t == 0:
        raise ValueError(f"unexpected j_t=0 for t={t}")
    k_t = j_t - 1
    if movers[k_t] != t:
        raise ValueError(f"expected mover[{k_t}] == t for t={t}, got {movers[k_t]}")

    prefix = tuple(movers[:j_t])
    prefix_set = set(prefix)
    changed_support = tuple(i for i, x in enumerate(configs[j_t]) if x != configs[0][i])
    visits_interval = set(interval).issubset(prefix_set)
    changed_interval = set(interval).issubset(changed_support)
    prefix_exact = prefix == interval

    monotone_no_backtrack = True
    for a, b in zip(prefix, prefix[1:]):
        if direction == "R":
            ok = b == a or b == right(n, a)
        else:
            ok = b == a or b == left(n, a)
        if not ok:
            monotone_no_backtrack = False
            break

    per_point_unique_visit = True
    all_hp_exists = True
    all_hp_not_before = True
    all_hp_not_after = True
    for p in interval[:-1]:
        hits = [k for k in range(j_t) if movers[k] == p]
        if not hits:
            all_hp_exists = False
            per_point_unique_visit = False
            all_hp_not_before = False
            all_hp_not_after = False
            continue
        k_p = hits[0]
        if len(hits) != 1:
            per_point_unique_visit = False
        if any(movers[k] == p for k in range(k_p)):
            all_hp_not_before = False
        if any(movers[k] == p for k in range(k_p + 1, j_t)):
            all_hp_not_after = False

    contexts_before_t = tuple(
        (movers[k], local_context(configs[k], movers[k])) for k in range(j_t)
    )

    return PrefixCheck(
        t=t,
        i0=i0,
        p_last=p_last,
        j_t=j_t,
        k_t=k_t,
        interval=interval,
        direction=direction,
        hk_last=(movers[-1] not in local_five(t, n)),
        hp_near_i0=(p_last in {i0, left(n, i0), right(n, i0)}),
        changed_support=changed_support,
        visits_interval=visits_interval,
        changed_interval=changed_interval,
        prefix_exact=prefix_exact,
        monotone_no_backtrack=monotone_no_backtrack,
        per_point_unique_visit=per_point_unique_visit,
        all_hp_exists=all_hp_exists,
        all_hp_not_before=all_hp_not_before,
        all_hp_not_after=all_hp_not_after,
        contexts_before_t=contexts_before_t,
    )


def summarize_cycle(n: int, gc: GoodCycleData, cycle_idx: int) -> List[str]:
    counts = state_counts(n)
    config_codes = [mixed_radix_code(cfg, counts) for cfg in gc.configs]
    out: List[str] = []
    out.append(
        f"cycle[{cycle_idx}] length={len(gc.configs)} "
        f"movers={gc.movers} first_cfg={gc.configs[0]} first_code={config_codes[0]}"
    )

    hk_last_hits = []
    all_checks = []
    for t in range(n):
        check = analyze_t(gc.configs, gc.movers, t)
        all_checks.append(check)
        if check.hk_last:
            hk_last_hits.append(check)

    out.append(
        "  all_t: "
        f"prefix_exact={sum(c.prefix_exact for c in all_checks)}/{n} "
        f"changed_interval={sum(c.changed_interval for c in all_checks)}/{n} "
        f"visits_interval={sum(c.visits_interval for c in all_checks)}/{n}"
    )

    if not hk_last_hits:
        out.append("  hk_last: none")
        return out

    out.append(f"  hk_last_count={len(hk_last_hits)}")
    for hit in hk_last_hits:
        out.append(
            "  "
            f"t={hit.t} i0={hit.i0} p_last={hit.p_last} near_i0={hit.hp_near_i0} "
            f"j_t={hit.j_t} k_t={hit.k_t} dir={hit.direction} interval={hit.interval}"
        )
        out.append(
            "    "
            f"visits_interval={hit.visits_interval} changed_interval={hit.changed_interval} "
            f"prefix_exact={hit.prefix_exact} monotone={hit.monotone_no_backtrack}"
        )
        out.append(
            "    "
            f"hk_p_exists={hit.all_hp_exists} "
            f"hp_not_before={hit.all_hp_not_before} "
            f"hp_not_after={hit.all_hp_not_after} "
            f"unique_visit={hit.per_point_unique_visit}"
        )
        out.append(
            "    "
            f"changed_support_at_j_t={hit.changed_support} "
            f"contexts_before_t={hit.contexts_before_t}"
        )
    return out


def run_one_n(n: int) -> List[str]:
    out: List[str] = []
    cycles = enumerate_good_cycles(n)
    out.append(
        f"n={n} state_counts={state_counts(n)} total_states={len(all_configs(n))} "
        f"good_cycles={len(cycles)}"
    )
    for idx, gc in enumerate(cycles):
        out.extend(summarize_cycle(n, gc, idx))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Probe first-t-change interval filling on CUP-2 good cycles."
    )
    parser.add_argument(
        "--n",
        type=int,
        nargs="*",
        default=[5, 6, 7],
        help="Ring sizes to enumerate.",
    )
    args = parser.parse_args()

    for n in args.n:
        for line in run_one_n(n):
            print(line)


if __name__ == "__main__":
    main()
