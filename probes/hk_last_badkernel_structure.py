#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from dataclasses import dataclass

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
GPT_ROOT = os.path.abspath(os.path.join(REPO_ROOT, "..", "gpt"))
GPT_SCRIPTS = os.path.join(GPT_ROOT, "scripts")
sys.path.insert(0, GPT_ROOT)
sys.path.insert(0, GPT_SCRIPTS)

from p2_cycle_screen import forced_rule_map  # type: ignore
from p2_good_cycle_search import enumerate_good_cycles, local_context  # type: ignore
from p2_completion_search import screening_data  # type: ignore


Config = tuple[int, ...]


def left(n: int, i: int) -> int:
    return (i - 1) % n


def right(n: int, i: int) -> int:
    return (i + 1) % n


def choose_alt(value: int, modulus: int) -> int:
    return (value + 1) % modulus


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def pivots(state_counts: tuple[int, ...]) -> list[int]:
    n = len(state_counts)
    return [
        i
        for i in range(n)
        if state_counts[left(n, i)] == 2 and state_counts[right(n, i)] == 2
    ]


def hk_last_hits(movers: tuple[int, ...], state_counts: tuple[int, ...]) -> list[tuple[int, int]]:
    n = len(state_counts)
    hits: list[tuple[int, int]] = []
    for t in pivots(state_counts):
        outside = [k for k, mover in enumerate(movers) if mover not in local_five(t, n)]
        if outside and outside[-1] + 1 == len(movers):
            hits.append((t, outside[-1]))
    return hits


def shorter_interval(i0: int, t: int, n: int) -> tuple[tuple[int, ...], str]:
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


def first_t_change(cycle: tuple[Config, ...], t: int) -> tuple[int, Config] | None:
    c0 = cycle[0]
    for j, cfg in enumerate(cycle):
        if cfg[t] != c0[t]:
            return j, cfg
    return None


def mover_prefix_monotone_to_first_t(
    movers: tuple[int, ...], t: int, n: int
) -> tuple[bool, int | None, tuple[int, ...], str]:
    i0 = movers[0]
    interval, direction = shorter_interval(i0, t, n)
    k_t = None
    for k, mover in enumerate(movers):
        if k > 0 and mover == t:
            k_t = k
            break
    if k_t is None:
        return False, None, interval, direction
    for k in range(k_t - 1):
        a = movers[k]
        b = movers[k + 1]
        if direction == "R" and b not in {a, right(n, a)}:
            return False, k_t, interval, direction
        if direction == "L" and b not in {a, left(n, a)}:
            return False, k_t, interval, direction
    return True, k_t, interval, direction


def interval_filled_at_first_t_change(
    cycle: tuple[Config, ...], movers: tuple[int, ...], t: int
) -> tuple[bool, int | None, tuple[int, ...], tuple[int, ...]]:
    i0 = movers[0]
    interval, _ = shorter_interval(i0, t, len(movers))
    first = first_t_change(cycle, t)
    if first is None:
        return False, None, interval, ()
    j_t, cfg = first
    c0 = cycle[0]
    changed = tuple(p for p in interval if cfg[p] != c0[p])
    return set(interval).issubset(changed), j_t, interval, changed


def in_mover_template(c: Config, cycle: tuple[Config, ...], movers: tuple[int, ...]) -> list[int]:
    n = len(c)
    out: list[int] = []
    for j, gcfg in enumerate(cycle):
        p = movers[j]
        if (
            c[left(n, p)] == gcfg[left(n, p)]
            and c[p] == gcfg[p]
            and c[right(n, p)] == gcfg[right(n, p)]
        ):
            out.append(j)
    return out


def cflip2(state_counts: tuple[int, ...], cycle: tuple[Config, ...], movers: tuple[int, ...], t: int) -> Config:
    c0 = list(cycle[0])
    i0 = movers[0]
    c0[i0] = choose_alt(c0[i0], state_counts[i0])
    c0[t] = choose_alt(c0[t], state_counts[t])
    return tuple(c0)


def forced_successors(
    cfg: Config, state_counts: tuple[int, ...], forced_map: dict[tuple[int, tuple[int, int, int]], int]
) -> list[tuple[int, Config]]:
    out: list[tuple[int, Config]] = []
    n = len(state_counts)
    for processor in range(n):
        key = (processor, local_context(cfg, processor))
        value = forced_map.get(key)
        if value is None or value == cfg[processor]:
            continue
        nxt = list(cfg)
        nxt[processor] = value
        out.append((processor, tuple(nxt)))
    return out


@dataclass(frozen=True)
class KernelSummary:
    state_counts: tuple[int, ...]
    cycle_length: int
    movers: tuple[int, ...]
    t: int
    k_out: int
    k0_size: int
    off_cycle_states: int
    missing_from_k0: tuple[Config, ...]
    cflip2_off_cycle: bool
    cflip2_in_k0: bool
    dead_states: tuple[Config, ...]
    chain_prefix: tuple[Config, ...]
    period_start: int | None
    period_length: int | None
    prefix_monotone: bool
    first_t_move_index: int | None
    shorter_interval: tuple[int, ...]
    interval_direction: str
    first_t_change_fills_interval: bool
    first_t_change_index: int | None
    first_t_change_support: tuple[int, ...]


def summarize_hit(
    state_counts: tuple[int, ...], cycle: tuple[Config, ...], movers: tuple[int, ...], t: int, k_out: int
) -> KernelSummary:
    forced_map = forced_rule_map(cycle, movers)
    all_cfgs = screening_data(state_counts).configs
    cycle_set = set(cycle)
    k0 = tuple(cfg for cfg in all_cfgs if cfg not in cycle_set and in_mover_template(cfg, cycle, movers))
    k0_set = set(k0)

    dead: list[Config] = []
    for cfg in k0:
        succs = [
            nxt
            for _, nxt in forced_successors(cfg, state_counts, forced_map)
            if nxt not in cycle_set and nxt in k0_set
        ]
        if not succs:
            dead.append(cfg)

    seed = cflip2(state_counts, cycle, movers, t)

    seen: dict[Config, int] = {}
    chain: list[Config] = []
    cur = seed
    while cur in k0_set and cur not in seen:
        seen[cur] = len(chain)
        chain.append(cur)
        succs = sorted(
            (processor, nxt)
            for processor, nxt in forced_successors(cur, state_counts, forced_map)
            if nxt not in cycle_set and nxt in k0_set
        )
        if not succs:
            break
        cur = succs[0][1]

    period_start = None
    period_length = None
    if cur in seen:
        period_start = seen[cur]
        period_length = len(chain) - period_start

    prefix_monotone, first_t_move_index, interval, direction = mover_prefix_monotone_to_first_t(
        movers, t, len(state_counts)
    )
    fills, j_t, _, support = interval_filled_at_first_t_change(cycle, movers, t)

    missing = tuple(cfg for cfg in all_cfgs if cfg not in cycle_set and cfg not in k0_set)
    return KernelSummary(
        state_counts=state_counts,
        cycle_length=len(cycle),
        movers=movers,
        t=t,
        k_out=k_out,
        k0_size=len(k0),
        off_cycle_states=len(all_cfgs) - len(cycle),
        missing_from_k0=missing,
        cflip2_off_cycle=seed not in cycle_set,
        cflip2_in_k0=seed in k0_set,
        dead_states=tuple(dead),
        chain_prefix=tuple(chain[:24]),
        period_start=period_start,
        period_length=period_length,
        prefix_monotone=prefix_monotone,
        first_t_move_index=first_t_move_index,
        shorter_interval=interval,
        interval_direction=direction,
        first_t_change_fills_interval=fills,
        first_t_change_index=j_t,
        first_t_change_support=support,
    )


def analyze_all_binary_family(n: int) -> dict[str, object]:
    state_counts = (2,) * n
    if n == 5:
        return {
            "n": n,
            "state_counts": state_counts,
            "hk_last_possible": False,
            "reason": "For n = 5, local_five(t) is the whole ring, so there is no outside mover.",
        }

    total_cycles = 0
    total_hits = 0
    failures: list[tuple[int, tuple[int, ...], int, str]] = []
    first_summary: KernelSummary | None = None

    for cycle_idx, (cycle, movers) in enumerate(
        enumerate_good_cycles(state_counts, max_cycles=500, time_limit=20.0),
        start=1,
    ):
        total_cycles = cycle_idx
        hits = hk_last_hits(movers, state_counts)
        for t, k_out in hits:
            total_hits += 1
            summary = summarize_hit(state_counts, cycle, movers, t, k_out)
            if first_summary is None:
                first_summary = summary
            if not summary.cflip2_off_cycle:
                failures.append((cycle_idx, movers, t, "cFlip2_on_cycle"))
            if not summary.cflip2_in_k0:
                failures.append((cycle_idx, movers, t, "cFlip2_not_in_K0"))
            if summary.dead_states:
                failures.append((cycle_idx, movers, t, f"K0_not_closed:{len(summary.dead_states)}"))

    if first_summary is None:
        return {
            "n": n,
            "state_counts": state_counts,
            "hk_last_possible": False,
            "reason": "No hk_last cycle found in the screened family.",
        }

    return {
        "n": n,
        "state_counts": state_counts,
        "hk_last_possible": True,
        "total_cycles": total_cycles,
        "hk_last_hits": total_hits,
        "all_hits_pass": not failures,
        "failures": failures[:8],
        "representative": first_summary,
    }


def analyze_mixed_comparison(state_counts: tuple[int, ...]) -> dict[str, object]:
    for cycle_idx, (cycle, movers) in enumerate(
        enumerate_good_cycles(state_counts, max_cycles=40, time_limit=8.0),
        start=1,
    ):
        hits = hk_last_hits(movers, state_counts)
        if not hits:
            continue
        t, k_out = hits[0]
        summary = summarize_hit(state_counts, cycle, movers, t, k_out)
        return {
            "state_counts": state_counts,
            "cycle_idx": cycle_idx,
            "representative": summary,
        }
    return {
        "state_counts": state_counts,
        "cycle_idx": None,
        "representative": None,
    }


def format_kernel_summary(summary: KernelSummary) -> list[str]:
    lines = [
        f"state_counts={summary.state_counts}",
        f"cycle_length={summary.cycle_length} movers={summary.movers}",
        f"hk_last=(t={summary.t}, k_out={summary.k_out})",
        f"|K0|={summary.k0_size} off_cycle_states={summary.off_cycle_states}",
        f"missing_from_K0_count={len(summary.missing_from_k0)}",
        f"cFlip2_off_cycle={summary.cflip2_off_cycle} cFlip2_in_K0={summary.cflip2_in_k0}",
        f"dead_states_in_K0={len(summary.dead_states)}",
        f"shorter_interval={summary.shorter_interval} dir={summary.interval_direction}",
        f"prefix_monotone_to_first_t={summary.prefix_monotone} first_t_move_index={summary.first_t_move_index}",
        (
            "first_t_change_fills_interval="
            f"{summary.first_t_change_fills_interval} "
            f"first_t_change_index={summary.first_t_change_index} "
            f"support={summary.first_t_change_support}"
        ),
        f"period_start={summary.period_start} period_length={summary.period_length}",
    ]
    if summary.missing_from_k0:
        lines.append(f"missing_from_K0_sample={summary.missing_from_k0[:8]}")
    if summary.dead_states:
        lines.append(f"dead_state_sample={summary.dead_states[:8]}")
    lines.append(f"chain_prefix={summary.chain_prefix}")
    return lines


def main() -> None:
    print("Exact Lean-local objects mirrored in Python")
    print("  cFlip2   := flip c0 at i0, then at t")
    print("  InMoverTemplate(c) := c matches some good config on (left p, p, right p)")
    print("  K0       := off-cycle configs satisfying InMoverTemplate")
    print("  badStep  := off-cycle step in the cycle-forced dynamics")
    print()

    print("Binary hk_last families")
    for n in (5, 6, 7, 8):
        result = analyze_all_binary_family(n)
        print(f"\n[n={n}]")
        if not result["hk_last_possible"]:
            print(f"  hk_last_possible=False reason={result['reason']}")
            continue
        print(
            f"  total_cycles={result['total_cycles']} hk_last_hits={result['hk_last_hits']} "
            f"all_hits_pass={result['all_hits_pass']}"
        )
        for line in format_kernel_summary(result["representative"]):
            print(f"  {line}")
        if result["failures"]:
            print(f"  failure_sample={result['failures']}")

    print("\nMixed comparison families")
    for state_counts in (
        (2, 2, 2, 2, 2, 10),
        (2, 2, 2, 2, 2, 2, 14),
        (2, 2, 2, 2, 2, 2, 2, 22),
    ):
        result = analyze_mixed_comparison(state_counts)
        print(f"\n[state_counts={state_counts}]")
        if result["representative"] is None:
            print("  no hk_last hit found in search budget")
            continue
        print(f"  cycle_idx={result['cycle_idx']}")
        for line in format_kernel_summary(result["representative"]):
            print(f"  {line}")


if __name__ == "__main__":
    main()
