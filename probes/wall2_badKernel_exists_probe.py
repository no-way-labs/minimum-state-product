#!/usr/bin/env python3
"""Probe the `badKernel_exists` sorry in `AllNormalFormFalse.lean`.

This script instantiates the `K₀` / `cFlip₂` construction on the explicit
`w5` witness from `SmallN/Defs.lean`:

  - n = 5
  - state counts = (2, 2, 2, 3, 4)
  - explicit good cycle `w5GoodCycleCodes`
  - explicit transition tables `w5P0`..`w5P4`

The goal is not to prove the theorem for `w5`, but to expose the structure:
  1. enumerate the good cycle configs and movers,
  2. build `cFlip₂`,
  3. check whether `cFlip₂` is off-cycle,
  4. construct `K₀`,
  5. examine successor closure inside `K₀`,
  6. trace a deterministic witness-successor chain from `cFlip₂`.
"""

from __future__ import annotations

import itertools
import re
from collections import Counter
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
DEFS_PATH = ROOT / "lean" / "LeanMn" / "SmallN" / "Defs.lean"
GPT_SCRIPTS = ROOT / "gpt" / "scripts"
sys.path.insert(0, str(GPT_SCRIPTS))

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore


def left(n: int, i: int) -> int:
    return (i + n - 1) % n


def right(n: int, i: int) -> int:
    return (i + 1) % n


def next_index(length: int, k: int) -> int:
    return (k + 1) % length


def parse_match_table(src: str, name: str) -> tuple[dict[tuple[int, int, int], int], int]:
    pattern = rf"private def {name} \(L S R : Nat\) : Nat :=\n  match L, S, R with\n((?:  \|.*\n)+)"
    m = re.search(pattern, src)
    if m is None:
        raise ValueError(f"could not find {name}")
    table: dict[tuple[int, int, int], int] = {}
    default = 0
    for raw in m.group(1).splitlines():
        raw = raw.strip()
        case_m = re.match(r"\|\s*([^,]+),\s*([^,]+),\s*([^ ]+)\s*=>\s*(\d+)", raw)
        if case_m is None:
            raise ValueError(f"bad case line in {name}: {raw}")
        a, b, c, out = case_m.groups()
        out_i = int(out)
        if a == "_" or b == "_" or c == "_":
            default = out_i
            continue
        table[(int(a), int(b), int(c))] = out_i
    return table, default


def parse_good_cycle_codes(src: str) -> list[int]:
    m = re.search(r"def w5GoodCycleCodes : List Nat := \[(.*?)\]", src, re.S)
    if m is None:
        raise ValueError("could not find w5GoodCycleCodes")
    return [int(x) for x in re.findall(r"\d+", m.group(1))]


class W5System:
    n = 5
    ms = (2, 2, 2, 3, 4)

    def __init__(self) -> None:
        src = DEFS_PATH.read_text()
        self.tables = {}
        self.defaults = {}
        for name in ["w5P0", "w5P1", "w5P2", "w5P3", "w5P4"]:
            table, default = parse_match_table(src, name)
            self.tables[name] = table
            self.defaults[name] = default
        self.good_cycle_codes = parse_good_cycle_codes(src)
        self.good_cycle = [self.cfg_of_code(code) for code in self.good_cycle_codes]
        self.good_set = set(self.good_cycle)
        self.good_movers = [self.unique_privileged(cfg) for cfg in self.good_cycle]
        self._verify_good_cycle()

    def out_val(self, i: int, L: int, S: int, R: int) -> int:
        name = f"w5P{i}"
        return self.tables[name].get((L, S, R), self.defaults[name])

    def cfg_of_code(self, k: int) -> tuple[int, ...]:
        return (
            (k // 1) % 2,
            (k // 2) % 2,
            (k // 4) % 2,
            (k // 8) % 3,
            (k // 24) % 4,
        )

    def code_of_cfg(self, cfg: tuple[int, ...]) -> int:
        return cfg[0] + 2 * (cfg[1] + 2 * (cfg[2] + 2 * (cfg[3] + 3 * cfg[4])))

    def privileged(self, cfg: tuple[int, ...], i: int) -> bool:
        out = self.out_val(i, cfg[left(self.n, i)], cfg[i], cfg[right(self.n, i)])
        return out != cfg[i]

    def move(self, cfg: tuple[int, ...], i: int) -> tuple[int, ...]:
        out = self.out_val(i, cfg[left(self.n, i)], cfg[i], cfg[right(self.n, i)])
        nxt = list(cfg)
        nxt[i] = out
        return tuple(nxt)

    def unique_privileged(self, cfg: tuple[int, ...]) -> int:
        movers = [i for i in range(self.n) if self.privileged(cfg, i)]
        if len(movers) != 1:
            raise ValueError(f"expected unique privileged mover, got {movers} at {cfg}")
        return movers[0]

    def all_configs(self):
        return itertools.product(*(range(m) for m in self.ms))

    def _verify_good_cycle(self) -> None:
        for j, cfg in enumerate(self.good_cycle):
            mover = self.good_movers[j]
            nxt = self.move(cfg, mover)
            want = self.good_cycle[next_index(len(self.good_cycle), j)]
            if nxt != want:
                raise ValueError(f"good cycle closure failed at j={j}: {cfg} --{mover}--> {nxt} != {want}")


def fire_counts(movers: list[int], n: int) -> list[int]:
    counts = [0] * n
    for p in movers:
        counts[p] += 1
    return counts


def flip_config(cfg: tuple[int, ...], q: int, v: int) -> tuple[int, ...]:
    out = list(cfg)
    out[q] = v
    return tuple(out)


def choose_alt(value: int, modulus: int) -> int:
    return (value + 1) % modulus


def witnesses(sys: W5System, cfg: tuple[int, ...], movers: list[int], cycle: list[tuple[int, ...]]) -> list[int]:
    out = []
    for j, good in enumerate(cycle):
        p = movers[j]
        if (
            cfg[left(sys.n, p)] == good[left(sys.n, p)]
            and cfg[p] == good[p]
            and cfg[right(sys.n, p)] == good[right(sys.n, p)]
        ):
            out.append(j)
    return out


def bad_successors(sys: W5System, cfg: tuple[int, ...]) -> list[tuple[int, tuple[int, ...]]]:
    out = []
    for p in range(sys.n):
        if not sys.privileged(cfg, p):
            continue
        nxt = sys.move(cfg, p)
        if nxt not in sys.good_set:
            out.append((p, nxt))
    return out


def kernel_successors(
    sys: W5System,
    cfg: tuple[int, ...],
    K0: set[tuple[int, ...]],
    movers: list[int],
    cycle: list[tuple[int, ...]],
) -> list[tuple[int, int, tuple[int, ...]]]:
    out = []
    for j in witnesses(sys, cfg, movers, cycle):
        p = movers[j]
        if not sys.privileged(cfg, p):
            continue
        nxt = sys.move(cfg, p)
        if nxt in K0 and nxt not in sys.good_set:
            out.append((j, p, nxt))
    return out


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def pivots(ms: tuple[int, ...]) -> list[int]:
    n = len(ms)
    return [i for i in range(n) if ms[left(n, i)] == 2 and ms[right(n, i)] == 2]


def hk_last_instances(movers: tuple[int, ...], n: int, pivs: list[int]) -> list[tuple[int, int]]:
    hits = []
    for t in pivs:
        outside = [idx for idx, mover in enumerate(movers) if mover not in local_five(t, n)]
        if outside and outside[-1] + 1 == len(movers):
            hits.append((t, outside[-1]))
    return hits


def find_hk_last_witness(ms: tuple[int, ...]):
    n = len(ms)
    pivs = pivots(ms)
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        if all(movers[k] == k % n for k in range(len(movers))):
            continue
        if all(movers[k] == (-k) % n for k in range(len(movers))):
            continue
        hits = hk_last_instances(movers, n, pivs)
        if hits:
            return tuple(cycle), tuple(movers), hits[0]
    return None


def template_witnesses(cfg: tuple[int, ...], cycle: tuple[tuple[int, ...], ...], movers: tuple[int, ...]) -> list[int]:
    n = len(cfg)
    out = []
    for j, good in enumerate(cycle):
        p = movers[j]
        if (
            cfg[left(n, p)] == good[left(n, p)]
            and cfg[p] == good[p]
            and cfg[right(n, p)] == good[right(n, p)]
        ):
            out.append(j)
    return out


def template_successors(
    cfg: tuple[int, ...],
    cycle: tuple[tuple[int, ...], ...],
    movers: tuple[int, ...],
    K0: set[tuple[int, ...]],
) -> list[tuple[int, int, tuple[int, ...]]]:
    out = []
    n = len(cfg)
    for j in template_witnesses(cfg, cycle, movers):
        p = movers[j]
        nxt = list(cfg)
        nxt[p] = cycle[next_index(len(cycle), j)][p]
        nxt_t = tuple(nxt)
        if nxt_t in K0:
            out.append((j, p, nxt_t))
    return out


def main() -> None:
    sys = W5System()
    n = sys.n
    cycle = sys.good_cycle
    movers = sys.good_movers
    counts = fire_counts(movers, n)
    pivots = [i for i in range(n) if sys.ms[left(n, i)] == 2 and sys.ms[right(n, i)] == 2]

    print("Wall 2: badKernel_exists probe on the explicit w5 witness")
    print(f"lean source: {DEFS_PATH}")
    print(f"state counts: {sys.ms}")
    print(f"good cycle length: {len(cycle)}")
    print(f"good cycle codes: {sys.good_cycle_codes}")
    print(f"good movers: {movers}")
    print(f"fire counts: {counts}")
    print(f"binary-neighbor pivots: {pivots}")
    print()

    if pivots != [1]:
        print("unexpected pivot set; aborting")
        return

    t = pivots[0]
    c0 = cycle[0]
    i0 = movers[0]
    v1 = choose_alt(c0[i0], sys.ms[i0])
    vt1 = choose_alt(c0[t], sys.ms[t])
    cflip2 = flip_config(flip_config(c0, i0, v1), t, vt1)

    print(f"chosen t: {t}")
    print(f"c0 code/config: {sys.code_of_cfg(c0)} / {c0}")
    print(f"i0 = moverAt(0): {i0}")
    print(f"v1 != c0[i0]: {v1}")
    print(f"vt1 != c0[t]: {vt1}")
    print(f"cFlip2 code/config: {sys.code_of_cfg(cflip2)} / {cflip2}")
    print(f"cFlip2 off-cycle: {cflip2 not in sys.good_set}")
    print()

    K0 = set()
    witness_hist = Counter()
    for cfg in map(tuple, sys.all_configs()):
        ws = witnesses(sys, cfg, movers, cycle)
        if cfg not in sys.good_set and ws:
            K0.add(cfg)
            witness_hist[len(ws)] += 1

    print(f"|K0| = {len(K0)}")
    print(f"witness multiplicity in K0: {dict(sorted(witness_hist.items()))}")
    print(f"cFlip2 in K0: {cflip2 in K0}")
    print(f"cFlip2 witnesses: {witnesses(sys, cflip2, movers, cycle)}")
    print()

    closed = True
    dead = []
    succ_hist = Counter()
    for cfg in sorted(K0):
        succs = kernel_successors(sys, cfg, K0, movers, cycle)
        succ_hist[len(succs)] += 1
        if not succs:
            closed = False
            if len(dead) < 8:
                dead.append((sys.code_of_cfg(cfg), cfg, witnesses(sys, cfg, movers, cycle)))

    print("kernel closure over witness-induced bad successors")
    print(f"  successor multiplicity in K0: {dict(sorted(succ_hist.items()))}")
    print(f"  existentially closed: {closed}")
    if dead:
        print("  sample dead states:")
        for item in dead:
            print(f"    {item}")
    print()

    bad_succs = bad_successors(sys, cflip2)
    kernel_succs = kernel_successors(sys, cflip2, K0, movers, cycle)
    print("cFlip2 successor profile")
    print(f"  all bad successors: {[(p, sys.code_of_cfg(c)) for p, c in bad_succs]}")
    print(f"  kernel successors: {[(j, p, sys.code_of_cfg(c)) for j, p, c in kernel_succs]}")
    print()

    print("deterministic witness-successor trace from cFlip2")
    seen: dict[tuple[int, ...], int] = {}
    chain: list[tuple[int, ...]] = []
    witness_chain: list[tuple[int, int, int]] = []
    cur = cflip2
    while cur not in seen:
        seen[cur] = len(chain)
        chain.append(cur)
        succs = sorted(kernel_successors(sys, cur, K0, movers, cycle), key=lambda x: (x[0], x[1], sys.code_of_cfg(x[2])))
        if not succs:
            break
        j, p, nxt = succs[0]
        witness_chain.append((j, p, sys.code_of_cfg(nxt)))
        cur = nxt

    for idx, cfg in enumerate(chain):
        print(
            f"  step={idx:2d} code={sys.code_of_cfg(cfg):2d} cfg={cfg} "
            f"witnesses={witnesses(sys, cfg, movers, cycle)}"
        )

    if cur in seen:
        start = seen[cur]
        print()
        print(f"cycle detected in witness-successor trace: start={start}, period={len(chain) - start}")
        print(f"cycle codes: {[sys.code_of_cfg(cfg) for cfg in chain[start:]]}")
    else:
        print()
        print("trace terminated at a state with no kernel successor")

    print()
    print("structurally relevant hk_last template probe")
    ms = (2,) * 7
    witness = find_hk_last_witness(ms)
    if witness is None:
        print("  no hk_last witness found in search budget")
        return

    cycle2, movers2, hit = witness
    cycle2_set = set(cycle2)
    t2, k_out = hit
    i0_2 = movers2[0]
    c0_2 = cycle2[0]
    cflip2_2 = list(c0_2)
    cflip2_2[i0_2] = (cflip2_2[i0_2] + 1) % ms[i0_2]
    cflip2_2[t2] = (cflip2_2[t2] + 1) % ms[t2]
    cflip2_2 = tuple(cflip2_2)

    all_cfgs2 = list(itertools.product(*(range(m) for m in ms)))
    K0_2 = {
        cfg
        for cfg in all_cfgs2
        if cfg not in cycle2_set and template_witnesses(cfg, cycle2, movers2)
    }

    succ_hist2 = Counter()
    dead2 = []
    for cfg in sorted(K0_2):
        succs = template_successors(cfg, cycle2, movers2, K0_2)
        succ_hist2[len(succs)] += 1
        if not succs and len(dead2) < 8:
            dead2.append(cfg)

    print(f"  ms={ms}")
    print(f"  good cycle length={len(cycle2)}")
    print(f"  movers={movers2}")
    print(f"  hk_last hit=(t={t2}, k_out={k_out})")
    print(f"  c0={c0_2}")
    print(f"  i0={i0_2}")
    print(f"  cFlip2={cflip2_2}")
    print(f"  cFlip2 off-cycle={cflip2_2 not in cycle2_set}")
    print(f"  cFlip2 in K0={cflip2_2 in K0_2}")
    print(f"  cFlip2 witnesses={template_witnesses(cflip2_2, cycle2, movers2)}")
    print(f"  |K0|={len(K0_2)}")
    print(f"  successor multiplicity in K0={dict(sorted(succ_hist2.items()))}")
    print(f"  existentially closed={not dead2}")
    if dead2:
        print(f"  sample dead states={dead2}")

    seen2: dict[tuple[int, ...], int] = {}
    chain2: list[tuple[int, ...]] = []
    cur2 = cflip2_2
    while cur2 in K0_2 and cur2 not in seen2:
        seen2[cur2] = len(chain2)
        chain2.append(cur2)
        succs = sorted(template_successors(cur2, cycle2, movers2, K0_2), key=lambda x: (x[0], x[1], x[2]))
        if not succs:
            break
        cur2 = succs[0][2]

    print("  witness-successor chain from cFlip2:")
    for idx, cfg in enumerate(chain2[:20]):
        print(f"    step={idx:2d} cfg={cfg} witnesses={template_witnesses(cfg, cycle2, movers2)}")
    if cur2 in seen2:
        start2 = seen2[cur2]
        print(f"  cycle detected: start={start2}, period={len(chain2) - start2}")
        print(f"  cycle states={chain2[start2:]}")
    else:
        print("  chain terminated before repeating")


if __name__ == "__main__":
    main()
