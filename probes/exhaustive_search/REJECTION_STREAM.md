# Rejection-certificate stream — schema and replay

This directory's `driver.py` produces a per-candidate rejection-
certificate stream under `artifacts/rejections/`. That stream is the
Python-side backing of the `≥`-direction of `thm:exact-values` for
$n \in \{3, \ldots, 9\}$.

## Current shipping state (v1.0 tag)

| n | Status | Shipped |
|---|---|---|
| 3 | ships | 0 certificates — no sub-threshold multisets exist |
| 4 | ships | 4,096 certificates for `ms=(2,2,2,2)`, `prod=16`; every one replay-verified |
| 5 | partial ship | Full certificate stream for the all-binary orient `(2,2,2,2,2)`, `prod=32` (32,768 certs, replay-verified) as a worked example. The five mixed-orient reps at `prod ∈ {48, 64, 72, 72, 80}` are regenerable via the C worker (see *Why n=5 is mixed-ship* below) but not pre-generated. |
| 6 | regenerable | full streams regenerable via C worker; not pre-generated |
| 7 | regenerable | full streams regenerable via C worker; not pre-generated |
| 8 | regenerable | full streams regenerable via C worker; not pre-generated |
| 9 | regenerable | full streams regenerable via C worker; not pre-generated |

Run `python3 driver.py --replay artifacts/rejections/` to re-verify
every shipped certificate (see *Replay* below).

The driver is deterministic and the outer loop is
embarrassingly parallel across `(n, multiset, orbit representative)`;
n=5..9 can be split across cores via multiple `driver.py --n N`
processes, or via the C fast-path worker `./exhaustive --n N --orient
M0,...` (see `exhaustive.c` in this directory). The C1 + C2
deterministic coverage manifest ships immediately for all n=3..9 via
`generate_manifest.py` (seconds from a clean clone, matches the
paper's `f684ed53216a0d7f`).

## Why n=5 is mixed-ship

A rejection-certificate stream has one cert per (candidate cycle,
rule-table completion) leaf. For binary-dominated orientations the
completion space is modest (2^k with k ≤ ~15), but for orientations
mixing in ternary, quaternary, or 5-ary processors the completion
count blows up combinatorially — per-orient bundle sizes at n=5
range from ~100 GB to ~1 TB of JSONL. That is not repo-shippable.

Aggregate counts, however, are authoritative and small. For the five
mixed orientations we run the exhaustive C worker in `--summary-only`
mode: the driver still traverses every cycle and every completion and
invokes the independent verifier on each, but per-cert JSON emission
is skipped, leaving only the final summary line with rejection counts.
Any referee who wants the full per-cert stream for a given orient can
regenerate it locally with the C driver (order of minutes to hours
per orient on a single core). The counts are deterministic and any
regeneration that disagrees with what `summary.json` reports would be
a finding.

## Directory layout

```
artifacts/rejections/
  summary.json                     # top-level index, per-n stats
  n3/                              # empty (no sub-threshold multisets)
  n4/
    index.json                     # n-level index, per-multiset stats
    ms-16-2-2-2-2.jsonl            # one rejection certificate per line
  n5/
    index.json                     # per-orient stats incl. counts
    ms-32-2-2-2-2-2.jsonl          # full stream (all-binary, 32,768 certs)
    # other 5 orients: counts only, in index.json and summary.json.
    # Regenerate full streams with the C worker.
  ...
  n9/
    index.json
    ms-{product}-{sorted-ms}.jsonl
```

Each `.jsonl` file has one rejection certificate per line. Lines are
emitted in the deterministic order of the driver's DFS over
(orientation, candidate good cycle, rule-table completion); running
the driver twice produces bit-for-bit identical files.

## Certificate schema (v1)

```json
{
  "schema_version": 1,
  "n": 5,
  "ms_sorted": [2, 2, 2, 3, 3],
  "orientation": [2, 2, 2, 3, 3],
  "product": 72,
  "cycle":  [[0,0,0,0,0], [1,0,0,0,0], ..., [0,0,0,0,0]],
  "movers": [0, 1, 2, 3, 4, 0, ...],
  "det_forced":  { "<p>,<L>,<S>,<R>": <out>, ... },
  "completion":  { "<p>,<L>,<S>,<R>": <out>, ... },
  "property_failed": "convergence",
  "detail": { "info": "43 bad configs reachable in a bad cycle" }
}
```

Fields:

* `n`, `ms_sorted`, `orientation`, `product` — which orbit representative.
* `cycle` — the candidate good cycle as a list of configurations (the
  lex-min rotation is the canonical form the driver enumerates).
* `movers` — the processor fired at each step; length == `len(cycle)`.
* `det_forced` — the partial rule-table entries that the cycle itself
  *forced* via the Dijkstra convention (mover output + silent neighbours)
  plus any entries filled by the forced-neighbor pruning rule
  (App C.2 proof-critical rule #1). Keys encode `(processor, left,
  self, right)` as a comma-separated string.
* `completion` — the additional rule-table entries the enumeration
  picked to fill every free slot and produce a total rule table. Union
  with `det_forced` gives the total rule table that was handed to
  the verifier.
* `property_failed` — the first of the six validity properties
  (§2.3) that `verify_system` rejected: one of `liveness`,
  `mutual_exclusion`, `mutual_exclusion_closure`, `closure`,
  `convergence`, `fairness`, `fairness_or_convergence`,
  `connectedness`. (The exact set reported depends on the verifier's
  return-label granularity.)
* `detail` — human-readable context from the verifier for that
  failure; not load-bearing, but useful for triage.

## Replay

A referee verifies the stream by running

```bash
python3 driver.py --replay artifacts/rejections/
```

which, for every certificate, reconstructs the total rule table
(`det_forced` ∪ `completion`), re-invokes `verify_system` on the
reconstructed `(ms, fs)`, and checks that the system is indeed
invalid. Any certificate whose replay says "valid" is flagged as a
**sub-threshold witness** — that would contradict the paper's
`thm:exact-values` for that row. The replay exits with a non-zero
status in that case.

Replay is ~milliseconds per certificate; a full audit of the shipped
bundle runs in under a minute on a single core.

## What the certificates *do not* show

A rejection certificate says: *this specific (cycle, completion) pair
is not a valid system.* It does not directly say: *no valid system
exists with this multiset at this product.* The latter is the
conjunction over every cycle and every completion the driver
enumerates. Coverage of the enumeration is discharged by:

1. C1 + C2 rehash (deterministic, verified by `generate_manifest.py`).
2. C3 cycle enumeration completeness (this driver's DFS with
   forced-neighbor propagation + `lex-min start` canonicalization).
3. C4 completion enumeration (branch-exhaust on free entries).
4. C5 verifier pass per completion.

Items 1–4 are all deterministic and replayable. The paper's §App C
argues that every valid system on the multiset, if it existed, would
be enumerated by this pipeline. Any breakdown in that argument would
show up as a cert-with-valid-replay in (1) above.

## Pruning rules (proof-critical vs. optimisation)

The two **proof-critical** pruning rules used during cycle
enumeration are:

* **Forced-neighbor consistency** (App C.2 rule #1) — each step's
  non-movers are silent; the corresponding rule-table entries are
  filled in on-the-fly. A conflict kills the branch.
* **Processor-orientation orbit reduction** (App C.2 rule #2 / #3) —
  one representative per dihedral orbit at C2, and lex-min starting
  config at C3 as the state-label renaming canonicalization.

The **optimisation-only** rule —

* **Quasi-unidirectionality** (no four cyclically consecutive binary
  processors, `lem:quasi-uni`) —

is recorded in each certificate via the `quasi_uni_optimization_class`
field in the per-orientation index summary, but the driver still
processes those candidates and emits their rejection certificates
normally. The final rejection is by the independent verifier, so the
lower-bound certificate does not depend on trusting
`lem:quasi-uni` as a lemma.
