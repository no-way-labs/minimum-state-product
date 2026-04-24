# N5 Residual Census Audit

Date: 2026-04-14

This note records the current computational status of the `n = 5` residual
census work inside `LeanMn/SmallN`.

It is meant to answer one narrow question:

> Why does the current exact generator produce counts around `2027`, while the
> older project docs repeatedly cite a residual `164`?

## Bottom line

At the moment, the safest conclusion is:

- the new `gen_smalln_lower_bound.py` is computing an exact and explicitly
  specified search object,
- the historical `164` is now best explained by a bounded legacy DFS regime,
  not by the exact search object used in the new generator.

So `164` should not currently be treated as the source of truth for Lean data
emission.

## Exact current generator counts

The current generator enumerates **canonical-start, full-support** cycles and
then applies the normalization pipeline described in
`M56_CLOSURE_PLAN_2026-04-14.md`.

### Profile `(2,2,2,3,3)`

Current exact output:

```text
raw=40320
relabel=2098
recanon=2027
determined=2098
types_unique={baf: 649, sweep: 172, wiggle: 1206}
```

More explicitly:

- raw canonical-start full-support cycles: `40,320`
- after first-seen relabeling: `2,098`
- after post-relabel cycle rotation/reversal recanonicalization: `2,027`
- determined-table key count: `2,098`

The `2027` figure matches the empirical probe already quoted in the closure
plan.

Under the document's topological cycle-type classification (`sweep` = `|W| ≥ 2`,
`baf` = `W = 0` with one reversal, `wiggle` = `W = 0` with at least two
reversals, `odd_winding` = `|W| = 1`), the current exact object classifies all
`2,027` post-relabel recanonicalized classes here as `sweep`.

### Profile `(2,2,3,2,3)`

Current exact output:

```text
raw=6912
relabel=312
recanon=292
determined=312
types_unique={sweep: 172, wiggle: 120}
```

So this profile is much smaller than `(2,2,2,3,3)`, but it is not empty and it
is not obviously covered by the historical `164`.

Under the same topological classifier, all `292` exact post-relabel
recanonicalized classes here are also `sweep`.

## What the historical scripts actually do

Two scripts are repeatedly cited in the project notes:

- `probes/cic_completion_failure2.py`
- `probes/cic_completion_failure3.py`

But both use **bounded** DFS search, not an exact exhaustive enumerator.

### `cic_completion_failure2.py`

Its enumerator is:

- `enumerate_good_cycles(ms, n, max_cycles=200, max_time=60.0)`
- per-start DFS cap: `nodes < 500000`
- hard return once `len(cycles) >= max_cycles`

The script body then actually calls:

- `enumerate_good_cycles(ms, n, max_cycles=100, max_time=120.0)`

So the script itself is capped at `100` cycles before later filtering.

### `cic_completion_failure3.py`

Its extended enumerator is:

- `enumerate_cycles_long(ms, n, max_cycles=200, max_time=120.0, max_path_len)`
- per-start DFS cap: `nodes < 1000000`
- hard return once `len(cycles) >= max_cycles`

The script body then calls:

- `enumerate_cycles_long(ms, n, max_cycles=200, max_time=180.0, max_path_len=40)`

And its own header says:

> "At n=5, ALL 82 full-processor cycles have bad SCCs ..."

So the legacy CIC scripts themselves do not consistently support the later
`164` wording.

## Strongest provenance evidence so far

The key experiment is to replay the **legacy DFS regime** without changing the
search logic, and just vary the `max_cycles` cap.

For `ms = (2,2,2,3,3)`:

```text
max_cycles=100  -> 100 total cycles,  82 full-processor cycles
max_cycles=150  -> 150 total cycles, 122 full-processor cycles
max_cycles=164  -> 164 total cycles, 135 full-processor cycles
max_cycles=200  -> 200 total cycles, 164 full-processor cycles
max_cycles=300  -> 300 total cycles, 262 full-processor cycles
```

This is the first genuinely convincing explanation of the historical `164`:

- the old DFS enumerator was bounded by `max_cycles = 200`,
- among those first `200` cycles, exactly `164` happen to visit all
  processors,
- later notes appear to have promoted that bounded-search count into a claimed
  exhaustive residual census.

This is now reproducible directly from the current SmallN generator via the
legacy replay mode:

```text
python3 .../gen_smalln_lower_bound.py \
  --profile 2,2,2,3,3 \
  --enumerator legacy \
  --legacy-max-cycles 200 \
  --legacy-post-filter-full-support

raw=164
```

Likewise:

```text
... --legacy-max-cycles 100 --legacy-post-filter-full-support

raw=82
```

So the historical `82` and `164` are now both explained by the same bounded DFS
pipeline.

There is parallel evidence on the `n = 6` side as well: replaying the same
legacy DFS shape on `ms = (2,2,2,3,3,3)` gives exactly `30` full-processor
cycles when the total cycle cap is `32`. So the historical `164/30` pair now
looks much more like a family of bounded-search artifacts than a pair of exact
residual censuses.

This too is now reproducible directly from the current SmallN generator:

```text
python3 .../gen_smalln_lower_bound.py \
  --profile 2,2,2,3,3,3 \
  --enumerator legacy \
  --legacy-max-cycles 32 \
  --legacy-post-filter-full-support

raw=30
```

This matches the header discrepancy in the old scripts:

- one script explicitly talks about `82` full-processor cycles,
- later docs talk about `164`,
- both are naturally explained by the same bounded DFS with different caps.

## The strongest current explanation

The mismatch is most plausibly one of these:

### Possibility A: `164` is a different residual object

This would mean the historical `164` is not counting the same thing as the new
generator.

Likely candidates:

- only non-sweep residuals after analytical sweep elimination,
- only a stricter normalized candidate object,
- only a legacy cycle-type quotient not yet reproduced in
  `gen_smalln_lower_bound.py`.

### Possibility B: `164` came from bounded search and later got promoted

This is now the leading explanation.

For `n = 5`, the bounded DFS regime reproduces the `164` exactly when one takes
the first `200` cycles and then filters to full-processor cycles.

So unless contrary evidence appears, the historical `164` should be treated as
an artifact of a capped legacy search, not as an exact exhaustive residual
census.

## What this means for the SmallN plan

The practical consequence is simple:

- do **not** emit Lean tail data from the historical `164` number yet,
- do **not** assume that `164` is just "one more missing symmetry" on top of
  the current exact generator,
- do **not** keep spending time searching for a symmetry quotient whose only
  job is to force `2027` down to `164`.

The next trustworthy route is:

1. define the exact residual object in words,
2. make the generator compute exactly that object,
3. only then freeze the resulting candidate list for Lean.

## Recommended next computational step

The best next step is to make the residual object explicit at the generator
level.

Concretely:

1. add an exact cycle-type classifier that matches the project's analytical
   split well enough to separate:
   - sweep
   - fc=2 back-and-forth
   - wiggle / higher-complexity residuals
2. decide whether the Lean tail proof should target:
   - the new exact census, or
   - a newly defined smaller residual object with an explicit completeness
     theorem
3. retire `164` unless a precise exact definition reproduces it independently
   of the legacy DFS caps.

Until that is done, the computational `n = 5` story is strong enough to guide
research, but not yet clean enough to freeze into Lean proof data.
