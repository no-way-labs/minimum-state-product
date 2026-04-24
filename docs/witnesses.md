---
title: "Witnesses for Minimizing the State Product of Self-Stabilizing Token Rings"
author: "K Alexander A-M"
date: "March 2026"
geometry: margin=1in
fontsize: 11pt
---

# Summary

We exhibit self-stabilizing token ring systems achieving the following state products:

| n | Product | State counts | Good cycle length |
|---|---------|--------------|-------------------|
| 5 | 96 = 2^3 * 3 * 4 | (2,2,2,3,4) | 18 |
| 6 | 288 = 2^3 * 3^2 * 4 | (2,2,2,4,3,3) | 35 |
| 7 | 864 = 2^3 * 3^3 * 4 | (3,2,2,2,3,4,3) | 52 |
| 8 | 2592 = 2^3 * 3^4 * 4 | (2,2,3,4,3,3,2,3) | 55 |

M_5 = 96 and M_6 = 288 are exact (all smaller products eliminated by exhaustive search).
M_7 <= 864 and M_8 <= 2592 are upper bounds.

Conjecture: M_n = 32 * 3^(n-4) for all n >= 5.

# Verification

The accompanying script `verify_witnesses.py` (Python 3.8+, no dependencies) checks all five Dijkstra properties for each witness:

```
$ python3 verify_witnesses.py
n=5, M_5=96, state_counts=(2, 2, 2, 3, 4):
  PASS  product=96  good_cycle_length=18  total_configs=96  bad_configs=78
n=6, M_6=288, state_counts=(2, 2, 2, 4, 3, 3):
  PASS  product=288  good_cycle_length=35  total_configs=288  bad_configs=253
n=7, M_7<=864, state_counts=(3, 2, 2, 2, 3, 4, 3):
  PASS  product=864  good_cycle_length=52  total_configs=864  bad_configs=812
n=8, M_8<=2592, state_counts=(2, 2, 3, 4, 3, 3, 2, 3):
  PASS  product=2592  good_cycle_length=55  total_configs=2592  bad_configs=2537
All witnesses verified.
```

# Transition Functions

Each processor P_i has state set {0, ..., m_i - 1}. The transition function
f_i(L, S, R) maps (left neighbor state, own state, right neighbor state) to a
new state. Processor P_i is privileged when f_i(L, S, R) != S.

## n = 5: state counts (2, 2, 2, 3, 4), product 96

**P0** (2-state, neighbors: m_4=4, m_1=2):

|  L  |  S  |  R  | f |
|-----|-----|-----|---|
|  0  |  0  |  0  | 1 |
|  0  |  0  |  1  | 1 |
|  0  |  1  |  0  | 1 |
|  0  |  1  |  1  | 1 |
|  1  |  0  |  0  | 0 |
|  1  |  0  |  1  | 0 |
|  1  |  1  |  0  | 0 |
|  1  |  1  |  1  | 0 |
|  2  |  0  |  0  | 0 |
|  2  |  0  |  1  | 0 |
|  2  |  1  |  0  | 0 |
|  2  |  1  |  1  | 0 |
|  3  |  0  |  0  | 0 |
|  3  |  0  |  1  | 0 |
|  3  |  1  |  0  | 0 |
|  3  |  1  |  1  | 0 |

**P1** (2-state, neighbors: m_0=2, m_2=2): f_1(L,S,R) = L

|  L  |  S  |  R  | f |
|-----|-----|-----|---|
|  0  |  0  |  0  | 0 |
|  0  |  0  |  1  | 0 |
|  0  |  1  |  0  | 0 |
|  0  |  1  |  1  | 0 |
|  1  |  0  |  0  | 1 |
|  1  |  0  |  1  | 0 |
|  1  |  1  |  0  | 1 |
|  1  |  1  |  1  | 1 |

**P2** (2-state, neighbors: m_1=2, m_3=3):

|  L  |  S  |  R  | f |
|-----|-----|-----|---|
|  0  |  0  |  0  | 0 |
|  0  |  0  |  1  | 0 |
|  0  |  0  |  2  | 1 |
|  0  |  1  |  0  | 1 |
|  0  |  1  |  1  | 0 |
|  0  |  1  |  2  | 1 |
|  1  |  0  |  0  | 1 |
|  1  |  0  |  1  | 0 |
|  1  |  0  |  2  | 0 |
|  1  |  1  |  0  | 1 |
|  1  |  1  |  1  | 0 |
|  1  |  1  |  2  | 0 |

**P3** (3-state, neighbors: m_2=2, m_4=4):

|  L  |  S  |  R  | f |    |  L  |  S  |  R  | f |
|-----|-----|-----|---|----|-----|-----|-----|---|
|  0  |  0  |  0  | 0 |    |  1  |  0  |  0  | 1 |
|  0  |  0  |  1  | 1 |    |  1  |  0  |  1  | 0 |
|  0  |  0  |  2  | 1 |    |  1  |  0  |  2  | 2 |
|  0  |  0  |  3  | 0 |    |  1  |  0  |  3  | 0 |
|  0  |  1  |  0  | 2 |    |  1  |  1  |  0  | 1 |
|  0  |  1  |  1  | 2 |    |  1  |  1  |  1  | 0 |
|  0  |  1  |  2  | 2 |    |  1  |  1  |  2  | 0 |
|  0  |  1  |  3  | 0 |    |  1  |  1  |  3  | 1 |
|  0  |  2  |  0  | 2 |    |  1  |  2  |  0  | 2 |
|  0  |  2  |  1  | 2 |    |  1  |  2  |  1  | 0 |
|  0  |  2  |  2  | 2 |    |  1  |  2  |  2  | 2 |
|  0  |  2  |  3  | 0 |    |  1  |  2  |  3  | 1 |

**P4** (4-state, neighbors: m_3=3, m_0=2):

|  L  |  S  |  R  | f |    |  L  |  S  |  R  | f |    |  L  |  S  |  R  | f |
|-----|-----|-----|---|----|-----|-----|-----|---|----|-----|-----|-----|---|
|  0  |  0  |  0  | 0 |    |  1  |  0  |  0  | 0 |    |  2  |  0  |  0  | 1 |
|  0  |  0  |  1  | 0 |    |  1  |  0  |  1  | 0 |    |  2  |  0  |  1  | 1 |
|  0  |  1  |  0  | 2 |    |  1  |  1  |  0  | 0 |    |  2  |  1  |  0  | 1 |
|  0  |  1  |  1  | 2 |    |  1  |  1  |  1  | 0 |    |  2  |  1  |  1  | 1 |
|  0  |  2  |  0  | 2 |    |  1  |  2  |  0  | 0 |    |  2  |  2  |  0  | 3 |
|  0  |  2  |  1  | 2 |    |  1  |  2  |  1  | 0 |    |  2  |  2  |  1  | 2 |
|  0  |  3  |  0  | 0 |    |  1  |  3  |  0  | 3 |    |  2  |  3  |  0  | 3 |
|  0  |  3  |  1  | 0 |    |  1  |  3  |  1  | 0 |    |  2  |  3  |  1  | 0 |

## n = 6: state counts (2, 2, 2, 4, 3, 3), product 288

Transition tables are encoded in `verify_witnesses.py` (function `witness_n6`).
The system has the same 3-binary-plus-quaternary architecture as n = 5.

## n = 7: state counts (3, 2, 2, 2, 3, 4, 3), product 864

Transition tables are encoded in `verify_witnesses.py` (function `witness_n7`).

## n = 8: state counts (2, 2, 3, 4, 3, 3, 2, 3), product 2592

Transition tables are encoded in `verify_witnesses.py` (function `witness_n8`).

# Architecture

All four witnesses share the same structure: 3 binary processors in a
consecutive block, 1 quaternary processor separated from the block by a
ternary buffer, and ternary fill for the remaining positions. The product
is always 2^3 * 4 * 3^(n-4) = 32 * 3^(n-4).
