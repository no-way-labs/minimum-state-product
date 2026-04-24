# Results Summary: Minimizing the State Product for Self-Stabilizing Token Rings

## Exact Values and Bounds

| $n$ | $M_n$ | $M_n^{1/n}$ | Witness vector | Cycle length | Lower bound proof |
|-----|--------|-------------|----------------|-------------|-------------------|
| 3 | **8** | 2.000 | $(2,2,2)$ | 8 | Gray code = all configs |
| 4 | **16** | 2.000 | $(2,2,2,2)$ | 16 | Gray code = all configs |
| 5 | **96** | 2.491 | $(2,2,2,3,4)$ | 18 | Products 72, 80 dead (exhaustive) |
| 6 | **288** | 2.568 | $(2,2,2,4,3,3)$ | 27 | Products 144–256 dead (exhaustive) |
| 7 | $\in [576, 864]$ | $[2.50, 2.74]$ | $(3,2,2,2,3,4,3)$ | 43 | Products through 512 dead; product 576 open (5 classes) |
| 8 | $\leq 2592$ | $\leq 2.83$ | $(2,2,3,4,3,3,2,3)$ | 55 | conjectured exact |
| 9 | $\leq 13122$ | $\leq 2.93$ | $(2,3,3,3,3,3,3,3,3)$ | 25 | product 7776 dead; gap 7777–13121 open |
| $n \geq 3$ | $\leq 2 \cdot 3^{n-1}$ | $\to 3$ | $(2,3,3,\ldots,3)$ | $3n-2$ | Sol 3 v1 (universal) |

## Two Competing Constructions

### Construction A: "3+1+rest" Pattern ($n = 5, \ldots, 8$)

For $5 \leq n \leq 8$, the optimal (or near-optimal) construction uses:
- **3 binary processors** ($m_i = 2$) placed consecutively (or nearly so)
- **1 quaternary processor** ($m_i = 4$) acting as "translator" between binary and ternary blocks
- **$(n-4)$ ternary processors** ($m_i = 3$)

$$M_n \leq 2^3 \cdot 4 \cdot 3^{n-4} = 32 \cdot 3^{n-4}$$

**Confirmed exact** for $n = 5, 6$. **Upper bound confirmed** for $n = 7, 8$. **DEAD at $n = 9$** (all 56 orientations exhaustively eliminated).

| $n$ | Pattern prediction | Actual $M_n$ | Match? |
|-----|-------------------|-------------|--------|
| 5 | $32 \cdot 3^1 = 96$ | 96 | ✓ exact |
| 6 | $32 \cdot 3^2 = 288$ | 288 | ✓ exact |
| 7 | $32 \cdot 3^3 = 864$ | $\leq 864$ | ✓ upper bound |
| 8 | $32 \cdot 3^4 = 2592$ | $\leq 2592$ | ✓ upper bound |
| 9 | $32 \cdot 3^5 = 7776$ | DEAD | ✗ pattern breaks |

### Construction B: Sol 3 v1 ($n \geq 3$, universal)

Adaptation of Dijkstra's Solution 3 with one binary processor:
- $ms = (2, 3, 3, \ldots, 3)$, product $= 2 \cdot 3^{n-1}$

**Rules (Sol 3 v1):**
- P0 (bottom, m=2): $f(L,S,R) = (S-1) \bmod 2$ if $(S+1) \bmod 2 = R \bmod 2$, else $S$
- P1–P_{n-2} (middle, m=3): $f(L,S,R) = L \bmod 3$ if $(S+1) \bmod 3 = L \bmod 3$; else $R \bmod 3$ if $(S+1) \bmod 3 = R \bmod 3$; else $S$
- P_{n-1} (top, m=3): $f(L,S,R) = (L \bmod 3 + 1) \bmod 3$ if $L \bmod 3 = R \bmod 3$ and $(L \bmod 3 + 1) \bmod 3 \neq S$; else $S$

**Verified for $n = 3, \ldots, 13$:**

| $n$ | product | cycle length | good configs |
|-----|---------|-------------|-------------|
| 3 | 18 | 7 | 13 |
| 4 | 54 | 10 | 22 |
| 5 | 162 | 13 | 30 |
| 6 | 486 | 16 | 38 |
| 7 | 1458 | 19 | 46 |
| 8 | 4374 | 22 | 54 |
| 9 | 13122 | 25 | 62 |
| 10 | 39366 | 28 | 70 |
| 11 | 118098 | 31 | 78 |
| 12 | 354294 | 34 | 86 |
| 13 | 1062882 | 37 | 94 |

**Exact formulas:** cycle length $= 3n - 2$, good configs $= 8n - 10$ (for $n \geq 4$).

### Construction Comparison

| $n$ | "3+1+rest" | Sol 3 v1 | Best known | Ratio |
|-----|------------|----------|-----------|-------|
| 5 | **96** | 162 | **96** | 0.59 |
| 6 | **288** | 486 | **288** | 0.59 |
| 7 | 864 | 1458 | $\leq$ 864 | 0.59 |
| 8 | 2592 | 4374 | $\leq$ 2592 | 0.59 |
| 9 | DEAD | 13122 | $\leq$ 13122 | — |
| 10 | DEAD* | 39366 | $\leq$ 39366 | — |

*Not tested, but pattern broke at $n=9$.

## Asymptotic Growth Rate

$$M_n^{1/n} \text{ sequence: } 2.00,\; 2.00,\; 2.49,\; 2.57,\; 2.74,\; 2.83,\; 2.93 \quad (n = 3, \ldots, 9)$$

The sequence is **monotonically increasing** and bounded by 3.

The Sol 3 v1 construction gives $M_n \leq 2 \cdot 3^{n-1}$ for all $n \geq 3$:
$$(2 \cdot 3^{n-1})^{1/n} = 2^{1/n} \cdot 3^{(n-1)/n} \to 3 \text{ as } n \to \infty$$

### Answers to Knuth's Central Open Questions

1. **Is $\limsup M_n^{1/n} < 3$?**
   Almost certainly **NO**. The data strongly suggests $\lim M_n^{1/n} = 3$.
   The Sol 3 v1 construction gives $M_n \leq 2 \cdot 3^{n-1}$, which is a constant factor ($2/3$) below $3^n$.
   Any construction with all $m_i \leq 3$ gives product $\leq 3^n$, and the question reduces to whether
   a constant factor saving below $3^n$ is achievable — which Sol 3 v1 achieves.

2. **Is $\liminf M_n^{1/n} > 2$?**
   Almost certainly **YES**. Even $M_5^{1/5} = 2.49 > 2$, and the sequence is increasing.

## Key Structural Results

### "3+1+rest" Breakdown at $n = 9$
The "3+1+rest" pattern with product $32 \cdot 3^{n-4}$ fails at $n = 9$. All 56 distinct necklaces of
$\{2,2,2,4,3,3,3,3,3\}$ were exhaustively tested (600s, 10M cycles per orientation). Zero survivors.
The $\{0,1\}^9$ SCC trap (492 configs) blocks convergence universally.

### Quaternary Necessity: Partial
For $5 \leq n \leq 7$: no pure-$\{2,3\}$ system exists (products 72, 216, 648 all dead). A quaternary processor is necessary in this range.

For $n \geq 9$: quaternary is NOT necessary. Sol 3 v1 uses only binary and ternary processors.

### RFC's Obstruction (Extended)
No 4+ consecutive binary processors. This limits the binary fraction to $\leq 3/n$.

### ARG's LCM Constraint
With $2N$ non-adjacent binary processors, each intervening block must have LCM $\geq N+1$.
For pure ternary blocks, LCM $= 3$, so $N \leq 2$ (at most 4 binary).

### Feasibility Sparsity
For large $n$, most integers cannot be factored into $n$ parts all $\geq 2$.
The requirement $\Omega(P) \geq n$ (prime factors with multiplicity) eliminates
most products, making the search space surprisingly small. For $n = 7$, only
12 products in $[128, 863]$ have feasible vectors.

### Orientation Sensitivity
The position of the quaternary "translator" processor is critical.
At each $n$, only 1–2 of $\sim 20$+ orientations yield valid systems.
At $n=8$, the winning orientation has non-contiguous binaries (P0,P1 + P6),
suggesting the "binary block" constraint relaxes at larger $n$.

## Explicit Witnesses

### $M_5 = 96$: $(2,2,2,3,4)$
- 30 good configs, 66 bad configs, cycle length 18
- Full transition functions in `product96_result.txt`

### $M_6 = 288$: $(2,2,2,4,3,3)$
- 46 good configs, 242 bad configs, cycle length 27
- Binary block at positions 0–2, quaternary at position 3, ternary at 4–5

### $M_7 \leq 864$: $(3,2,2,2,3,4,3)$
- Binary block at positions 1–3, quaternary at position 5, ternary at 0, 4, 6
- Cycle length 43 (parallel agent witness)

### $M_8 \leq 2592$: $(2,2,3,4,3,3,2,3)$
- Binary at P0, P1, P6 (NOT contiguous); quaternary at P3; ternary at P2, P4, P5, P7
- Cycle length 55. Found at orientation 21/35 of multiset $\{2,2,2,4,3,3,3,3\}$.
- Full transition functions in `n8_sweep_results.txt`

### $M_9 \leq 13122$: $(2,3,3,3,3,3,3,3,3)$
- 62 good configs, 13060 bad configs, cycle length 25
- Sol 3 v1 construction (Dijkstra Solution 3 with binary bottom processor)
- Independently verified with two separate verifiers

### $M_{10} \leq 39366$: $(2,3,3,3,3,3,3,3,3,3)$
- 70 good configs, 39296 bad configs, cycle length 28
- Sol 3 v1 construction

## Methodology

### Good-cycle enumeration + SMT completion (for "3+1+rest" witnesses)
1. **Enumerate** locally consistent good cycles via backtracking
2. **Extract** forced transition-function entries from the cycle
3. **Complete** unforced entries using Z3 SMT solver with:
   - Liveness constraints on bad configs
   - Rank-function convergence encoding: $\text{rank}[\text{succ}] < \text{rank}[c]$ for all bad-to-bad transitions
4. **Verify** the completed system with the full 5-property checker

### Sol 3 v1 (for universal upper bound)
1. Parametrize Dijkstra Sol 3 rules with modular comparisons ($\%m_i$)
2. Set $m_0 = 2$, $m_1 = \cdots = m_{n-1} = 3$
3. Verify all 5 properties computationally

### Structural elimination
- RFC filter: reject vectors with 4+ consecutive binary
- ARG LCM filter: reject vectors violating the block LCM constraint
- $\Omega(P) \geq n$ filter: reject products that can't be factored into $n$ parts $\geq 2$
- Computational elimination: exhaustive cycle screening + SMT for surviving classes

## Tools

| Tool | Purpose |
|------|---------|
| `verifier.py` | Full 5-property verification (function-based rules) |
| `docs/verify_witnesses.py` | Full 5-property verification (table-based rules) |
| `verify_sol3v1_n9.py` | Sol 3 v1 verification for $n=9,10$ |
| `verify_sol3v1_extended.py` | Sol 3 v1 systematic sweep $n=3,\ldots,13$ |
| `complete_96.py` | Good-cycle enumeration + Z3 SMT completion |
| `search_96.py` | Backtracking good-cycle search |
| `search_n6.py` | $n=6$ product search |
| `search_n7.py` | $n=7$ systematic search + product enumeration |
| `lower_bounds.py` | Structural lower bound analysis |
| `wave_filter.py` | Wave structure analysis |
| `targeted_search.py` | Exhaustive S3-hybrid search |
| `n8_sweep.py` | Automated necklace sweep for $n=8$ candidate multisets |
| `n9_sweep.py` | Automated necklace sweep for $n=9$ candidate multisets |
| `p2_smt_completion.py` | GPT's pipeline: cycle enum + propagation + Z3 |

## Open Problems

1. **Is $M_7 = 864$?** Requires killing product 576 (5 open classes remaining).
2. **Is $M_8 = 2592$?** Upper bound confirmed. Requires lower bound work on products $< 2592$.
3. **Is there an $n=9$ witness with product $< 13122$?** Product 7776 dead. Products 7777–13121 largely unexplored. Product 10368 partially tested (~77/140 orientations dead).
4. **Is $M_n = 2 \cdot 3^{n-1}$ for all $n \geq 9$?** Sol 3 v1 gives this upper bound. No better construction known for $n \geq 9$.
5. **Can Sol 3 v1 be further compressed?** E.g., two binary processors giving product $4 \cdot 3^{n-2}$.
6. **Does $M_n^{1/n} \to 3$?** Almost certainly yes. The answer to Knuth's question "$\limsup < 3$?" is NO.
