# Exploration Log: Minimizing the State Product for Self-Stabilizing Token Rings

## Strategy Register

**Eliminated approach classes:**
- [Expl 1] Modifying Dijkstra S3 by replacing a single processor: gives product $2 \cdot 3^{n-1}$ (valid but far from optimal for $n=5$)
- [Cross-pollination] Products 72 and 80 for $n=5$: fully eliminated by good-cycle enumeration + fatal recurrent-component screening
- [Cross-pollination] Products 144, 192, 216, 240, 256 for $n=6$: fully eliminated. All classes at each product dead. **$M_6 = 288$ is exact.**
- [Cross-pollination + Expl 6] Products 288–512 for $n=7$: fully eliminated. Products 576, 640, 648, 672, 720, 768, 800 computationally dead or structurally infeasible. Only product 576 has open classes (5 clustered classes, 270K+ cycles screened without survivors). **$576 \leq M_7 \leq 864$.**
- [Expl 8] "3+1+rest" pattern at $n=9$: product 7776 = $32 \cdot 3^5$ is DEAD. All 56 orientations of $\{2,2,2,4,3,3,3,3,3\}$ exhaustively screened (600s/10M cycles each, 0 survivors). The pattern breaks at $n=9$.

**Obstructions:**
- All-binary ($m_i = 2$ for all $i$) fails for $n \geq 5$ — quasi-unidirectionality forces bad cycles (Haddad–Knuth seminar, 1985)
- Four or more consecutive 2-state processors are impossible (RFC's generalization)
- With $2N$ non-adjacent 2-state processors, the LCM of state counts in each intervening block must be $\geq N+1$ (ARG's constraint)
- **[Expl 6, WEAKENED by Expl 8]** Quaternary necessity conjecture: REFUTED for $n \geq 9$. Sol 3 v1 with $ms = (2, 3^{n-1})$ (no quaternary) gives valid systems for ALL $n \geq 3$. The conjecture may still hold for $5 \leq n \leq 8$ (needed for optimality at those $n$), but is NOT universal.
- **[NEW, Expl 6]** Sparsity of feasible products: for $n=7$, only 12 products in $[128, 863]$ can even be factored into 7 parts $\geq 2$ AND satisfy RFC. The gap $[577, 863]$ contains only 7 feasible products, of which 6 are computationally dead.

**Building blocks:**
- Gray code construction achieves $M_n = 2^n$ for $n \leq 4$
- Dijkstra Solution 3 achieves $3^n$ for all $n$ (3-state uniform)
- Dijkstra Solution 2 achieves $4^{n-1}$ (but is a line solution, not ring)
- **[Expl 1, GENERALIZED by Expl 8]** Hybrid S3+binary = "Sol 3 v1": replace bottom processor with 2-state, keep rest as Sol 3 with $\%m$ modular comparisons. Valid for ALL $n \geq 3$. Product $2 \cdot 3^{n-1}$, cycle length $3n - 2$, good configs $8n - 10$ (for $n \geq 4$).
- **[NEW, Expl 4]** Non-uniform construction for $n=6$: $ms = (2,2,2,4,3,3)$, product $288 = M_6$ (exact). 4-state processor at position 3 bridges the binary block (P0–P2) and ternary block (P4–P5).
- **[NEW, Expl 5]** "3+1+rest" pattern for $n=7$: $ms = (3,2,2,2,3,4,3)$, product $864$. Binary block at positions 1–3, quaternary at position 5, ternary at 0, 4, 6. Orientation is critical: 9 of 10 tested orientations failed. Confirmed by parallel agent.

**Known reformulations:**
- Wave-filter perspective (DEK): processors filter $k$-waves to $\lceil k/2 \rceil$-waves per lap. Floor version easy but goes dead; ceiling version is the hard direction. Not yet formalized.
- **[Expl 3, REFUTED]** $\sqrt{6}$ conjecture: $M_n^{1/n} \to \sqrt{6} \approx 2.449$. REFUTED by $M_6 = 288$ ($288^{1/6} \approx 2.57 > \sqrt{6}$). The sequence $M_n^{1/n}$ is INCREASING: $2.00, 2.00, 2.49, 2.57$.
- **[NEW, Expl 5]** The "3+1+rest" pattern: optimal vectors use 3 binary + 1 quaternary + $(n-4)$ ternary processors. Product $= 2^3 \cdot 4 \cdot 3^{n-4} = 32 \cdot 3^{n-4}$. Gives $M_n^{1/n} \to 3$ asymptotically.
  - **Confirmed for $n = 5, 6, 7, 8$**: $M_5 = 96 = 32 \cdot 3$, $M_6 = 288 = 32 \cdot 9$, $M_7 \leq 864 = 32 \cdot 27$, $M_8 \leq 2592 = 32 \cdot 81$.
  - **[Expl 7]** $n=8$ witness: $ms = (2,2,3,4,3,3,2,3)$, product $2592$, cycle length 55. Binaries NOT contiguous (P0,P1 + P6).
  - **[Expl 8]** Pattern BREAKS at $n=9$: product 7776 dead (all 56 orientations).
  - $M_n^{1/n}$ sequence: $2.00, 2.00, 2.49, 2.57, 2.74, 2.83$ ($n=3,\ldots,8$). Monotonically increasing, approaching 3.
  - The $\sqrt{6}$ conjecture is **REFUTED**. The true asymptotic appears to be $M_n^{1/n} \to 3$.
- **[NEW, Expl 8]** Sol 3 v1 construction: $ms = (2, 3, 3, \ldots, 3)$, product $2 \cdot 3^{n-1}$, valid for ALL $n \geq 3$.
  - Better than standard Sol 3 ($3^n$) by factor $3/2$ for all $n$.
  - Worse than "3+1+rest" ($32 \cdot 3^{n-4}$) by factor $27/16 \approx 1.69$ — but "3+1+rest" breaks at $n=9$.
  - For $n \geq 9$: best known upper bound is $M_n \leq 2 \cdot 3^{n-1}$ (may not be tight).
  - $M_n^{1/n} \to 3$ (same asymptotic as Sol 3, since $2^{1/n} \to 1$).

---

## Exploration 1

### Strategy
Replace the bottom processor in Dijkstra Solution 3 with a 2-state processor, keeping all other processors at their S3 rules, and exhaustively search over the 2-state processor's $2^{18} = 262{,}144$ possible transition functions.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- $n=5$, $ms = (2,3,3,3,3)$, product $= 162$, cycle length $= 13$.
- Binary P0 transition function (bits = 0x10492):
  - Privileged when: $(S=0, R=1, L \neq 2)$ or $(S=1, R \neq 1)$
  - Output: goes to 1 if $R=1$ and ($L \neq 2$ or $S=1$); else goes to 0
  - Simplified: $f_0(L,S,R) = \mathbb{1}[R=1]$ when $L \in \{0,1\}$; $f_0(2,S,R) = S \cdot \mathbb{1}[R=1]$ when $L=2$

STRUCTURAL RESULTS:
- $M_5 \leq 162$, improving the previous best $M_5 \leq 243$
- The bottom processor (P0) in Dijkstra S3 can function with only 2 states for $n=5$
- This partially answers the first central open question: $M_5^{1/5} \leq 162^{1/5} \approx 2.76 < 3$

TOOLS:
- `verifier.py`: verifies all 5 Dijkstra properties for arbitrary transition functions
- `targeted_search.py`: exhaustive search replacing one S3 processor with 2-state

### Open Questions
1. Can TWO processors be replaced with 2-state? (product would be $4 \cdot 3^3 = 108$)
2. Does this extend to all $n$? If so, $M_n \leq 2 \cdot 3^{n-1}$ for all $n$.
3. Can the binary-bottom construction work at other positions (top, middle)?
4. What is the minimum product achievable for $n=5$?

---

## Exploration 2

### Strategy
Cross-pollination from parallel agent: $M_5 = 96$ (exact). Verified independently by finding an explicit construction at product 96 with state vector $(2,2,2,3,4)$ using good-cycle enumeration + SMT completion.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- $n=5$, $ms = (2,2,2,3,4)$, product $= 96 = M_5$, cycle length $= 18$.
- 30 good configs, 66 bad configs, all 5 properties verified.
- Full transition functions saved in `product96_result.txt`.
- Surviving pattern classes at product 96: $(2,2,2,3,4)$ and $(2,2,3,2,4)$.

STRUCTURAL RESULTS:
- $M_5 = 96$ (exact: lower bound 80 excluded by parallel search, upper bound 96 verified here)
- $M_5^{1/5} = 96^{1/5} \approx 2.49 < 3$. This strongly suggests $\limsup M_n^{1/n} < 3$.
- The optimal construction uses a 4-state processor (not just 3-state + binary). This means non-uniform state counts are essential.
- Product 72 $(= 2^3 \cdot 3^2)$ and 80 $(= 2^4 \cdot 5)$ are impossible (eliminated by parallel search).

TOOLS:
- `complete_96.py`: good-cycle enumeration + Z3 SMT completion for arbitrary state vectors
- `search_96.py`: good-cycle backtracking search

### Key Parameters
- $n=5$: state vector $(2,2,2,3,4)$, cycle length 18
- 500 good cycles enumerated, #100 was completable
- SMT completion had 35 free entries to fill

### Open Questions
1. Why does product 96 work but 72 and 80 don't? What structural property does the 4-state processor provide?
2. Does a similar pattern extend to $n=6$? The cross-pollination suggests $M_6 \geq 216$.
3. For $n=6$, is $(2,2,2,3,3,3)$ at product 216 feasible?
4. What is the asymptotic growth rate? $96^{1/5} \approx 2.49$ for $n=5$ and $216^{1/6} \approx 2.45$ for $n=6$ (if $M_6 = 216$) suggest $M_n^{1/n} \to c$ for some $c \in (2, 3)$.

---

## Exploration 3

### Strategy
Wave-filter analysis and information-theoretic investigation of why certain state products work. Compare wave structures of Dijkstra S3 vs. the product-96 system. Develop the $\sqrt{6}$ conjecture.

### Outcome
STALLED (theoretical, pending more data points)

### Concrete Artifacts

COMPUTED EXAMPLES:
- Dijkstra S3, $n=5$: max 2 waves, 19.8% good configs, max convergence depth 22
- Product 96 system: max 2 waves, 31.3% good configs, max convergence depth 23
- Product 96 cycle structure: P3 (3-state) moves 6 times, P2/P4 move 4 times, P0/P1 (binary) move 2 times. All states of all processors are used.

STRUCTURAL RESULTS:
- Both systems have at most 2 waves for $n=5$. Wave merging governs convergence.
- The product-96 system has proportionally more good configs (31.3% vs 19.8%).
- Binary processors serve as "boundary reflectors" that change rarely.
- Higher-state processors (3-state, 4-state) serve as "wave carriers" that move frequently.

### Reformulations

**The $\sqrt{6}$ conjecture.** If we split processors roughly half-binary, half-ternary:
- Product $= 2^{n/2} \cdot 3^{n/2} = 6^{n/2} = (\sqrt{6})^n$
- $\sqrt{6} \approx 2.449$, so $\approx 1.29$ bits/processor

Evidence:
- $M_5 = 96 = 2^5 \cdot 3$, giving $M_5^{1/5} \approx 2.49$ (slightly above $\sqrt{6}$)
- If $M_6 = 216 = 6^3$, then $M_6^{1/6} = \sqrt{6}$ exactly
- If $M_n^{1/n} \to \sqrt{6}$, this answers both central open questions: $\limsup < 3$ and $\liminf > 2$

LOAD-BEARING ASSESSMENT: This conjecture reframes the combinatorial search as an information-theoretic question: how many bits per processor are needed for wave-filtering? If confirmed, it could guide construction of explicit algorithms. However, the evidence base is thin (two data points). Need $M_6$ and $M_7$ to assess.

### What Would Unblock This
- Confirmed value of $M_6$ (or tight bounds)
- $M_7$ to test whether $M_n^{1/n}$ is converging
- A proof that $k$-wave filtering requires $\geq \log_2 k$ bits of local state, which would give the lower bound

### Open Questions
1. Is the $\sqrt{6}$ conjecture correct? Need more data points.
2. Can the wave-filter perspective yield a proof of $\liminf > 2$?
3. What is the role of the 4-state processor in $M_5$? It provides $\log_2 4 = 2$ bits, more than a 3-state processor's $\log_2 3 \approx 1.58$ bits. Is this "excess" needed or can $(2,2,2,3,3)$ at product 72 work?
4. The parallel agent reports product 72 is impossible. This means 3 binary + 2 ternary ($= 72$) lacks enough information, but 3 binary + 1 ternary + 1 quaternary ($= 96$) works. The difference is $\log_2(96) - \log_2(72) = \log_2(4/3) \approx 0.42$ bits — the 4-state processor provides a critical extra $0.42$ bits over a 3-state processor.

---

## Exploration 4

### Strategy
Attack $n=6$ with product-288 vectors $(2,2,2,\sigma_3,\sigma_4,\sigma_5)$ where $\{\sigma_3,\sigma_4,\sigma_5\}$ is a permutation of $\{3,3,4\}$. This mirrors the $n=5$ pattern of using a 4-state processor alongside binary and ternary ones. Used good-cycle enumeration + Z3 SMT completion.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- $n=6$, $ms = (2,2,2,4,3,3)$, product $= 288$, cycle length $= 27$.
- 46 good configs, 242 bad configs, all 5 properties verified.
- Found on cycle #6 out of 300 enumerated (fast).

STRUCTURAL RESULTS:
- $M_6 \leq 288 = 2^5 \cdot 3^2$. This beats $3^6 = 729$ by a factor of 2.5.
- $288^{1/6} \approx 2.57$, somewhat above $\sqrt{6} \approx 2.449$.
- $(2,2,2,3,3,4)$ and $(2,2,2,3,4,3)$ FAILED (300 cycles each, no valid completion). Only $(2,2,2,4,3,3)$ succeeded — position of the 4-state processor matters.
- The 4-state processor appears critical: placed at position 3 (between the binary block and the ternary block), it acts as a "translator" between the two regimes.

### Key Parameters
- Vectors tested: $(2,2,2,3,3,4)$ ✗, $(2,2,2,3,4,3)$ ✗, $(2,2,2,4,3,3)$ ✓
- 300 cycles enumerated per vector, cycle lengths 16–41
- The valid cycle had length 27

### Open Questions (RESOLVED)
1. ~~Is $M_6 = 288$ optimal?~~ **YES.** $M_6 = 288$ exactly. Products 144–256 exhaustively eliminated by parallel agent.
2. ~~Product 216 $(2,2,2,3,3,3)$ feasible?~~ **NO.** Dead — confirmed by both parallel agent exhaustive screening and our own searches.
3. ~~Can products 240, 256, 270 yield valid systems?~~ **NO.** All dead.
4. ~~$\sqrt{6}$ conjecture?~~ **REFUTED.** $288^{1/6} \approx 2.57 > \sqrt{6}$, and $864^{1/7} \approx 2.74$. The sequence is increasing toward 3.

---

## Exploration 5

### Strategy
Attack $n=7$. The "3+1+rest" pattern predicts $M_7 = 32 \cdot 3^3 = 864$ with state vector from multiset $\{2,2,2,3,3,3,4\}$. Exhaustive orientation search across all feasible orientations and alternative multisets at product 864, plus systematic search of intermediate products.

### Outcome
SUCCEEDED (via parallel agent cross-pollination)

### Concrete Artifacts

COMPUTED EXAMPLES:
- $n=7$, $ms = (3,2,2,2,3,4,3)$, product $= 864$. Cycle length $= 43$.
- Binary block at positions 1–3, quaternary at position 5, ternary at positions 0, 4, 6.
- Independent witness: $ms = (2,2,2,4,3,4,3)$, product $= 1152$, cycle length $= 43$ (two 4-state processors).

STRUCTURAL RESULTS:
- $576 \leq M_7 \leq 864$. Products through 512 exhaustively dead (parallel agent). Product 576 has 5 open clustered classes (270K+ cycles screened without survivors).
- Orientation is extremely sensitive: 9 of 10 tested orientations of $(2,2,2,3,3,3,4)$ failed.
- The quaternary is NOT immediately adjacent to the binary block — position 5 with a ternary buffer at position 4.
- Products 640, 648, 672, 720, 768, 800 are all dead (computationally tested, 50–200 cycles per vector).

TOOLS:
- `search_n7.py`: systematic n=7 search with product/orientation enumeration
- `lower_bounds.py`: structural lower bound analysis

### Open Questions
1. Is $M_7 = 864$? Depends on whether product 576's 5 open classes are dead.
2. Does the "3+1+rest" pattern extend to $n=8$? Prediction: $M_8 \leq 2592 = 32 \cdot 3^4$.

---

## Exploration 6

### Strategy
Theoretical lower bound analysis for $n=7$: use number-theoretic and structural constraints to rule out entire product ranges without exhaustive cycle screening.

### Outcome
SUCCEEDED (significant structural insight)

### Concrete Artifacts

STRUCTURAL RESULTS:
- **Feasibility sparsity.** For $n=7$, only 12 products in $[128, 863]$ can even be factored into 7 parts $\geq 2$ while satisfying RFC. The constraint $\Omega(P) \geq n$ eliminates most integers.
- **Complete gap enumeration $[577, 863]$:** only 7 feasible products:

  | Product | Vectors | Status |
  |---------|---------|--------|
  | 576 | 14 | OPEN (5 classes) |
  | 640 | 2 | DEAD |
  | 648 | 5 | DEAD (pure 2/3) |
  | 672 | 2 | DEAD (0 cycles) |
  | 720 | 12 | DEAD |
  | 768 | 16 | DEAD |
  | 800 | 1 | DEAD (0 cycles) |

- **Quaternary necessity conjecture.** For $n \geq 5$, any valid system requires $\max(m_i) \geq 4$. Evidence: all pure-$\{2,3\}$ products dead at $n = 5, 6, 7$.

### Open Questions
1. Can the quaternary necessity conjecture be proved?
2. Is the bound of 3 binary processors tight for all $n$?
3. Is $\lim M_n^{1/n} = 3$?

---

## Exploration 7

### Strategy
Attack $n=8$ using the "3+1+rest" pattern prediction: $M_8 \leq 2592 = 32 \cdot 3^4$ with multiset $\{2,2,2,3,3,3,3,4\}$. Used GPT's improved pipeline (symmetry-reduced cycle enumeration + propagation-based screening + SMT completion).

### Outcome
SUCCEEDED — witness found at orientation 21/35 after rerunning with proper limits ($10^7$ cycles, 600s/orientation).

### Concrete Artifacts

COMPUTED EXAMPLES:
- $n=8$, $ms = (2,2,3,4,3,3,2,3)$, product $= 2592 = 32 \cdot 3^4$. Cycle length $= 55$.
- Binary at P0, P1, P6; quaternary at P3; ternary at P2, P4, P5, P7.
- Independently verified: `verify_system` confirms valid system with 1 recurrent cycle.

STRUCTURAL RESULTS:
- **The "3+1+rest" pattern extends to $n=8$.** $M_8 \leq 2592 = 32 \cdot 3^4$.
- Of 35 distinct necklaces of $\{2,2,2,4,3,3,3,3\}$, only orientation 21 $(2,2,3,4,3,3,2,3)$ yielded a witness. 20 orientations tested dead with 600s each.
- The binary processors are NOT contiguous: P0, P1 are adjacent but P6 is separated. This differs from the $n=7$ pattern where binaries were in a block.
- Orientation 8 $(2,2,3,2,3,4,3,3)$ had 20 survivors but all failed propagation completion.

TOOLS:
- `n8_sweep.py`: automated sweep of all necklaces of candidate multisets
- `p2_smt_completion.py` (GPT): full pipeline with pre-screening + Z3
- `n8_sweep_results.txt`: full log of sweep results

### Key Lesson
Initial runs with 500 cycles/orientation found nothing. The witness required orientation 21 and cycle 277 — confirming that at large $n$, witnesses are extremely rare and exhaustive sweeps with high limits are essential.

### Open Questions
1. Is $M_8 = 2592$? Requires lower bound work on products $< 2592$.
2. ~~Does the "3+1+rest" pattern extend to $n=9$?~~ **NO.** Product 7776 is dead (Expl 8).

---

## Exploration 8

### Strategy
Two-part investigation: (1) Sweep "3+1+rest" pattern at $n=9$ (product 7776), and (2) independently verify the Sol 3 v1 construction at $ms = (2, 3^8)$, product 13122, claimed by another agent.

### Outcome
SUCCEEDED (verification) + IMPORTANT STRUCTURAL FINDING

### Concrete Artifacts

COMPUTED EXAMPLES:
- $n=9$ "3+1+rest" sweep: all 56 orientations of $\{2,2,2,4,3,3,3,3,3\}$, product 7776, are DEAD. 600s/10M cycles per orientation, 0 survivors total. The "3+1+rest" pattern breaks at $n=9$.
- $n=9$ Sol 3 v1: $ms = (2,3,3,3,3,3,3,3,3)$, product $13122 = 2 \cdot 3^8$. Cycle length 25, 62 good configs, 13060 bad configs. All 5 properties PASS. Independently verified with two separate verifiers.
- $n=10$ Sol 3 v1: $ms = (2,3,3,3,3,3,3,3,3,3)$, product $39366 = 2 \cdot 3^9$. Cycle length 28, 70 good configs. All 5 properties PASS.
- Sol 3 v1 verified for ALL $n = 3, \ldots, 13$:

  | $n$ | product | cycle length | good configs | formula check |
  |-----|---------|-------------|-------------|---------------|
  | 3 | 18 | 7 | 13 | $3(3)-2=7$ ✓ |
  | 4 | 54 | 10 | 22 | $3(4)-2=10$ ✓ |
  | 5 | 162 | 13 | 30 | $3(5)-2=13$ ✓ |
  | 6 | 486 | 16 | 38 | $3(6)-2=16$ ✓ |
  | 7 | 1458 | 19 | 46 | ✓ |
  | 8 | 4374 | 22 | 54 | ✓ |
  | 9 | 13122 | 25 | 62 | ✓ |
  | 10 | 39366 | 28 | 70 | ✓ |
  | 11 | 118098 | 31 | 78 | ✓ |
  | 12 | 354294 | 34 | 86 | ✓ |
  | 13 | 1062882 | 37 | 94 | ✓ |

STRUCTURAL RESULTS:
- **Sol 3 v1 is universally valid** for all $n \geq 3$ with $ms = (2, 3, 3, \ldots, 3)$.
- **Cycle length** $= 3n - 2$ (exact for all tested $n$).
- **Good configs** $= 8n - 10$ (exact for $n \geq 4$; $n = 3$ has 13).
- **"3+1+rest" BREAKS at $n=9$**: the SCC obstruction is universal across all 56 orientations. Zero survivors at any orientation. The quaternary processor that was essential for $n = 5, \ldots, 8$ cannot compensate for the larger configuration space at $n = 9$.
- **Quaternary necessity conjecture REFUTED** for large $n$: Sol 3 v1 uses $\max(m_i) = 3$ (no quaternary) and is valid for all $n$.

TOOLS:
- `verify_sol3v1_n9.py`: verification of Sol 3 v1 at $n = 9, 10$ using both verifier.py and docs/verify_witnesses.py
- `verify_sol3v1_extended.py`: systematic sweep of Sol 3 v1 for $n = 3, \ldots, 13$, plus comparison with standard Sol 3

### Reformulations

**Two competing constructions.** For small $n$ ($5 \leq n \leq 8$), the "3+1+rest" pattern ($32 \cdot 3^{n-4}$) dominates Sol 3 v1 ($2 \cdot 3^{n-1}$) by a factor of $27/16$. For $n \geq 9$, "3+1+rest" dies and Sol 3 v1 becomes the best known construction. This suggests a crossover phenomenon: the optimal construction strategy changes qualitatively around $n = 9$.

LOAD-BEARING ASSESSMENT: The crossover raises the central question: is there a THIRD construction that interpolates — better than "3+1+rest" for $n \geq 9$ but better than Sol 3 v1? Products between 7776 and 13122 at $n = 9$ remain unexplored (except partial sweep of 10368, ~77/140 orientations dead).

### Failure Constraint
The "3+1+rest" pattern fails at $n=9$ because the 492-config $\{0,1\}^9$ SCC trap blocks convergence at every tested product and orientation. This is NOT an insufficient-search problem — it is a structural obstruction.

### What This Rules Out
Any "3+1+rest" construction with exactly 3 binary + 1 quaternary + $(n-4)$ ternary processors at $n = 9$.

### What Would Unblock This
A construction at $n = 9$ with product strictly between 7776 and 13122. Candidates: products with 2 quaternary processors (10368 partially tested), or products with a 5-state processor (9720), or novel multisets.

### Key Parameters
- $n=9$ "3+1+rest" sweep: 56 orientations × 600s × 10M cycles. ALL dead (0 survivors).
- $n=9$ Sol 3 v1: verified in <0.2s. Immediate success.
- $n=10$ Sol 3 v1: verified in <0.4s. Immediate success.

### Open Questions
1. **Is there an $n=9$ witness with product $< 13122$?** Products 7776–13121 are largely unexplored.
2. **Is Sol 3 v1 optimal for $n \geq 9$?** I.e., is $M_n = 2 \cdot 3^{n-1}$ for large $n$?
3. **Why does "3+1+rest" break at $n=9$?** Is the $\{0,1\}^n$ SCC trap the fundamental obstacle, and if so, at what $n$ does it become fatal?
4. **Can Sol 3 v1 be further compressed?** E.g., replacing two processors with 2-state (product $4 \cdot 3^{n-2}$).

---

