# Slab Counting Theorem — SK ≥ 1 for n ≥ 6

## Statement

> **Theorem (Slab Counting).** Let n ≥ 6, ms a multiset with ∏m_i < M_n
> and some m_i ≥ 3, and C a fair simple closed cycle on ms with
> |C| ≥ 2n+2. Then SK(C) ≥ 1.

Combined with:
- **Det consistency** (all-binary ms → only L=2n → Lemma A),
- **Lemma A** (L=2n → |SK| = 2^n − 2n − 2·[n odd] ≥ 1),
- **Lemma B** (L=2n+1 → |SK| ≥ Lemma A value + 2^(n−3) − 1 ≥ 1),
- **n=5 computation** (exhaustive verification on 25 mixed multisets),

this gives: **M_n is a lower bound on the state product of any
self-stabilizing token ring, for all n ≥ 5.**

## Proof

### Setup

Let C = (c_0, c_1, …, c_{L−1}) be a fair simple closed cycle on ms
with mover sequence (p_0, p_1, …, p_{L−1}). The det dictionary
det(C) records L move entries (one per fire) and additional stay
entries (non-movers at each step).

Define:
- V_i = {c_k[i] : 0 ≤ k < L} (value range at position i)
- VC = ∏_i V_i (value-compatible configuration space)
- NG = VC \ C (non-good value-compatible configs)

The **forced graph** G has vertex set NG and edge set: for each det
move entry (p, a, b, d) → e with e ≠ b, and each c ∈ NG with
c[(p−1) mod n] = a, c[p] = b, c[(p+1) mod n] = d, an edge from c
to c' where c'[p] = e and c'[i] = c[i] for i ≠ p, provided c' ∈ NG.

**SK(C) ≥ 1** iff G has a directed cycle.

### Step 1: Slabs

For a det move entry at position p with key (p, a, b, d) → e, define:
- **Source slab** S_src = {c ∈ VC : c[(p−1)] = a, c[p] = b, c[(p+1)] = d}
- **Target slab** S_tgt = {c ∈ VC : c[(p−1)] = a, c[p] = e, c[(p+1)] = d}

Both slabs have the same size:

  |S_src| = |S_tgt| = ∏_{i ∉ {p−1, p, p+1}} |V_i|

Call this S_p, the **slab size** at position p. Since |V_i| ≥ 2 for
all i (fairness: each processor fires ≥ 2 times, visiting ≥ 2 values):

  S_p = ∏_{i ∉ {p−1, p, p+1}} |V_i| ≥ 2^{n−3}

The source and target slabs are **disjoint** (since b ≠ e, configs in
S_src have c[p] = b while configs in S_tgt have c[p] = e).

A det move entry produces a **VC-NG edge** iff there exists c ∈ S_src ∩ NG
whose target c' ∈ S_tgt ∩ NG. An entry is **blocked** iff it produces
zero VC-NG edges.

### Step 2: Blocking condition

An entry at position p is blocked iff: for every c ∈ S_src, either
c ∈ C or c' ∈ C (the source or target is a cycle config).

Define α = |S_src ∩ C| and β = |S_tgt ∩ C|. A source c ∈ S_src \ C
has its target c' blocked iff c' ∈ C, i.e., c' ∈ S_tgt ∩ C. Since
the source-to-target map is a bijection on the slab (changing only
c[p] from b to e), exactly β sources in S_src \ C have their target
in C.

So: unblocked pairs = |S_src \ C| − β = (S_p − α) − β = S_p − α − β.

Entry is blocked iff **α + β ≥ S_p**.

### Step 3: Counting argument

Sum α + β over all L move entries. Each cycle config c ∈ C
contributes to this sum as follows:

**Source contribution (α):** At each position p, c is in the source
slab of at most one entry (the one whose source triple matches c's
triple at p). Across all L entries, c contributes at most once per
entry. But the total Σ α across all entries at all positions is
exactly L: each fire step t has exactly one cycle config c_t in the
source slab of the entry created at step t.

  Σ_{all entries} α = L

**Target contribution (β):** At each position p, c is in the target
slab of at most one entry (the one whose target triple matches c's
triple at p). Across all n positions, c contributes at most n to the
total Σ β.

  Σ_{all entries} β ≤ n · L

(Each of L cycle configs contributes at most n, one per position.)

**Total:**

  Σ_{all entries} (α + β) ≤ L + nL = (n + 1)L

**Need for all entries to be blocked:**

  Σ_{all entries} (α + β) ≥ Σ_{all entries} S_p ≥ L · 2^{n−3}

(Since there are L entries, each needing α + β ≥ S_p ≥ 2^{n−3}.)

**Contradiction when 2^{n−3} > n + 1:**

  L · 2^{n−3} > (n + 1) · L

This simplifies to **2^{n−3} > n + 1**, which holds for all **n ≥ 6**:

| n | 2^{n−3} | n+1 | holds? |
|---|---------|-----|--------|
| 6 |       8 |   7 | ✓      |
| 7 |      16 |   8 | ✓      |
| 8 |      32 |   9 | ✓      |
| 9 |      64 |  10 | ✓      |

(And for all larger n, since 2^{n−3} grows exponentially while n+1
grows linearly.)

Therefore: **not all entries can be blocked**. At least one entry has
an unblocked pair, producing a VC-NG edge.

### Step 4: Edge implies cycle

The forced graph G has at least one edge (from step 3). Starting from
any vertex with an outgoing edge, follow the chain of forced edges.
Since G is a finite graph, the chain must eventually revisit a vertex,
forming a directed cycle. Therefore SK(C) ≥ 1. **∎**

## Scope and limitations

- **n ≥ 6 only.** At n = 5: 2^2 = 4 < 6 = n+1. The counting has
  slack on the wrong side. n=5 requires separate treatment
  (exhaustive computation on 25 mixed sub-M_5 multisets).

- **Mixed multisets only.** All-binary multisets (all m_i = 2) are
  handled by the det consistency theorem + Lemma A: the only fair
  cycles have L = 2n, and Lemma A gives |SK| = 2^n − 2n − 2·[n odd] ≥ 1.

- **L ≥ 2n+2 only.** L = 2n is Lemma A, L = 2n+1 is Lemma B.

- **The bound is SK ≥ 1, not SK ≥ 2^{n−1}.** This suffices for the
  lower bound proof (SK ≥ 1 → forced graph has trapped configs →
  system not self-stabilizing).

## Proof in Lean (sketch)

```lean
/-- At n ≥ 6, the slab size exceeds the blocking budget. -/
theorem slab_gt_budget (n : ℕ) (hn : 6 ≤ n) : n + 1 < 2^(n-3) := by
  omega  -- or interval_cases for small n, then induction

/-- A fair cycle on a mixed sub-M_n multiset has SK ≥ 1. -/
theorem sk_pos_of_slab_counting
    (n : ℕ) (hn : 6 ≤ n)
    (ms : Fin n → ℕ) (hms : ∀ i, 2 ≤ ms i)
    (hmixed : ∃ i, 3 ≤ ms i)
    (hprod : ∏ i, ms i < M_n n)
    (C : FairCycle ms) (hL : 2*n + 2 ≤ C.length) :
    1 ≤ C.sk := by
  -- Step 1-3: pigeonhole on slab sizes vs blocking budget
  have h_slab : ∀ entry, entry.slab_size ≥ 2^(n-3) := slab_size_ge_binary C
  have h_budget : ∑ entry, (entry.α + entry.β) ≤ (n+1) * C.length :=
    blocking_budget_bound C
  have h_need : (n+1) * C.length < 2^(n-3) * C.length :=
    Nat.mul_lt_mul_right C.length_pos (slab_gt_budget n hn)
  -- So ∑(α+β) < ∑ slab_size → some entry is unblocked
  obtain ⟨entry, h_unblocked⟩ := exists_unblocked_entry C h_budget h_need
  -- Step 4: unblocked entry → edge → chain → cycle
  exact sk_pos_of_edge C (edge_of_unblocked entry h_unblocked)
```

The key lemmas:
1. `slab_size_ge_binary`: each slab has ≥ 2^{n−3} configs
2. `blocking_budget_bound`: total (α+β) ≤ (n+1)L
3. `slab_gt_budget`: 2^{n−3} > n+1 for n ≥ 6
4. `exists_unblocked_entry`: pigeonhole extraction
5. `edge_of_unblocked`: unblocked entry → VC-NG edge
6. `sk_pos_of_edge`: edge in finite graph → cycle → SK ≥ 1

## Connections

This theorem replaces:
- Shadow Cycle Mirror Theorem (CIC Expl 11–12)
- Palindromic Entry Conflict (CIC Expl 14)
- Universal Entry Conflict (BinSCC Expl 10)
- Wiggle Shadow Cycle (CIC Expl 12–13, 15)

All four constructive mechanisms are subsumed by one counting
inequality. The Lean formalization should be under 200 lines
(vs thousands for the constructive proofs).

## Full lower bound architecture

```
theorem lower_bound (n : ℕ) (hn : 5 ≤ n)
    (ms : Fin n → ℕ) (hms : ∀ i, 2 ≤ ms i)
    (hprod : ∏ i, ms i < M_n n) :
    ¬ SelfStabilizing ms := by
  intro ⟨f, G, hvalid⟩
  -- G is a fair simple closed cycle
  have hsk : 1 ≤ G.sk := by
    by_cases hall : ∀ i, ms i = 2
    · -- All-binary: det consistency → L = 2n → Lemma A
      exact lemma_a_pos (det_consistency_length hall G)
    · -- Mixed: some m_i ≥ 3
      push_neg at hall
      obtain ⟨i, hi⟩ := hall
      by_cases hL : G.length ≤ 2*n + 1
      · -- Short cycle: Lemma A or B
        interval_cases G.length <;> [exact lemma_a_pos ..; exact lemma_b_pos ..]
      · -- Long cycle, n ≥ 6: slab counting
        by_cases hn6 : 6 ≤ n
        · exact sk_pos_of_slab_counting n hn6 ms hms ⟨i, hi⟩ hprod G (by omega)
        · -- n = 5: computational verification
          interval_cases n  -- only n = 5 remains
          exact sk_pos_n5_computation ms hms ⟨i, hi⟩ hprod G (by omega)
  -- SK ≥ 1 contradicts validity
  exact absurd hsk (sk_eq_zero_of_valid hvalid)
```
