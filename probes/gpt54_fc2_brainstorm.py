#!/usr/bin/env python3
"""Send brainstorming prompt to GPT-5.4 about fc<=2 for middle binary processor."""

import sys
sys.path.insert(0, "./_paper3_external/generator")
from llm_client import LLMClient

PROMPT = r"""
We are formalizing in Lean 4 a proof that M_n = 4·3^(n-2) for self-stabilizing token rings (Dijkstra-style). The last major blocker is proving:

**CLAIM**: In any zero-winding good cycle on a ring of size n >= 5 with processors having state counts ms = (m_0, ..., m_{n-1}), if there exist 3 consecutive binary processors at positions {p-1, p, p+1} (each with m = 2, states {0,1}), and the total product < 4·3^(n-2), then fc(p) <= 2 (the middle binary processor fires at most twice).

This is computationally verified at n=5,7,9 with zero exceptions.

**DEFINITIONS**:
- A "good cycle" is a sequence of (config, mover_position) pairs that visits distinct configurations, returns to start, and the mover fires at each step (changing its state). Each processor fires fc(i) times total.
- Binary processors toggle: 0->1 or 1->0. So fc must be even to return to original value. Thus fc(p) in {0, 2, 4, ...}.
- "Zero winding" means the mover positions, viewed as a walk on Z_n, have net displacement 0 (equal CW and CCW steps).
- "Entry conflict" at processor q means some full context (L, S, R) = (state of q-1, state of q, state of q+1) appears at BOTH a step where q is the mover AND a step where q is a non-mover. This is impossible in a valid system (the transition function would need to both change and preserve S).
- The good cycle has length L = sum of all fc(i). Each binary processor has fc in {0, 2, 4, ...}. Each ternary has fc in {0, 3, 6, ...}.

**WHAT WE KNOW / DEAD ENDS**:
1. The "parity-at-p" approach is DEAD: trying to prove L-parity and R-parity are both even at p forces entry conflict at p itself, but M_v ∩ N_v = emptyset by definition, so there's no contradiction at p — entry conflict at p would mean the cycle ISN'T a good cycle, which is what we want to show is impossible with fc>=4, not something we can assume.

2. You (GPT-5.4) previously suggested the "excursion return" argument: if fc(p) >= 4, then between the 1st and 3rd firing of p, a NEIGHBOR (p-1 or p+1) sees a repeated full context, giving entry conflict at the neighbor. This is the most promising analytical direction.

3. We have `native_decide` in Lean 4 for finite decidable checks on bounded state spaces.

**TWO CANDIDATE PATHS**:

**Path A (Analytical — excursion return)**:
- The idea: p fires at times t1 < t2 < t3 < t4. Between t1 and t3, p has toggled twice (returning to original value). Meanwhile p's neighbors (binary, states {0,1}) have also potentially toggled. The key constraint is that p-1 and p+1 each have only 2 states, so their (L,S,R) context lives in {0,1}^3 = 8 possibilities.
- Question: HOW exactly does fc(p) >= 4 force a context repeat at a neighbor? What's the pigeonhole? The neighbor has 8 possible contexts, but the cycle has potentially many steps...
- The constraint must use the BINARY nature of all 3 processors AND the structure of the good cycle (no entry conflict, zero winding).

**Path B (Computational / native_decide)**:
- Encode the 3-binary window as a finite automaton. The local state is (c_{p-1}, c_p, c_{p+1}) in {0,1}^3 = 8 configs. The "rest of the ring" is abstracted.
- Question: What EXACTLY would we decide over? We can't just check the 8 local configs — we need to account for which processor is the mover at each step (could be p-1, p, p+1, or someone outside the window).
- When the mover is OUTSIDE {p-1, p, p+1}, the local state can change at the boundary (c_{p-1} if mover = p-2, or c_{p+1} if mover = p+2). So we'd need to track boundary effects.
- State space: local config (8) x phase info? Is this tractable?

**QUESTIONS FOR YOU**:

1. **Which path is more promising for Lean 4 formalization?** Consider: proof length, conceptual clarity, robustness to edge cases, and ease of Lean encoding.

2. **For Path A**: Give the EXACT mechanism. How does fc(p) >= 4 force entry conflict at p-1 or p+1? State it as a clean lemma with proof sketch. What are the cases? Where does zero-winding enter?

3. **For Path B**: What's the minimal finite structure to decide over? Can we reduce to checking all possible "local traces" of length <= some bound on the 3-binary window? What bound?

4. **Are there other approaches we're missing?** For instance:
   - Could we use the fact that binary processors have only 2 states to get a "short cycle" argument (if fc(p) >= 4, some sub-cycle exists)?
   - Could we use transfer matrices or counting arguments on the binary window?
   - Is there a graph-theoretic argument on the "firing graph"?

5. **Edge cases**: The neighbors p-1, p+1 are also binary. If fc(p) >= 4, what can we say about fc(p-1) and fc(p+1)? Does the binary constraint on neighbors help?

6. **For the Lean encoding**: Would it help to first prove a STRONGER claim like "fc(p-1) + fc(p) + fc(p+1) <= 6" (sum of fires in the binary window is bounded)?

Please think carefully and give detailed, precise arguments. We need something that will actually work in Lean 4, not just a hand-wave.
"""

client = LLMClient()
response = client.chat(PROMPT.strip(), model="gpt-5.4")
print("=" * 80)
print("GPT-5.4 RESPONSE:")
print("=" * 80)
print(response.text)
print("=" * 80)
print(f"Tokens used: {response.tokens_used}")
