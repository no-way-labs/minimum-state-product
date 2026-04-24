#!/usr/bin/env python3
"""Brainstorm the parity blocker with GPT-5.4"""
import sys
# NOTE: this probe originally imported from a sibling research project
# (paper3_dev_010) that is not part of this artifact. The path below
# resolves to './_paper3_external/...' (placeholder — does not exist).
# The probe is retained for provenance; it documents an attempted
# cross-project comparison and will not run standalone.
sys.path.insert(0, './_paper3_external/generator')
from llm_client import LLMClient

client = LLMClient()

prompt = """I'm formalizing a lower bound proof for self-stabilizing token rings in Lean 4. I'm stuck on one specific mathematical lemma and need a fresh perspective.

THE SETUP:
- Ring of n≥9 processors, at least 3 consecutive binary (state space {0,1})
- A "good cycle" visits distinct configurations, each stepping to the next via one processor firing
- Zero winding: the mover's net displacement around the ring is 0
- No "safe" processor (every processor is within distance 1 of some mover position)

THE GOAL: Prove an "entry conflict" exists — a processor that sees the same local context (L, S, R) at both a step where it fires and a step where it doesn't fire. This contradicts the deterministic transition function.

THE APPROACH THAT WORKS FOR FC=2:
Take the middle binary processor p (= i+1 in the triple {i, i+1, i+2}). Between consecutive firings of p:
- S (p's value) is preserved (p doesn't fire between)
- L (left neighbor i's value) preserved iff i fires even times (binary → returns)
- R (right neighbor i+2's value) preserved iff i+2 fires even times (binary → returns)

When fireCount(p) = 2: there's only 1 gap containing ALL of i's firings (even total) and ALL of i+2's firings (even total). Both parities even → entry conflict.

THE BLOCKER FOR FC≥4:
When p fires ≥4 times: multiple gaps. Each gap has some fire count for i and i+2. The total across all gaps is even for each, but individual gaps can be odd. We need at least ONE gap where BOTH are even. This isn't guaranteed by counting alone — both gaps can be (odd, odd) which sums to (even, even).

WHAT I'VE TRIED:
1. Pigeonhole across gaps (4 parity states, 2k gaps) — doesn't force an EE gap
2. Gap≥4 alternation argument — only works when movers don't wander
3. Contiguous run entry conflict — handles consecutive firings but doesn't help with isolated firings
4. Min-gap edge crossing descent — too many edge cases (gap=1, wrapping, non-binary endpoint)

QUESTION: Is there a proof technique that either:
(a) Shows the parity condition (both even in some gap) IS always satisfied under these hypotheses?
(b) Gives an entry conflict WITHOUT needing the parity condition?
(c) Uses convergence (well-foundedness of bad-step relation) to derive contradiction?
(d) Shows fireCount = 2 for all processors from the hypotheses?

Any fresh angle would help. The math is proved computationally (verified for n=5..13) but I can't express it in Lean's type theory."""

response = client.chat(prompt, model="o3")
print(response.text)
print(f"\n[Tokens used: {response.tokens_used}]")
