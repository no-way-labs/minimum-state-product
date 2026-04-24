#!/usr/bin/env python3
"""Static edit-law catalogue for the current Case 3c template layer.

This freezes the exact gain/loss sets for the observed template catalogue so
later large-range verifier work can consume a stable law table instead of
re-deriving template edits from low-n probes.
"""

from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass


REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from probes.gpt.glb_case3c_spine_shift_compare import shift_rule
from probes.gpt.glb_case3c_template_catalogue import template_for_case


AnchoredRule = tuple[str, tuple[int, int, int], int]


@dataclass(frozen=True)
class StaticTemplateLaw:
    template_id: str
    losses: frozenset[AnchoredRule]
    gains: frozenset[AnchoredRule]
    source: str

    @property
    def size_slope(self) -> int:
        return len(self.gains) - len(self.losses)


TEMPLATE_LAWS: dict[str, StaticTemplateLaw] = {
    "reverse_base_light": StaticTemplateLaw(
        template_id="reverse_base_light",
        losses=frozenset(),
        gains=frozenset(
            {
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 1),
                ("Q", (0, 1, 1), 1),
                ("Q", (1, 1, 1), 1),
                ("Q-2", (1, 1, 2), 2),
                ("Q-2", (1, 2, 2), 2),
                ("Q-2", (2, 0, 0), 0),
                ("Q-2", (2, 2, 0), 0),
                ("Q-2", (2, 2, 2), 2),
            }
        ),
        source="exploration_log_allkiller.md (reverse base n=9->10 tail-edit inventory)",
    ),
    "reverse_base_dense": StaticTemplateLaw(
        template_id="reverse_base_dense",
        losses=frozenset(
            {
                ("Q-1", (0, 2, 0), 0),
                ("Q-1", (0, 2, 1), 2),
                ("Q-1", (1, 0, 0), 0),
                ("Q-1", (1, 1, 0), 0),
                ("Q-1", (2, 0, 0), 0),
                ("Q-1", (2, 0, 1), 2),
                ("Q-1", (2, 2, 1), 2),
                ("Q-2", (0, 0, 2), 0),
                ("Q-2", (1, 1, 0), 2),
                ("Q-2", (1, 2, 0), 2),
                ("Q-2", (2, 0, 2), 0),
                ("Q-2", (2, 2, 0), 2),
                ("Q-2", (2, 2, 2), 0),
            }
        ),
        gains=frozenset(
            {
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 1),
                ("Q", (0, 1, 1), 1),
                ("Q", (0, 2, 0), 0),
                ("Q", (0, 2, 1), 2),
                ("Q", (1, 0, 0), 0),
                ("Q", (1, 1, 0), 0),
                ("Q", (1, 1, 1), 1),
                ("Q", (2, 0, 0), 0),
                ("Q", (2, 0, 1), 2),
                ("Q", (2, 2, 1), 2),
                ("Q-1", (0, 0, 2), 0),
                ("Q-1", (1, 1, 0), 2),
                ("Q-1", (1, 2, 0), 2),
                ("Q-1", (2, 0, 2), 0),
                ("Q-1", (2, 2, 0), 2),
                ("Q-1", (2, 2, 2), 0),
                ("Q-2", (1, 1, 2), 2),
                ("Q-2", (1, 2, 2), 2),
                ("Q-2", (2, 0, 0), 0),
                ("Q-2", (2, 2, 0), 0),
                ("Q-2", (2, 2, 2), 2),
            }
        ),
        source="/tmp/semi_rev_base_actual.out",
    ),
    "forward_base_uniform": StaticTemplateLaw(
        template_id="forward_base_uniform",
        losses=frozenset(
            {
                ("Q-1", (0, 0, 1), 0),
                ("Q-1", (0, 2, 1), 0),
                ("Q-1", (1, 0, 1), 1),
                ("Q-1", (2, 1, 0), 2),
                ("Q-1", (2, 2, 0), 2),
            }
        ),
        gains=frozenset(
            {
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 0),
                ("Q", (0, 2, 1), 0),
                ("Q", (1, 0, 1), 1),
                ("Q", (1, 1, 0), 1),
                ("Q", (1, 1, 1), 1),
                ("Q", (2, 1, 0), 2),
                ("Q", (2, 2, 0), 2),
                ("Q", (2, 2, 1), 2),
                ("Q-1", (0, 0, 2), 0),
                ("Q-1", (0, 2, 2), 0),
                ("Q-1", (1, 0, 0), 1),
                ("Q-1", (2, 1, 1), 2),
                ("Q-1", (2, 2, 2), 2),
            }
        ),
        source="/tmp/local_fwd_base_actual.out and /tmp/semi_fwd_base_actual.out",
    ),
    "reverse_upper_light": StaticTemplateLaw(
        template_id="reverse_upper_light",
        losses=frozenset(
            {
                ("Q-2", (0, 0, 1), 1),
                ("Q-2", (0, 1, 1), 1),
            }
        ),
        gains=frozenset(
            {
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 1),
                ("Q", (0, 1, 1), 1),
                ("Q-2", (2, 0, 0), 0),
                ("Q-2", (2, 2, 0), 0),
                ("Q-3", (0, 0, 1), 1),
                ("Q-3", (0, 1, 1), 1),
                ("Q-3", (1, 1, 1), 1),
                ("Q-3", (1, 1, 2), 2),
                ("Q-3", (1, 2, 2), 2),
                ("Q-3", (2, 2, 2), 2),
            }
        ),
        source="/tmp/asym_rev_upper_actual.out and /tmp/local_rev_upper_actual.out",
    ),
    "reverse_upper_trailing2": StaticTemplateLaw(
        template_id="reverse_upper_trailing2",
        losses=frozenset(
            {
                ("Q-2", (0, 0, 1), 1),
                ("Q-2", (0, 1, 1), 1),
                ("Q-4", (0, 0, 1), 1),
                ("Q-4", (0, 1, 1), 1),
                ("Q-4", (1, 1, 1), 1),
            }
        ),
        gains=frozenset(
            {
                ("P5", (0, 0, 1), 1),
                ("P5", (0, 1, 1), 1),
                ("P5", (1, 1, 1), 1),
                ("P5", (1, 1, 2), 2),
                ("P5", (1, 2, 2), 2),
                ("P5", (2, 2, 2), 2),
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 1),
                ("Q", (0, 1, 1), 1),
                ("Q-3", (0, 0, 1), 1),
                ("Q-3", (0, 1, 1), 1),
                ("Q-3", (1, 1, 1), 1),
                ("Q-3", (2, 0, 0), 0),
                ("Q-4", (2, 2, 0), 0),
            }
        ),
        source="/tmp/trailing2_rev_upper_derive.out",
    ),
    "reverse_upper_semi": StaticTemplateLaw(
        template_id="reverse_upper_semi",
        losses=frozenset(
            {
                ("Q-2", (0, 0, 1), 1),
                ("Q-2", (0, 1, 1), 1),
                ("Q-2", (1, 2, 0), 2),
            }
        ),
        gains=frozenset(
            {
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 1),
                ("Q", (0, 1, 1), 1),
                ("Q-1", (1, 2, 0), 2),
                ("Q-2", (2, 0, 0), 0),
                ("Q-2", (2, 2, 0), 0),
                ("Q-3", (0, 0, 1), 1),
                ("Q-3", (0, 1, 1), 1),
                ("Q-3", (0, 2, 2), 2),
                ("Q-3", (1, 1, 1), 1),
                ("Q-3", (1, 2, 2), 2),
            }
        ),
        source="/tmp/semi_rev_upper_actual.out",
    ),
    "forward_upper_light": StaticTemplateLaw(
        template_id="forward_upper_light",
        losses=frozenset(
            {
                ("Q-1", (0, 0, 1), 0),
                ("Q-1", (0, 2, 0), 2),
                ("Q-1", (1, 0, 1), 1),
                ("Q-1", (1, 1, 1), 1),
                ("Q-3", (0, 0, 1), 0),
                ("Q-3", (2, 2, 0), 2),
            }
        ),
        gains=frozenset(
            {
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 0),
                ("Q", (0, 2, 0), 2),
                ("Q", (1, 0, 1), 1),
                ("Q", (1, 1, 1), 1),
                ("Q-1", (1, 0, 0), 1),
                ("Q-1", (1, 1, 0), 1),
                ("Q-2", (0, 0, 1), 0),
                ("Q-2", (1, 1, 1), 1),
                ("Q-2", (2, 2, 0), 2),
                ("Q-2", (2, 2, 1), 2),
                ("Q-3", (0, 0, 2), 0),
                ("Q-3", (0, 2, 2), 0),
                ("Q-3", (2, 1, 1), 2),
                ("Q-3", (2, 2, 2), 2),
            }
        ),
        source="/tmp/rep_fwd_upper_family.out and /tmp/local_fwd_upper_actual.out",
    ),
    "forward_upper_semi": StaticTemplateLaw(
        template_id="forward_upper_semi",
        losses=frozenset(
            {
                ("Q-1", (0, 0, 1), 0),
                ("Q-1", (1, 0, 1), 1),
                ("Q-1", (1, 1, 1), 1),
            }
        ),
        gains=frozenset(
            {
                ("Q", (0, 0, 0), 0),
                ("Q", (0, 0, 1), 0),
                ("Q", (0, 2, 0), 2),
                ("Q", (1, 0, 1), 1),
                ("Q", (1, 1, 1), 1),
                ("Q-1", (1, 0, 0), 1),
                ("Q-1", (1, 1, 0), 1),
                ("Q-2", (0, 0, 1), 0),
                ("Q-3", (0, 0, 2), 0),
            }
        ),
        source="/tmp/semi_fwd_upper_actual.out",
    ),
}


def law_for_case(
    regime_label: str,
    orientation: str,
    include_upper_wiggle: bool,
) -> StaticTemplateLaw:
    template_id = template_for_case(regime_label, orientation, include_upper_wiggle)
    return TEMPLATE_LAWS[template_id]


def apply_template_step(
    spine: frozenset[AnchoredRule],
    template_id: str,
) -> frozenset[AnchoredRule]:
    law = TEMPLATE_LAWS[template_id]
    shifted = frozenset(shift_rule(rule) for rule in spine)
    return frozenset((shifted - law.losses) | law.gains)


def print_summary() -> None:
    for template_id in sorted(TEMPLATE_LAWS):
        law = TEMPLATE_LAWS[template_id]
        print(
            f"template={template_id} slope={law.size_slope} "
            f"losses={len(law.losses)} gains={len(law.gains)}"
        )
        print(f"  source={law.source}")


def print_rules() -> None:
    for template_id in sorted(TEMPLATE_LAWS):
        law = TEMPLATE_LAWS[template_id]
        print(
            f"template={template_id} slope={law.size_slope} "
            f"losses={len(law.losses)} gains={len(law.gains)}"
        )
        print(f"  loss_rules={sorted(law.losses)}")
        print(f"  gain_rules={sorted(law.gains)}")
        print(f"  source={law.source}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("summary", "rules"), default="summary")
    args = parser.parse_args()

    if args.mode == "rules":
        print_rules()
        return
    print_summary()


if __name__ == "__main__":
    main()
