#!/usr/bin/env python3
"""Compressed template catalogue for the current Case 3c regime laws.

This is a research summary layer above the recurrence scripts. It records the
observed compression of the small-n regime catalogue into a smaller set of edit
templates after the branch-selection correction from explorations 28-31.

The catalogue is intentionally lightweight: it does not re-derive the laws.
Its job is to make the current meta-law visible and give later scripts a stable
place to read the observed template structure from.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass


FamilyKey = tuple[str, bool]


def family_name(orientation: str, include_upper_wiggle: bool) -> str:
    return f"{orientation}_{'upper' if include_upper_wiggle else 'base'}"


@dataclass(frozen=True)
class ObservedTemplate:
    template_id: str
    size_slope: int
    loss_count: int
    gain_count: int
    loss_bands: tuple[str, ...]
    gain_bands: tuple[str, ...]
    note: str


@dataclass(frozen=True)
class ObservedCase:
    regime_label: str
    orientation: str
    include_upper_wiggle: bool
    base_n: int
    source: str

    @property
    def family(self) -> str:
        return family_name(self.orientation, self.include_upper_wiggle)

    @property
    def case_id(self) -> str:
        return f"{self.regime_label}/{self.family}"


@dataclass(frozen=True)
class MetaTemplate:
    meta_id: str
    template_ids: tuple[str, ...]
    shared_regimes: tuple[str, ...]
    shared_invariants: tuple[str, ...]
    relation: str


TEMPLATES: dict[str, ObservedTemplate] = {
    "reverse_base_light": ObservedTemplate(
        template_id="reverse_base_light",
        size_slope=9,
        loss_count=0,
        gain_count=9,
        loss_bands=(),
        gain_bands=("Q", "Q-2"),
        note="reverse-base light branch: pure extension on the tail corridor",
    ),
    "reverse_base_dense": ObservedTemplate(
        template_id="reverse_base_dense",
        size_slope=9,
        loss_count=13,
        gain_count=22,
        loss_bands=("Q-1", "Q-2"),
        gain_bands=("Q", "Q-1", "Q-2"),
        note="reverse-base dense branch: all-completion semi-symmetric family",
    ),
    "forward_base_uniform": ObservedTemplate(
        template_id="forward_base_uniform",
        size_slope=9,
        loss_count=5,
        gain_count=14,
        loss_bands=("Q-1",),
        gain_bands=("Q", "Q-1"),
        note="forward-base uniform replacement law across current regimes",
    ),
    "reverse_upper_light": ObservedTemplate(
        template_id="reverse_upper_light",
        size_slope=9,
        loss_count=2,
        gain_count=11,
        loss_bands=("Q-2",),
        gain_bands=("Q", "Q-2", "Q-3"),
        note="reverse-upper light branch shared by local and asymmetric families",
    ),
    "reverse_upper_trailing2": ObservedTemplate(
        template_id="reverse_upper_trailing2",
        size_slope=9,
        loss_count=5,
        gain_count=14,
        loss_bands=("Q-2", "Q-4"),
        gain_bands=("P5", "Q", "Q-3", "Q-4"),
        note="reverse-upper trailing-2 exceptional branch",
    ),
    "reverse_upper_semi": ObservedTemplate(
        template_id="reverse_upper_semi",
        size_slope=8,
        loss_count=3,
        gain_count=11,
        loss_bands=("Q-2",),
        gain_bands=("Q", "Q-1", "Q-2", "Q-3"),
        note="reverse-upper semi-symmetric all-completion branch",
    ),
    "forward_upper_light": ObservedTemplate(
        template_id="forward_upper_light",
        size_slope=9,
        loss_count=6,
        gain_count=15,
        loss_bands=("Q-1", "Q-3"),
        gain_bands=("Q", "Q-1", "Q-2", "Q-3"),
        note="forward-upper light branch shared by local and asymmetric families",
    ),
    "forward_upper_semi": ObservedTemplate(
        template_id="forward_upper_semi",
        size_slope=6,
        loss_count=3,
        gain_count=9,
        loss_bands=("Q-1",),
        gain_bands=("Q", "Q-1", "Q-2", "Q-3"),
        note="forward-upper semi-symmetric all-completion branch",
    ),
}


CASES: tuple[ObservedCase, ...] = (
    ObservedCase("asymmetric_1ab", "reverse", False, 9, "family_recurrence"),
    ObservedCase("local_11k", "reverse", False, 10, "regime_recurrence"),
    ObservedCase("semi_symmetric_2plus", "reverse", False, 10, "regime_recurrence"),
    ObservedCase("asymmetric_1ab", "forward", False, 9, "family_recurrence"),
    ObservedCase("local_11k", "forward", False, 10, "regime_recurrence"),
    ObservedCase("semi_symmetric_2plus", "forward", False, 10, "regime_recurrence"),
    ObservedCase("asymmetric_1ab", "reverse", True, 10, "regime_recurrence"),
    ObservedCase("local_11k", "reverse", True, 10, "regime_recurrence"),
    ObservedCase("reverse_upper_trailing2", "reverse", True, 10, "regime_recurrence"),
    ObservedCase("semi_symmetric_2plus", "reverse", True, 10, "regime_recurrence"),
    ObservedCase("asymmetric_1ab", "forward", True, 11, "family_recurrence"),
    ObservedCase("local_11k", "forward", True, 10, "regime_recurrence"),
    ObservedCase("semi_symmetric_2plus", "forward", True, 10, "regime_recurrence"),
)

META_TEMPLATES: dict[str, MetaTemplate] = {
    "upper_light_oriented": MetaTemplate(
        meta_id="upper_light_oriented",
        template_ids=("reverse_upper_light", "forward_upper_light"),
        shared_regimes=("asymmetric_1ab", "local_11k"),
        shared_invariants=(
            "upper family only",
            "shared by local and asymmetric regimes",
            "size slope 9 in both orientations",
        ),
        relation=(
            "orientation-parametrized pair; the exact edit signatures differ "
            "(reverse 2/11 versus forward 6/15), so this is a qualitative "
            "compression, not one exact template"
        ),
    ),
    "upper_semi_oriented": MetaTemplate(
        meta_id="upper_semi_oriented",
        template_ids=("reverse_upper_semi", "forward_upper_semi"),
        shared_regimes=("semi_symmetric_2plus",),
        shared_invariants=(
            "upper family only",
            "semi-symmetric all-completion branch",
            "three losses in both orientations",
        ),
        relation=(
            "orientation-parametrized pair; the slopes stay distinct "
            "(reverse 8 versus forward 6), so the current data does not support "
            "collapsing this to one orientation-free normalized law"
        ),
    ),
    "upper_exceptional_reverse": MetaTemplate(
        meta_id="upper_exceptional_reverse",
        template_ids=("reverse_upper_trailing2",),
        shared_regimes=("reverse_upper_trailing2",),
        shared_invariants=(
            "upper family only",
            "reverse orientation only",
            "trailing-2 exceptional branch",
        ),
        relation="singleton reverse-only exceptional template",
    ),
}


def template_for_case(
    regime_label: str,
    orientation: str,
    include_upper_wiggle: bool,
) -> str:
    family = family_name(orientation, include_upper_wiggle)
    if family == "reverse_base":
        if regime_label in {"asymmetric_1ab", "local_11k"}:
            return "reverse_base_light"
        if regime_label == "semi_symmetric_2plus":
            return "reverse_base_dense"
    elif family == "forward_base":
        if regime_label in {"asymmetric_1ab", "local_11k", "semi_symmetric_2plus"}:
            return "forward_base_uniform"
    elif family == "reverse_upper":
        if regime_label in {"asymmetric_1ab", "local_11k"}:
            return "reverse_upper_light"
        if regime_label == "reverse_upper_trailing2":
            return "reverse_upper_trailing2"
        if regime_label == "semi_symmetric_2plus":
            return "reverse_upper_semi"
    elif family == "forward_upper":
        if regime_label in {"asymmetric_1ab", "local_11k"}:
            return "forward_upper_light"
        if regime_label == "semi_symmetric_2plus":
            return "forward_upper_semi"
    raise ValueError(f"no observed template for {regime_label}/{family}")


def cases_by_template() -> dict[str, list[ObservedCase]]:
    grouped: dict[str, list[ObservedCase]] = {template_id: [] for template_id in TEMPLATES}
    for case in CASES:
        grouped[template_for_case(case.regime_label, case.orientation, case.include_upper_wiggle)].append(case)
    return grouped


def meta_template_for_template(template_id: str) -> str:
    for meta_id, meta in META_TEMPLATES.items():
        if template_id in meta.template_ids:
            return meta_id
    raise ValueError(f"no meta-template for template {template_id}")


def meta_template_for_case(
    regime_label: str,
    orientation: str,
    include_upper_wiggle: bool,
) -> str:
    template_id = template_for_case(regime_label, orientation, include_upper_wiggle)
    return meta_template_for_template(template_id)


def cases_by_meta_template() -> dict[str, list[ObservedCase]]:
    grouped: dict[str, list[ObservedCase]] = {meta_id: [] for meta_id in META_TEMPLATES}
    for case in CASES:
        if not case.include_upper_wiggle:
            continue
        grouped[meta_template_for_case(case.regime_label, case.orientation, case.include_upper_wiggle)].append(case)
    return grouped


def print_templates() -> None:
    grouped = cases_by_template()
    for template_id in sorted(TEMPLATES):
        template = TEMPLATES[template_id]
        members = sorted(case.case_id for case in grouped[template_id])
        print(
            f"template={template.template_id} slope={template.size_slope} "
            f"losses={template.loss_count} gains={template.gain_count}"
        )
        print(f"  loss_bands={template.loss_bands}")
        print(f"  gain_bands={template.gain_bands}")
        print(f"  members={members}")
        print(f"  note={template.note}")


def print_cases() -> None:
    for case in sorted(CASES, key=lambda row: (row.family, row.regime_label)):
        template_id = template_for_case(case.regime_label, case.orientation, case.include_upper_wiggle)
        print(
            f"case={case.case_id} template={template_id} base_n={case.base_n} "
            f"source={case.source}"
        )


def print_meta_templates() -> None:
    grouped = cases_by_meta_template()
    for meta_id in sorted(META_TEMPLATES):
        meta = META_TEMPLATES[meta_id]
        members = sorted(case.case_id for case in grouped[meta_id])
        print(f"meta={meta.meta_id} templates={meta.template_ids}")
        print(f"  shared_regimes={meta.shared_regimes}")
        print(f"  shared_invariants={meta.shared_invariants}")
        print(f"  members={members}")
        print(f"  relation={meta.relation}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("templates", "cases", "meta"), default="templates")
    args = parser.parse_args()

    if args.mode == "cases":
        print_cases()
        return
    if args.mode == "meta":
        print_meta_templates()
        return
    print_templates()


if __name__ == "__main__":
    main()
