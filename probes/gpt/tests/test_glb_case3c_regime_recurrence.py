import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
REGIME_RECURRENCE_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_regime_recurrence.py"
)
FAMILY_RECURRENCE_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_family_recurrence.py"
)


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class RegimeRecurrenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.regime = load_module("glb_case3c_regime_recurrence_test", REGIME_RECURRENCE_PY)
        cls.family = load_module("glb_case3c_family_recurrence_test_2", FAMILY_RECURRENCE_PY)

    def test_asymmetric_reverse_base_matches_existing_representative_law(self) -> None:
        regime_law = self.regime.derive_law("asymmetric_1ab", "reverse", False, timeout_ms=1200)
        family_law = self.family.derive_law("reverse", include_upper_wiggle=False, timeout_ms=1200)

        self.assertEqual(regime_law.base_n, 9)
        self.assertEqual(regime_law.base_gaps, (1, 2, 3))
        self.assertEqual(regime_law.base_spine, family_law.base_spine)
        self.assertEqual(regime_law.losses, family_law.losses)
        self.assertEqual(regime_law.gains, family_law.gains)
        self.assertEqual(self.regime.expected_size(11, regime_law), 61)

    def test_local_regime_reverse_base_packages_from_actual_completion_branch(self) -> None:
        law = self.regime.derive_law(
            "local_11k",
            "reverse",
            False,
            base_n=10,
            timeout_ms=1200,
        )
        actual_n11 = self.regime.probe_summary_for_gaps(
            (1, 1, 6),
            "reverse",
            False,
            1200,
            "lexmin",
            "actual_completion",
        )

        self.assertEqual(law.base_gaps, (1, 1, 5))
        self.assertEqual(law.assignment_mode, "actual_completion")
        self.assertEqual(self.regime.expected_size(11, law), 72)
        self.assertEqual(
            self.regime.generate_spine(11, law),
            frozenset(actual_n11["normalized_common_spine_rules"]),
        )

    def test_semi_symmetric_reverse_base_packages_from_actual_completion_branch(self) -> None:
        law = self.regime.derive_law(
            "semi_symmetric_2plus",
            "reverse",
            False,
            base_n=10,
            timeout_ms=1200,
        )
        actual_n12 = self.regime.probe_summary_for_gaps(
            (2, 2, 5),
            "reverse",
            False,
            1200,
            "lexmin",
            "actual_completion",
        )

        self.assertEqual(law.base_gaps, (2, 2, 3))
        self.assertEqual(law.assignment_mode, "actual_completion")
        self.assertEqual(self.regime.expected_size(12, law), 78)
        self.assertEqual(
            self.regime.generate_spine(12, law),
            frozenset(actual_n12["normalized_common_spine_rules"]),
        )

    def test_reverse_upper_trailing2_packages_from_actual_completion_branch(self) -> None:
        law = self.regime.derive_law(
            "reverse_upper_trailing2",
            "reverse",
            True,
            base_n=10,
            timeout_ms=1200,
        )
        actual_n11 = self.regime.probe_summary_for_gaps(
            (1, 5, 2),
            "reverse",
            True,
            1200,
            "lexmin",
            "actual_completion",
        )

        self.assertEqual(law.base_gaps, (1, 4, 2))
        self.assertEqual(law.assignment_mode, "actual_completion")
        self.assertEqual(self.regime.expected_size(11, law), 55)
        self.assertEqual(
            self.regime.generate_spine(11, law),
            frozenset(actual_n11["normalized_common_spine_rules"]),
        )


if __name__ == "__main__":
    unittest.main()
