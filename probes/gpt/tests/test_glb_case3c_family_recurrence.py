import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RECURRENCE_PY = (
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


class FamilyRecurrenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.recurrence = load_module("glb_case3c_family_recurrence_test", RECURRENCE_PY)

    def test_upper_law_counts_match_observed_templates(self) -> None:
        reverse = self.recurrence.derive_law("reverse", include_upper_wiggle=True, timeout_ms=1200)
        forward = self.recurrence.derive_law("forward", include_upper_wiggle=True, timeout_ms=1200)

        self.assertEqual(reverse.base_n, 10)
        self.assertEqual(len(reverse.base_spine), 40)
        self.assertEqual(len(reverse.losses), 2)
        self.assertEqual(len(reverse.gains), 11)
        self.assertEqual(reverse.size_slope, 9)

        self.assertEqual(forward.base_n, 11)
        self.assertEqual(len(forward.base_spine), 72)
        self.assertEqual(len(forward.losses), 6)
        self.assertEqual(len(forward.gains), 15)
        self.assertEqual(forward.size_slope, 9)

    def test_generated_upper_spines_match_probe_at_n13(self) -> None:
        reverse = self.recurrence.derive_law("reverse", include_upper_wiggle=True, timeout_ms=1200)
        forward = self.recurrence.derive_law("forward", include_upper_wiggle=True, timeout_ms=1200)

        reverse_n13 = self.recurrence.generate_spine(13, reverse)
        forward_n13 = self.recurrence.generate_spine(13, forward)

        reverse_actual = self.recurrence.probe_summary(13, "reverse", True, 1200, "lexmin")
        forward_actual = self.recurrence.probe_summary(13, "forward", True, 1200, "lexmin")

        self.assertEqual(reverse_n13, frozenset(reverse_actual["normalized_common_spine_rules"]))
        self.assertEqual(forward_n13, frozenset(forward_actual["normalized_common_spine_rules"]))
        self.assertEqual(self.recurrence.expected_size(13, reverse), 67)
        self.assertEqual(self.recurrence.expected_size(13, forward), 90)


if __name__ == "__main__":
    unittest.main()
