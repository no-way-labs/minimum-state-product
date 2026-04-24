import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
PROBE_PY = REPO_ROOT / "probes" / "gpt" / "glb_case3c_forced_spine_probe.py"


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class ForcedSpineProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.probe = load_module("glb_case3c_forced_spine_probe_test", PROBE_PY)

    def test_base_family_probe_matches_n9_exact_anchors_with_lexmin_selector(self) -> None:
        reverse = self.probe.probe_summary(9, "reverse", False, 1200)
        forward = self.probe.probe_summary(9, "forward", False, 1200)

        self.assertEqual(reverse["predicted_completion_assignments"], 6)
        self.assertEqual(reverse["solved_cycles"], 6)
        self.assertEqual(reverse["cycle_selector"], "lexmin")
        self.assertEqual(reverse["normalized_forced_common_spine_size"], 43)

        self.assertEqual(forward["predicted_completion_assignments"], 3)
        self.assertEqual(forward["solved_cycles"], 3)
        self.assertEqual(forward["cycle_selector"], "lexmin")
        self.assertEqual(forward["normalized_forced_common_spine_size"], 72)

    def test_gap_probe_matches_representative_family_for_123_pattern(self) -> None:
        from_gaps = self.probe.probe_summary_for_gaps((1, 2, 3), "reverse", False, 1200)
        from_n = self.probe.probe_summary(9, "reverse", False, 1200)

        self.assertEqual(from_gaps["state_counts"], from_n["state_counts"])
        self.assertEqual(from_gaps["interior_edges"], from_n["interior_edges"])
        self.assertEqual(from_gaps["tail"], from_n["tail"])
        self.assertEqual(
            from_gaps["normalized_common_spine_rules"],
            from_n["normalized_common_spine_rules"],
        )

    def test_actual_completion_mode_restricts_local_branch_assignments(self) -> None:
        predicted = self.probe.probe_summary_for_gaps(
            (1, 1, 5),
            "reverse",
            False,
            1200,
            "lexmin",
            "predicted_completion",
        )
        actual = self.probe.probe_summary_for_gaps(
            (1, 1, 5),
            "reverse",
            False,
            1200,
            "lexmin",
            "actual_completion",
        )

        self.assertEqual(predicted["missing_cycles"], 4)
        self.assertEqual(predicted["selected_assignment_count"], 6)
        self.assertEqual(actual["missing_cycles"], 0)
        self.assertEqual(actual["selected_assignment_count"], 2)
        self.assertEqual(actual["selected_assignments"], [(1, 1), (2, 2)])


if __name__ == "__main__":
    unittest.main()
