import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SNAPSHOT_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_anchor_snapshot.py"
)


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class AnchorSnapshotTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.snapshot = load_module("glb_case3c_anchor_snapshot_test", SNAPSHOT_PY)

    def test_iter_snapshot_cases_matches_catalogue(self) -> None:
        cases = self.snapshot.iter_snapshot_cases()
        self.assertEqual(len(cases), 13)
        self.assertIn("asymmetric_1ab/reverse_base", {case.case_id for case in cases})
        self.assertIn("reverse_upper_trailing2/reverse_upper", {case.case_id for case in cases})

    def test_select_cases_filters_case_id_and_family(self) -> None:
        selected = self.snapshot.select_cases(
            {"local_11k/reverse_upper"},
            set(),
            set(),
        )
        self.assertEqual([case.case_id for case in selected], ["local_11k/reverse_upper"])

        selected = self.snapshot.select_cases(
            set(),
            {"semi_symmetric_2plus"},
            {"forward_upper"},
        )
        self.assertEqual([case.case_id for case in selected], ["semi_symmetric_2plus/forward_upper"])


if __name__ == "__main__":
    unittest.main()
