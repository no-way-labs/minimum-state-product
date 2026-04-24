import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
STATIC_BASE_ANCHORS_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_static_base_anchors.py"
)


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class StaticBaseAnchorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.anchors = load_module("glb_case3c_static_base_anchors_test", STATIC_BASE_ANCHORS_PY)

    def test_static_base_anchor_catalogue_has_all_six_base_cases(self) -> None:
        self.assertEqual(len(self.anchors.STATIC_BASE_ANCHORS), 6)
        self.assertEqual(
            self.anchors.anchor_for_case("asymmetric_1ab", "reverse", False).template_id,
            "reverse_base_light",
        )
        self.assertEqual(
            self.anchors.anchor_for_case("semi_symmetric_2plus", "forward", False).template_id,
            "forward_base_uniform",
        )

    def test_static_base_anchor_generation_matches_known_sizes(self) -> None:
        local_reverse = self.anchors.anchor_for_case("local_11k", "reverse", False)
        self.assertEqual(len(local_reverse.base_spine), 63)
        self.assertEqual(self.anchors.expected_size(11, local_reverse), 72)

        semi_forward = self.anchors.anchor_for_case("semi_symmetric_2plus", "forward", False)
        self.assertEqual(len(semi_forward.base_spine), 60)
        self.assertEqual(self.anchors.expected_size(12, semi_forward), 78)


if __name__ == "__main__":
    unittest.main()
