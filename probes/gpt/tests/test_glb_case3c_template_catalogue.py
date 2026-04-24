import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
CATALOGUE_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_template_catalogue.py"
)


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class TemplateCatalogueTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.catalogue = load_module("glb_case3c_template_catalogue_test", CATALOGUE_PY)

    def test_case_template_mapping_matches_current_meta_catalogue(self) -> None:
        self.assertEqual(
            self.catalogue.template_for_case("local_11k", "reverse", False),
            "reverse_base_light",
        )
        self.assertEqual(
            self.catalogue.template_for_case("semi_symmetric_2plus", "forward", False),
            "forward_base_uniform",
        )
        self.assertEqual(
            self.catalogue.template_for_case("reverse_upper_trailing2", "reverse", True),
            "reverse_upper_trailing2",
        )
        self.assertEqual(
            self.catalogue.template_for_case("semi_symmetric_2plus", "forward", True),
            "forward_upper_semi",
        )

    def test_template_membership_compresses_catalogue(self) -> None:
        grouped = self.catalogue.cases_by_template()
        self.assertEqual(
            sorted(case.case_id for case in grouped["forward_base_uniform"]),
            [
                "asymmetric_1ab/forward_base",
                "local_11k/forward_base",
                "semi_symmetric_2plus/forward_base",
            ],
        )
        self.assertEqual(
            sorted(case.case_id for case in grouped["reverse_upper_light"]),
            [
                "asymmetric_1ab/reverse_upper",
                "local_11k/reverse_upper",
            ],
        )
        self.assertEqual(
            sorted(case.case_id for case in grouped["forward_upper_light"]),
            [
                "asymmetric_1ab/forward_upper",
                "local_11k/forward_upper",
            ],
        )

    def test_upper_meta_templates_capture_second_order_compression(self) -> None:
        self.assertEqual(
            self.catalogue.meta_template_for_case("local_11k", "reverse", True),
            "upper_light_oriented",
        )
        self.assertEqual(
            self.catalogue.meta_template_for_case("semi_symmetric_2plus", "forward", True),
            "upper_semi_oriented",
        )
        self.assertEqual(
            self.catalogue.meta_template_for_case("reverse_upper_trailing2", "reverse", True),
            "upper_exceptional_reverse",
        )

        grouped = self.catalogue.cases_by_meta_template()
        self.assertEqual(
            sorted(case.case_id for case in grouped["upper_light_oriented"]),
            [
                "asymmetric_1ab/forward_upper",
                "asymmetric_1ab/reverse_upper",
                "local_11k/forward_upper",
                "local_11k/reverse_upper",
            ],
        )
        self.assertEqual(
            sorted(case.case_id for case in grouped["upper_semi_oriented"]),
            [
                "semi_symmetric_2plus/forward_upper",
                "semi_symmetric_2plus/reverse_upper",
            ],
        )


if __name__ == "__main__":
    unittest.main()
