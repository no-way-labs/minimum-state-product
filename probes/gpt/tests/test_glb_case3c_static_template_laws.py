import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
CATALOGUE_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_template_catalogue.py"
)
STATIC_LAWS_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_static_template_laws.py"
)


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class StaticTemplateLawTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.catalogue = load_module("glb_case3c_template_catalogue_static_test", CATALOGUE_PY)
        cls.static_laws = load_module("glb_case3c_static_template_laws_test", STATIC_LAWS_PY)

    def test_static_counts_match_observed_template_catalogue(self) -> None:
        for template_id, template in self.catalogue.TEMPLATES.items():
            law = self.static_laws.TEMPLATE_LAWS[template_id]
            self.assertEqual(len(law.losses), template.loss_count)
            self.assertEqual(len(law.gains), template.gain_count)
            self.assertEqual(law.size_slope, template.size_slope)

    def test_case_dispatch_uses_static_template_law(self) -> None:
        law = self.static_laws.law_for_case("local_11k", "reverse", True)
        self.assertEqual(law.template_id, "reverse_upper_light")

        law = self.static_laws.law_for_case("semi_symmetric_2plus", "forward", False)
        self.assertEqual(law.template_id, "forward_base_uniform")

        law = self.static_laws.law_for_case("reverse_upper_trailing2", "reverse", True)
        self.assertEqual(law.template_id, "reverse_upper_trailing2")


if __name__ == "__main__":
    unittest.main()
