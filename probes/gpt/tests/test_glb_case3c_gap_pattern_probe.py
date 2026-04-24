import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
PROBE_PY = (
    REPO_ROOT / "probes" / "gpt"
    / "glb_case3c_gap_pattern_probe.py"
)


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class GapPatternProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.probe = load_module("glb_case3c_gap_pattern_probe_test", PROBE_PY)

    def test_state_counts_from_gaps_builds_normalized_case3c_family(self) -> None:
        self.assertEqual(
            self.probe.state_counts_from_gaps((1, 2, 3)),
            (2, 3, 2, 3, 3, 2, 3, 3, 4),
        )
        self.assertEqual(
            self.probe.state_counts_from_gaps((2, 2, 2)),
            (2, 3, 3, 2, 3, 3, 2, 3, 4),
        )

    def test_true_case3c_gap_patterns_matches_known_catalogues(self) -> None:
        self.assertEqual(
            self.probe.true_case3c_gap_patterns(9),
            ((1, 1, 4), (1, 2, 3), (1, 3, 2), (2, 2, 2)),
        )
        self.assertEqual(
            self.probe.true_case3c_gap_patterns(10),
            ((1, 1, 5), (1, 2, 4), (1, 3, 3), (1, 4, 2), (2, 2, 3)),
        )

    def test_family_spec_matches_representative_edges(self) -> None:
        state_counts = self.probe.state_counts_from_gaps((1, 2, 3))

        self.assertEqual(
            self.probe.family_spec_from_state_counts(state_counts, "reverse", False),
            ((1, 4), (0, 8)),
        )
        self.assertEqual(
            self.probe.family_spec_from_state_counts(state_counts, "forward", False),
            ((2, 5), (0, 1)),
        )
        self.assertEqual(
            self.probe.family_spec_from_state_counts(state_counts, "reverse", True),
            ((1, 4, 7), (0, 8)),
        )
        self.assertEqual(
            self.probe.family_spec_from_state_counts(state_counts, "forward", True),
            ((2, 5, 7), (0, 1)),
        )

    def test_exact_signature_groups_identical_gap_regimes(self) -> None:
        representative_result = {
            "actual_bottom_slot_counter": {
                (0, "seed_unsat"): 3,
                (1, "completion_unsat"): 3,
                (2, "completion_unsat"): 3,
            },
            "summary": {
                ("completion_unsat", 33): 6,
                ("seed_unsat", None): 3,
            },
            "mismatches": [],
        }
        shifted_result = {
            "actual_bottom_slot_counter": {
                (0, "seed_unsat"): 3,
                (1, "completion_unsat"): 3,
                (2, "completion_unsat"): 3,
            },
            "summary": {
                ("completion_unsat", 33): 6,
                ("seed_unsat", None): 3,
            },
            "mismatches": [],
        }
        local_result = {
            "actual_bottom_slot_counter": {
                (0, "seed_unsat"): 3,
                (1, "completion_unsat"): 1,
                (1, "seed_unsat"): 2,
                (2, "completion_unsat"): 1,
                (2, "seed_unsat"): 2,
            },
            "summary": {
                ("completion_unsat", 33): 1,
                ("completion_unsat", 8): 1,
                ("seed_unsat", None): 7,
            },
            "mismatches": [((1, 0), "completion_unsat", "seed_unsat", None)],
        }

        rows = [
            {
                "gaps": (1, 2, 3),
                "family": "reverse_base",
                "predicted_match": True,
                "slot_status_signature": self.probe.slot_status_signature(representative_result),
                "summary_signature": self.probe.summary_signature(representative_result),
                "exact_signature": self.probe.exact_signature(representative_result),
                "result": representative_result,
            },
            {
                "gaps": (1, 3, 2),
                "family": "reverse_base",
                "predicted_match": True,
                "slot_status_signature": self.probe.slot_status_signature(shifted_result),
                "summary_signature": self.probe.summary_signature(shifted_result),
                "exact_signature": self.probe.exact_signature(shifted_result),
                "result": shifted_result,
            },
            {
                "gaps": (1, 1, 4),
                "family": "reverse_base",
                "predicted_match": False,
                "slot_status_signature": self.probe.slot_status_signature(local_result),
                "summary_signature": self.probe.summary_signature(local_result),
                "exact_signature": self.probe.exact_signature(local_result),
                "result": local_result,
            },
        ]

        clusters = self.probe.cluster_taxonomy(rows)
        self.assertEqual(len(clusters["reverse_base"]), 2)
        self.assertEqual(clusters["reverse_base"][0]["gaps_list"], [(1, 1, 4)])
        self.assertEqual(clusters["reverse_base"][0]["predicted_match"], False)
        self.assertEqual(clusters["reverse_base"][1]["gaps_list"], [(1, 2, 3), (1, 3, 2)])
        self.assertEqual(clusters["reverse_base"][1]["predicted_match"], True)

    def test_symbolic_regime_label_matches_observed_families(self) -> None:
        self.assertEqual(
            self.probe.symbolic_regime_label((1, 1, 4), "reverse", False),
            "local_11k",
        )
        self.assertEqual(
            self.probe.symbolic_regime_label((1, 2, 3), "forward", False),
            "asymmetric_1ab",
        )
        self.assertEqual(
            self.probe.symbolic_regime_label((2, 2, 2), "forward", True),
            "semi_symmetric_2plus",
        )
        self.assertEqual(
            self.probe.symbolic_regime_label((1, 3, 2), "reverse", True),
            "reverse_upper_trailing2",
        )
        self.assertEqual(
            self.probe.symbolic_regime_label((1, 4, 3), "reverse", True),
            "asymmetric_1ab",
        )

    def test_symbolic_comparison_matches_sample_exact_partition(self) -> None:
        exact_rows = [
            {
                "gaps": (1, 1, 6),
                "family": "forward_upper",
                "exact_signature": ("local",),
            },
            {
                "gaps": (1, 2, 5),
                "family": "forward_upper",
                "exact_signature": ("asym",),
            },
            {
                "gaps": (1, 3, 4),
                "family": "forward_upper",
                "exact_signature": ("asym",),
            },
            {
                "gaps": (2, 2, 4),
                "family": "forward_upper",
                "exact_signature": ("semi",),
            },
            {
                "gaps": (2, 3, 3),
                "family": "forward_upper",
                "exact_signature": ("semi",),
            },
        ]
        comparison = self.probe.compare_symbolic_to_exact(
            exact_rows,
            ((1, 1, 6), (1, 2, 5), (1, 3, 4), (2, 2, 4), (2, 3, 3)),
            ("forward",),
            (True,),
        )
        self.assertTrue(comparison["forward_upper"]["match"])

    def test_symbolic_partition_matches_logged_n9_taxonomy(self) -> None:
        clusters = self.probe.cluster_symbolic(
            self.probe.symbolic_rows(
                self.probe.true_case3c_gap_patterns(9),
                ("reverse", "forward"),
                (False, True),
            )
        )
        self.assertEqual(
            self._cluster_gap_sets(clusters),
            {
                "forward_base": [
                    [(1, 1, 4)],
                    [(1, 2, 3), (1, 3, 2)],
                    [(2, 2, 2)],
                ],
                "forward_upper": [
                    [(1, 1, 4)],
                    [(1, 2, 3), (1, 3, 2)],
                    [(2, 2, 2)],
                ],
                "reverse_base": [
                    [(1, 1, 4)],
                    [(1, 2, 3), (1, 3, 2)],
                    [(2, 2, 2)],
                ],
                "reverse_upper": [
                    [(1, 1, 4)],
                    [(1, 2, 3)],
                    [(1, 3, 2)],
                    [(2, 2, 2)],
                ],
            },
        )

    def test_symbolic_partition_matches_logged_n10_taxonomy(self) -> None:
        clusters = self.probe.cluster_symbolic(
            self.probe.symbolic_rows(
                self.probe.true_case3c_gap_patterns(10),
                ("reverse", "forward"),
                (False, True),
            )
        )
        self.assertEqual(
            self._cluster_gap_sets(clusters),
            {
                "forward_base": [
                    [(1, 1, 5)],
                    [(1, 2, 4), (1, 3, 3), (1, 4, 2)],
                    [(2, 2, 3)],
                ],
                "forward_upper": [
                    [(1, 1, 5)],
                    [(1, 2, 4), (1, 3, 3), (1, 4, 2)],
                    [(2, 2, 3)],
                ],
                "reverse_base": [
                    [(1, 1, 5)],
                    [(1, 2, 4), (1, 3, 3), (1, 4, 2)],
                    [(2, 2, 3)],
                ],
                "reverse_upper": [
                    [(1, 1, 5)],
                    [(1, 2, 4), (1, 3, 3)],
                    [(1, 4, 2)],
                    [(2, 2, 3)],
                ],
            },
        )

    def test_symbolic_partition_matches_logged_n11_taxonomy(self) -> None:
        clusters = self.probe.cluster_symbolic(
            self.probe.symbolic_rows(
                self.probe.true_case3c_gap_patterns(11),
                ("reverse", "forward"),
                (False, True),
            )
        )
        self.assertEqual(
            self._cluster_gap_sets(clusters),
            {
                "forward_base": [
                    [(1, 1, 6)],
                    [(1, 2, 5), (1, 3, 4), (1, 4, 3), (1, 5, 2)],
                    [(2, 2, 4), (2, 3, 3)],
                ],
                "forward_upper": [
                    [(1, 1, 6)],
                    [(1, 2, 5), (1, 3, 4), (1, 4, 3), (1, 5, 2)],
                    [(2, 2, 4), (2, 3, 3)],
                ],
                "reverse_base": [
                    [(1, 1, 6)],
                    [(1, 2, 5), (1, 3, 4), (1, 4, 3), (1, 5, 2)],
                    [(2, 2, 4), (2, 3, 3)],
                ],
                "reverse_upper": [
                    [(1, 1, 6)],
                    [(1, 2, 5), (1, 3, 4), (1, 4, 3)],
                    [(1, 5, 2)],
                    [(2, 2, 4), (2, 3, 3)],
                ],
            },
        )

    def _cluster_gap_sets(
        self,
        clusters: dict[str, list[dict[str, object]]],
    ) -> dict[str, list[list[tuple[int, int, int]]]]:
        return {
            family: sorted(
                [sorted(cluster["gaps_list"]) for cluster in family_clusters],
                key=lambda gap_list: gap_list,
            )
            for family, family_clusters in sorted(clusters.items())
        }


if __name__ == "__main__":
    unittest.main()
