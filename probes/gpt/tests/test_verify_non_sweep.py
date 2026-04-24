import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
VERIFY_NON_SWEEP_PY = REPO_ROOT / "src_comp_ver" / "verify_non_sweep.py"


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class VerifyNonSweepTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.oracle = load_module("verify_non_sweep_oracle", VERIFY_NON_SWEEP_PY)

    def test_clean_cycle_search_matches_known_examples(self) -> None:
        found = self.oracle.gec_conflict_scan.find_bn_clean_cycle(
            (2, 3, 3, 2, 3, 3, 2, 4),
            max_length=24,
            min_neighbors=0,
        )
        self.assertTrue(found.found)
        self.assertEqual(
            found.word,
            (0, 7, 6, 5, 4, 3, 2, 1, 0, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1, 0, 7, 0, 7),
        )

        not_found = self.oracle.gec_conflict_scan.find_bn_clean_cycle(
            (2, 3, 2, 3, 2, 3, 2, 3, 4),
            max_length=24,
            min_neighbors=0,
        )
        self.assertFalse(not_found.found)

    def test_case3a_n9_direct_counts_match_expected(self) -> None:
        summaries = self.oracle.verify_case3a_range(range(9, 10))
        actual = {
            (summary.n, summary.label): (
                summary.non_sweep_words,
                summary.valid_realizations,
                summary.conflicting_realizations,
                summary.passed,
            )
            for summary in summaries
        }
        self.assertEqual(actual[(9, "pure")], (9, 576, 576, True))
        self.assertEqual(actual[(9, "mixed")], (9, 864, 864, True))

    def test_wiggle_n9_and_n10_match_expected_symbolic_status(self) -> None:
        summaries = self.oracle.verify_wiggle_range(range(9, 11))
        actual = {summary.n: summary for summary in summaries}

        self.assertEqual(actual[9].diff_count, 2)
        self.assertEqual(actual[9].unexpected_diff_count, 0)
        self.assertTrue(actual[9].distinct_ok)
        self.assertTrue(actual[9].disjoint_ok)
        self.assertTrue(actual[9].passed)

        self.assertEqual(actual[10].diff_count, 0)
        self.assertEqual(actual[10].unexpected_diff_count, 0)
        self.assertTrue(actual[10].passed)

    def test_hybrid_scan_prefix_runs_without_clean_residue(self) -> None:
        summary = self.oracle.run_frontier_hybrid_scan(
            "multiset",
            max_length=20,
            limit=1,
            completion_timeout_ms=1000,
        )
        self.assertEqual(summary.orientation_count, 1)
        self.assertEqual(summary.clean_orientations, 0)
        self.assertEqual(summary.clean_cycles, 0)
        self.assertEqual(summary.completion_unknown, 0)
        self.assertEqual(summary.valid_systems, 0)

    def test_cli_runs_exact_checks(self) -> None:
        proc = subprocess.run(
            [
                sys.executable,
                str(VERIFY_NON_SWEEP_PY),
                "--from-n",
                "9",
                "--to-n",
                "9",
                "--frontier-clean-scan-mode",
                "multiset",
                "--frontier-clean-limit",
                "1",
                "--frontier-clean-max-len",
                "20",
                "--frontier-hybrid-mode",
                "multiset",
                "--frontier-hybrid-limit",
                "1",
                "--frontier-hybrid-max-len",
                "20",
                "--frontier-hybrid-completion-timeout-ms",
                "1000",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("CASE 3a fc=2 non-sweeps", proc.stdout)
        self.assertIn("Wiggle shadow symbolic checks", proc.stdout)
        self.assertIn("n=9 non-consecutive clean-cycle scan", proc.stdout)
        self.assertIn("n=9 non-consecutive hybrid completion scan", proc.stdout)
        self.assertIn("ALL EXACT NON-SWEEP CHECKS PASSED.", proc.stdout)


if __name__ == "__main__":
    unittest.main()
