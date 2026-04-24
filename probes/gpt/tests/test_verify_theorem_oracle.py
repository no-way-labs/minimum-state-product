import importlib.util
import math
import subprocess
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SRC_COMP_VER = REPO_ROOT / "src_comp_ver"
VERIFY_THEOREM_PY = SRC_COMP_VER / "verify_theorem.py"
VERIFY_STRUCTURAL_PY = SRC_COMP_VER / "verify_structural.py"

CUP2_EXPECTED = {
    4: {"product": 36, "cycle_length": 10, "good": 17, "bad": 19},
    5: {"product": 108, "cycle_length": 13, "good": 23, "bad": 85},
    6: {"product": 324, "cycle_length": 16, "good": 31, "bad": 293},
    7: {"product": 972, "cycle_length": 19, "good": 40, "bad": 932},
    8: {"product": 2916, "cycle_length": 22, "good": 50, "bad": 2866},
    9: {"product": 8748, "cycle_length": 25, "good": 61, "bad": 8687},
}

LOWER_BOUND_EXPECTED = {
    4: {"lower_bound": 2, "case1": 0, "case2": 1, "case3": 1, "sweep_total": 2, "sweep_blocked": 2},
    5: {"lower_bound": 6, "case1": 0, "case2": 4, "case3": 2, "sweep_total": 8, "sweep_blocked": 8},
    6: {"lower_bound": 27, "case1": 0, "case2": 13, "case3": 14, "sweep_total": 100, "sweep_blocked": 100},
    7: {"lower_bound": 118, "case1": 0, "case2": 56, "case3": 62, "sweep_total": 847, "sweep_blocked": 847},
    8: {"lower_bound": 575, "case1": 0, "case2": 274, "case3": 301, "sweep_total": 7893, "sweep_blocked": 7893},
    9: {"lower_bound": 3945, "case1": 0, "case2": 1749, "case3": 2196},
}


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class VerifyTheoremOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.oracle = load_module("verify_theorem_oracle", VERIFY_THEOREM_PY)
        cls.summary_counts_cache = {}
        cls.summary_full_cache = {}

    @classmethod
    def summary_for_n(cls, n: int, include_sweeps: bool):
        cache = cls.summary_full_cache if include_sweeps else cls.summary_counts_cache
        if n in cache:
            return cache[n]

        oracle = cls.oracle
        target = oracle.M_target(n)
        ms_cup, tables_cup = oracle.build_cup2(n)
        cup = oracle.verify_system(ms_cup, tables_cup)
        if not cup["valid"]:
            raise AssertionError(f"Oracle CUP-2 verification failed for n={n}: {cup}")

        vecs = oracle.enumerate_sub_threshold(n, target)
        case1 = case2 = case3 = 0
        sweep_total = sweep_blocked = 0

        for ms in vecs:
            case = oracle.classify(ms, n)
            if case == "case1":
                case1 += 1
            elif case == "case2":
                case2 += 1
            else:
                case3 += 1
                if include_sweeps:
                    st, sb = oracle.verify_sweeps(ms, n)
                    sweep_total += st
                    sweep_blocked += sb

        cache[n] = {
            "target": target,
            "cup2": {
                "product": cup["product"],
                "cycle_length": cup["cycle_length"],
                "good": cup["good"],
                "bad": cup["bad"],
            },
            "lower_bound": len(vecs),
            "case1": case1,
            "case2": case2,
            "case3": case3,
            "sweep_total": sweep_total,
            "sweep_blocked": sweep_blocked,
        }
        return cache[n]

    def test_target_function_has_expected_crossover(self) -> None:
        oracle = self.oracle
        self.assertEqual(oracle.M_target(4), 32)
        self.assertEqual(oracle.M_target(8), 2592)
        self.assertEqual(oracle.M_target(9), 8748)
        self.assertEqual(oracle.M_target(10), 26244)

    def test_structural_checker_script_succeeds(self) -> None:
        proc = subprocess.run(
            [sys.executable, str(VERIFY_STRUCTURAL_PY)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("ALL STRUCTURAL CHECKS PASSED.", proc.stdout)

    def test_cup2_reference_counts_through_n9(self) -> None:
        for n, expected in CUP2_EXPECTED.items():
            with self.subTest(n=n):
                summary = self.summary_for_n(n, include_sweeps=False)
                self.assertEqual(summary["target"], self.oracle.M_target(n))
                self.assertEqual(summary["cup2"], expected)

    def test_small_witnesses_are_valid_at_exact_targets(self) -> None:
        oracle = self.oracle
        for n, witness_builder in oracle.WITNESSES.items():
            with self.subTest(n=n):
                ms, tables = witness_builder()
                result = oracle.verify_system(ms, tables)
                self.assertTrue(result["valid"], result.get("reason"))
                self.assertEqual(math.prod(ms), oracle.M_target(n))

    def test_lower_bound_case_splits_match_known_exact_counts(self) -> None:
        for n, expected in LOWER_BOUND_EXPECTED.items():
            with self.subTest(n=n):
                summary = self.summary_for_n(n, include_sweeps=(n <= 8))
                self.assertEqual(summary["lower_bound"], expected["lower_bound"])
                self.assertEqual(summary["case1"], expected["case1"])
                self.assertEqual(summary["case2"], expected["case2"])
                self.assertEqual(summary["case3"], expected["case3"])
                if n <= 8:
                    self.assertEqual(summary["sweep_total"], expected["sweep_total"])
                    self.assertEqual(summary["sweep_blocked"], expected["sweep_blocked"])


if __name__ == "__main__":
    unittest.main()
