import importlib.util
import math
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
PAPER_ROOT = REPO_ROOT
SRC_COMP_VER = PAPER_ROOT / "src_comp_ver"
VERIFY_FAST_C = SRC_COMP_VER / "verify_fast.c"
VERIFY_THEOREM_PY = SRC_COMP_VER / "verify_theorem.py"
VERIFY_STRUCTURAL_PY = SRC_COMP_VER / "verify_structural.py"


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class VerifyFastOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if shutil.which("cc") is None:
            raise unittest.SkipTest("`cc` is required to build verify_fast for oracle tests")

        cls.verify_theorem = load_module("verify_theorem_ref", VERIFY_THEOREM_PY)
        cls.tempdir = tempfile.TemporaryDirectory()
        cls.verify_fast_bin = Path(cls.tempdir.name) / "verify_fast"
        subprocess.run(
            ["cc", "-O3", "-pthread", "-o", str(cls.verify_fast_bin), str(VERIFY_FAST_C)],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )

        cls._verify_fast_sections = None
        cls._reference_full = {}
        cls._reference_counts = {}
        cls._sweep_cache = {}

    @classmethod
    def tearDownClass(cls) -> None:
        cls.tempdir.cleanup()

    @classmethod
    def run_verify_fast(cls, n_max: int):
        if cls._verify_fast_sections is not None and max(cls._verify_fast_sections) >= n_max:
            return cls._verify_fast_sections

        proc = subprocess.run(
            [str(cls.verify_fast_bin), str(n_max)],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        cls._verify_fast_sections = cls.parse_verify_fast_output(proc.stdout)
        return cls._verify_fast_sections

    @staticmethod
    def parse_verify_fast_output(output: str):
        section_re = re.compile(
            r"^n = (?P<n>\d+)   M_n = (?P<target>\d+)   CUP-2 product = (?P<cup2>\d+)\n"
            r"^=+\n"
            r"(?P<body>.*?)(?=^=+\n(?:n = |ALL CHECKS PASSED|SOME CHECKS FAILED)|\Z)",
            re.MULTILINE | re.DOTALL,
        )
        result = {}
        for match in section_re.finditer(output):
            n = int(match.group("n"))
            body = match.group("body")
            cup = re.search(
                r"CUP-2 VALID  product=(\d+)  cycle=(\d+)  good=(\d+)  bad=(\d+)",
                body,
            )
            lower = re.search(r"Lower bound: (\d+) sub-threshold rotation classes", body)
            case1 = re.search(r"Case 1 \(<=2 binary, arithmetic\): (\d+)", body)
            case2 = re.search(r"Case 2 \(4\+ consec binary, RFC\):  (\d+)", body)
            case3 = re.search(r"Case 3 \(3\+ binary, <=3 consec\):  (\d+)", body)
            sweep = re.search(r"Sweep cycles: (\d+)/(\d+) blocked", body)

            if not all([cup, lower, case1, case2, case3]):
                raise AssertionError(f"Could not parse verify_fast section for n={n}")

            result[n] = {
                "target": int(match.group("target")),
                "cup2_product": int(match.group("cup2")),
                "cup2": {
                    "product": int(cup.group(1)),
                    "cycle_length": int(cup.group(2)),
                    "good": int(cup.group(3)),
                    "bad": int(cup.group(4)),
                },
                "lower_bound": int(lower.group(1)),
                "case1": int(case1.group(1)),
                "case2": int(case2.group(1)),
                "case3": int(case3.group(1)),
                "sweep_blocked": int(sweep.group(1)) if sweep else 0,
                "sweep_total": int(sweep.group(2)) if sweep else 0,
            }
        return result

    @classmethod
    def reference_summary(cls, n: int, include_sweeps: bool):
        cache = cls._reference_full if include_sweeps else cls._reference_counts
        if n in cache:
            return cache[n]

        theorem = cls.verify_theorem
        target = theorem.M_target(n)
        ms_cup, tables_cup = theorem.build_cup2(n)
        cup = theorem.verify_system(ms_cup, tables_cup)
        if not cup["valid"]:
            raise AssertionError(f"Python reference CUP-2 verifier failed for n={n}: {cup}")

        vecs = theorem.enumerate_sub_threshold(n, target)
        c1 = c2 = c3 = 0
        sweep_total = sweep_blocked = 0

        for ms in vecs:
            case = theorem.classify(ms, n)
            if case == "case1":
                c1 += 1
            elif case == "case2":
                c2 += 1
            else:
                c3 += 1
                if include_sweeps:
                    key = (n, tuple(ms))
                    if key not in cls._sweep_cache:
                        cls._sweep_cache[key] = theorem.verify_sweeps(ms, n)
                    st, sb = cls._sweep_cache[key]
                    sweep_total += st
                    sweep_blocked += sb

        cache[n] = {
            "target": target,
            "cup2_product": math.prod(ms_cup),
            "cup2": {
                "product": cup["product"],
                "cycle_length": cup["cycle_length"],
                "good": cup["good"],
                "bad": cup["bad"],
            },
            "lower_bound": len(vecs),
            "case1": c1,
            "case2": c2,
            "case3": c3,
            "sweep_total": sweep_total,
            "sweep_blocked": sweep_blocked,
        }
        return cache[n]

    @classmethod
    def canonical_sweep_counts(cls, ms, n):
        theorem = cls.verify_theorem
        nb_vals = {p: 1 for p in range(n)}
        cycle = theorem.construct_sweep(ms, n, nb_vals)
        if cycle is None:
            return (0, 0)
        ok, det = theorem.check_consistency(cycle, n)
        if not ok:
            return (0, 0)
        total = 1
        for p, m in enumerate(ms):
            if m > 2:
                total *= (m - 1)
        kernel_size = theorem.forced_kernel_size(det, set(cycle), ms, n)
        return (total, total if kernel_size > 0 else 0)

    def test_structural_verifier_passes(self) -> None:
        proc = subprocess.run(
            [sys.executable, str(VERIFY_STRUCTURAL_PY)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("ALL STRUCTURAL CHECKS PASSED.", proc.stdout)

    def test_c_matches_python_reference_through_n8(self) -> None:
        sections = self.run_verify_fast(10)
        for n in range(4, 9):
            with self.subTest(n=n):
                c_summary = sections[n]
                py_summary = self.reference_summary(n, include_sweeps=True)
                self.assertEqual(c_summary["target"], py_summary["target"])
                self.assertEqual(c_summary["cup2_product"], py_summary["cup2_product"])
                self.assertEqual(c_summary["cup2"], py_summary["cup2"])
                self.assertEqual(c_summary["lower_bound"], py_summary["lower_bound"])
                self.assertEqual(c_summary["case1"], py_summary["case1"])
                self.assertEqual(c_summary["case2"], py_summary["case2"])
                self.assertEqual(c_summary["case3"], py_summary["case3"])
                self.assertEqual(c_summary["sweep_total"], py_summary["sweep_total"])
                self.assertEqual(c_summary["sweep_blocked"], py_summary["sweep_blocked"])

    def test_c_matches_reference_counts_through_n10(self) -> None:
        sections = self.run_verify_fast(10)
        for n in (9, 10):
            with self.subTest(n=n):
                c_summary = sections[n]
                py_summary = self.reference_summary(n, include_sweeps=False)
                self.assertEqual(c_summary["target"], py_summary["target"])
                self.assertEqual(c_summary["cup2_product"], py_summary["cup2_product"])
                self.assertEqual(c_summary["cup2"], py_summary["cup2"])
                self.assertEqual(c_summary["lower_bound"], py_summary["lower_bound"])
                self.assertEqual(c_summary["case1"], py_summary["case1"])
                self.assertEqual(c_summary["case2"], py_summary["case2"])
                self.assertEqual(c_summary["case3"], py_summary["case3"])

    def test_canonical_sweep_reduction_matches_exhaustive_reference_through_n8(self) -> None:
        theorem = self.verify_theorem
        for n in range(4, 9):
            target = theorem.M_target(n)
            for ms in theorem.enumerate_sub_threshold(n, target):
                case = theorem.classify(ms, n)
                if not case.startswith("case3"):
                    continue
                with self.subTest(n=n, ms=tuple(ms)):
                    key = (n, tuple(ms))
                    if key not in self._sweep_cache:
                        self._sweep_cache[key] = theorem.verify_sweeps(ms, n)
                    exhaustive = self._sweep_cache[key]
                    canonical = self.canonical_sweep_counts(ms, n)
                    self.assertEqual(canonical, exhaustive)


if __name__ == "__main__":
    unittest.main()
