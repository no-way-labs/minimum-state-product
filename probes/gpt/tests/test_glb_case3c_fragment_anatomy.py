import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
ANATOMY_PY = REPO_ROOT / "probes" / "gpt" / "glb_case3c_fragment_anatomy.py"
STARPOWER_PY = REPO_ROOT / "probes" / "gpt" / "glb_case3c_starpower_probe.py"
ASSIGNMENT_SCAN_PY = REPO_ROOT / "probes" / "gpt" / "glb_three_sweep_assignment_scan.py"
COMPLETION_PY = REPO_ROOT / "probes" / "gpt" / "p2_completion_search.py"
SEEDED_PY = REPO_ROOT / "probes" / "gpt" / "p2_seeded_cycle_search.py"


def load_module(module_name: str, path: Path):
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


class FragmentAnatomyNormalizationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.anatomy = load_module("glb_case3c_fragment_anatomy_test", ANATOMY_PY)
        cls.starpower = load_module("glb_case3c_starpower_probe_test", STARPOWER_PY)
        cls.assignment_scan = load_module("glb_three_sweep_assignment_scan_test", ASSIGNMENT_SCAN_PY)
        cls.completion = load_module("p2_completion_search_test", COMPLETION_PY)
        cls.seeded = load_module("p2_seeded_cycle_search_test", SEEDED_PY)

    def test_cycle_normalization_quotients_local_state_relabeling(self) -> None:
        n = 9
        orientation = "forward"
        assignment = (0, 0)
        state_counts = self.starpower.representative_case3c_state_counts(n)
        interior_edges, tail = self.starpower.family_spec(n, orientation, False)
        word = self.assignment_scan.build_word(interior_edges, assignment, orientation, tail, n)

        cycle = self.seeded.solve_good_cycle_from_movers(state_counts, word, timeout_ms=1200).cycle
        self.assertIsNotNone(cycle)
        cycle = cycle
        _, _, domains = self.completion.build_initial_domains_from_cycle(state_counts, cycle, word)
        forced_map = {
            key: next(iter(domain))
            for key, domain in domains.items()
            if len(domain) == 1
        }

        permutations = []
        for state_count in state_counts:
            mapping = {state: state for state in range(state_count)}
            if state_count >= 3:
                mapping[1], mapping[2] = mapping[2], mapping[1]
            permutations.append(mapping)
        permutations = tuple(permutations)

        relabeled_cycle = self.anatomy.normalize_cycle(cycle, permutations)
        relabeled_forced_map = self._apply_permutation_to_forced_map(forced_map, permutations, n)

        canonical_original = self.anatomy.normalize_cycle(
            cycle,
            self.anatomy.cycle_first_appearance_permutations(cycle, state_counts),
        )
        canonical_relabeled = self.anatomy.normalize_cycle(
            relabeled_cycle,
            self.anatomy.cycle_first_appearance_permutations(relabeled_cycle, state_counts),
        )
        self.assertEqual(canonical_original, canonical_relabeled)

        normalized_original_forced = self.anatomy.normalize_forced_map(
            forced_map,
            self.anatomy.cycle_first_appearance_permutations(cycle, state_counts),
            n,
        )
        normalized_relabeled_forced = self.anatomy.normalize_forced_map(
            relabeled_forced_map,
            self.anatomy.cycle_first_appearance_permutations(relabeled_cycle, state_counts),
            n,
        )
        self.assertEqual(normalized_original_forced, normalized_relabeled_forced)

    @staticmethod
    def _apply_permutation_to_forced_map(
        forced_map: dict[tuple[int, tuple[int, int, int]], int],
        permutations: tuple[dict[int, int], ...],
        n: int,
    ) -> dict[tuple[int, tuple[int, int, int]], int]:
        return {
            (
                processor,
                (
                    permutations[(processor - 1) % n][ctx[0]],
                    permutations[processor][ctx[1]],
                    permutations[(processor + 1) % n][ctx[2]],
                ),
            ): permutations[processor][out_state]
            for (processor, ctx), out_state in forced_map.items()
        }


if __name__ == "__main__":
    unittest.main()
