import unittest

from p2_ring import (
    RingSystem,
    build_dijkstra_solution_1,
    build_dijkstra_solution_3,
    materialize_rule,
    n5_easy_lower_bound,
    verify_system,
)
from scripts.p2_completion_search import has_fatal_forced_cycle_singletons
from scripts.p2_cycle_screen import forced_rule_map
from scripts.p2_good_cycle_search import enumerate_good_cycles, search_good_cycle
from scripts.p2_seeded_cycle_search import extract_unique_recurrent_cycle, solve_good_cycle_from_movers
from scripts.p2_smt_completion import solve_cycle_with_smt
from p2_witnesses import (
    build_n5_product_96_witness,
    build_n6_product_288_block_witness,
    build_n6_product_288_witness,
    build_n7_product_1152_witness,
    build_n7_product_864_witness,
)


class P2RingTests(unittest.TestCase):
    def test_dijkstra_solution_1_is_valid_at_threshold(self) -> None:
        result = verify_system(build_dijkstra_solution_1(n=3, m=3))
        self.assertTrue(result.valid, result.message)

    def test_dijkstra_solution_1_fails_for_five_binary_processors(self) -> None:
        result = verify_system(build_dijkstra_solution_1(n=5, m=2))
        self.assertFalse(result.valid)

    def test_dijkstra_solution_3_is_valid(self) -> None:
        result = verify_system(build_dijkstra_solution_3(n=4))
        self.assertTrue(result.valid, result.message)

    def test_dead_system_is_invalid(self) -> None:
        state_counts = (2, 2, 2)
        rules = tuple(
            materialize_rule(state_counts, i, lambda left, self_state, right: self_state)
            for i in range(3)
        )
        result = verify_system(RingSystem(state_counts=state_counts, rules=rules))
        self.assertFalse(result.valid)

    def test_n5_easy_lower_bound(self) -> None:
        self.assertEqual(n5_easy_lower_bound(), 72)

    def test_n5_product_96_witness_is_valid(self) -> None:
        system = build_n5_product_96_witness()
        self.assertEqual(system.size, 96)
        result = verify_system(system)
        self.assertTrue(result.valid, result.message)

    def test_n6_product_288_witness_is_valid(self) -> None:
        system = build_n6_product_288_witness()
        self.assertEqual(system.size, 288)
        result = verify_system(system)
        self.assertTrue(result.valid, result.message)

    def test_n6_product_288_block_witness_is_valid(self) -> None:
        system = build_n6_product_288_block_witness()
        self.assertEqual(system.size, 288)
        result = verify_system(system)
        self.assertTrue(result.valid, result.message)

    def test_n7_product_864_witness_is_valid(self) -> None:
        system = build_n7_product_864_witness()
        self.assertEqual(system.size, 864)
        result = verify_system(system)
        self.assertTrue(result.valid, result.message)

    def test_n7_product_1152_witness_is_valid(self) -> None:
        system = build_n7_product_1152_witness()
        self.assertEqual(system.size, 1152)
        result = verify_system(system)
        self.assertTrue(result.valid, result.message)

    def test_smt_completion_finds_n5_product_96_witness(self) -> None:
        state_counts = (2, 2, 2, 3, 4)
        survivor = None
        for cycle, movers in enumerate_good_cycles(state_counts, time_limit=10, max_cycles=200):
            cycle_set = frozenset(cycle)
            forced_map = forced_rule_map(cycle, movers)
            if has_fatal_forced_cycle_singletons(state_counts, cycle_set, forced_map):
                continue
            survivor = (cycle, movers)
            break
        self.assertIsNotNone(survivor)
        cycle, movers = survivor
        result = solve_cycle_with_smt(state_counts, cycle, movers, timeout_ms=10000)
        self.assertTrue(result.found, result.message)
        self.assertIsNotNone(result.system)

    def test_seeded_cycle_search_finds_cycle_for_n7_product_864_movers(self) -> None:
        system = build_n7_product_864_witness()
        _, movers = extract_unique_recurrent_cycle(system)
        result = solve_good_cycle_from_movers(system.state_counts, movers, timeout_ms=5000)
        self.assertTrue(result.found, result.message)
        self.assertIsNotNone(result.cycle)
        self.assertEqual(len(result.cycle), len(movers))

    def test_seeded_cycle_search_rejects_open_product_576_class_for_n7_product_864_movers(self) -> None:
        system = build_n7_product_864_witness()
        _, movers = extract_unique_recurrent_cycle(system)
        result = solve_good_cycle_from_movers((2, 2, 3, 2, 2, 3, 4), movers, timeout_ms=5000)
        self.assertFalse(result.found)

    def test_good_cycle_search_supports_mover_prefix(self) -> None:
        state_counts = (2, 2, 2, 3, 4)
        result = search_good_cycle(state_counts, time_limit=10)
        self.assertIsNotNone(result.cycle)
        self.assertIsNotNone(result.movers)
        prefix = result.movers[:3]
        prefixed = search_good_cycle(state_counts, time_limit=10, mover_prefix=prefix)
        self.assertIsNotNone(prefixed.cycle)
        self.assertIsNotNone(prefixed.movers)
        self.assertEqual(prefixed.movers[: len(prefix)], prefix)


if __name__ == "__main__":
    unittest.main()
