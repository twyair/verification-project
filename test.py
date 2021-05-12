import unittest

import main


class VerifierTests(unittest.TestCase):
    def test_array(self):
        fns = main.get_functions("array")
        for f in [
            "max3_array",
            "max3_array_indirect",
            "sort3",
        ]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check().is_ok())

    def test_max3(self):
        fns = main.get_functions("max3")
        for f in [
            "max3_v1",
            "max3_v2",
            "max3_v3",
        ]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check().is_ok())

    def test_random(self):
        fns = main.get_functions("random")
        for f in [
            "is_prime",
            "array_reverse",
            "vector_add",
            "sqrt_v1",
            "partition",
            "mccarthy_91",
            "de_morgan",
            "first_true",
            "flip_even",
            "array_max",
            "max2",
            "max2_float",
            "bubble_sort",
            "merge",
            "binary_search",
        ]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check().is_ok())
        for f in ["max2_bug", "de_morgan_bug"]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertFalse(fns[f].check().is_ok())

    def test_iterative_check(self):
        fns = main.get_functions("random")
        for f in ["insertion_sort", "sqrt_v2", "sqrt_v3"]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check_iter().is_ok())


if __name__ == "__main__":
    unittest.main()
