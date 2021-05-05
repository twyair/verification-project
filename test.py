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

    def test_max(self):
        fns = main.get_functions("max")
        for f in [
            "array_max",
            "max2",
            "max2_float",
        ]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check().is_ok())
        self.assertFalse("max2_wrong")

    def test_sort(self):
        fns = main.get_functions("sort")
        for f in [
            "bubble_sort_sub",
            "insertion_sort",
            "bubble_sort",
        ]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check().is_ok())

    def test_bools(self):
        fns = main.get_functions("bools")
        for f in [
            "de_morgan",
            "first_true",
            "flip_even",
        ]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check().is_ok())
        self.assertFalse("de_morgan_bug")

    def test_random(self):
        fns = main.get_functions("random")
        for f in [
            "is_prime",
            "array_reverse",
            "vector_add",
            "sqrt_v1",
            "partition",
            "mccarthy_91",
        ]:
            with self.subTest(f"test_{f} failed\n"):
                self.assertTrue(fns[f].check().is_ok())


if __name__ == "__main__":
    unittest.main()
