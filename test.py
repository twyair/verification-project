import main
import unittest


class TestStringMethods(unittest.TestCase):
    def test_array(self):
        fns = main.get_functions("array")
        self.assertTrue(fns["max3_array"].check().is_sat())
        self.assertTrue(fns["max3_array_indirect"].check().is_sat())
        self.assertTrue(fns["sort3"].check().is_sat())

    def test_max3(self):
        fns = main.get_functions("max3")
        self.assertTrue(fns["max3_v1"].check().is_sat())
        self.assertTrue(fns["max3_v2"].check().is_sat())
        self.assertTrue(fns["max3_v3"].check().is_sat())

    def test_max(self):
        fns = main.get_functions("max")
        self.assertTrue(fns["array_max"].check().is_sat())
        self.assertTrue(fns["max2"].check().is_sat())
        self.assertFalse(fns["max2_wrong"].check().is_sat())

    def test_sort(self):
        fns = main.get_functions("sort")
        self.assertTrue(fns["bubble_sort_sub"].check().is_sat())
        self.assertTrue(fns["insertion_sort"].check().is_sat())
        self.assertTrue(fns["bubble_sort"].check().is_sat())


if __name__ == "__main__":
    unittest.main()
