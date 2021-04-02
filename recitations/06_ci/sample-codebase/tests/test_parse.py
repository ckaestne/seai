import unittest

from app.parse import parse, Person


class TestParse(unittest.TestCase):
    def test_valid_csv(self):
        # Valid CSV Example
        valid_csv = '1,John Smith,Pittsburgh,PA,15224,42'

        p = parse(valid_csv)

        self.assertEqual(1, p.id)
        self.assertEqual('John Smith', p.name)
        self.assertEqual('Pittsburgh', p.city)
        self.assertEqual('PA', p.state)
        self.assertEqual(15224, p.zip_code)
        self.assertEqual(42, p.age)

    def test_invalid_number_of_cols(self):
        csv_input = '1,extra_col,John Smith,Pittsburgh,PA,15224,42'

        p = parse(csv_input)
        self.assertIsNone(p)

    def test_invalid_zip_code(self):
        csv_input = '1,John Smith,Pittsburgh,PA,15224-15232,42'

        p = parse(csv_input)
        self.assertIsNone(p, 'Zip code range should be rejected')


if __name__ == '__main__':
    unittest.main()
