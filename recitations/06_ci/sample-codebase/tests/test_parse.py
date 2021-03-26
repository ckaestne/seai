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


if __name__ == '__main__':
    unittest.main()
