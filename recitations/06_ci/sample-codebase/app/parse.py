class Person:
    def __init__(self):
        self.id = None
        self.name = None
        self.city = None
        self.state = None
        self.zip_code = None
        self.age = None


def parse(csv_input):
    values = csv_input.split(',')

    p = Person()
    p.id = parse_id(values)
    p.name = parse_name(values)
    p.city = parse_city(values)
    p.state = parse_state(values)
    p.zip_code = parse_zip_code(values)
    p.age = parse_age(values)

    return p


def parse_id(values):
    return int(values[0])


def parse_name(values):
    return str(values[1])


def parse_city(values):
    return str(values[2])


def parse_state(values):
    return str(values[3])


def parse_zip_code(values):
    return int(values[4])


def parse_age(values):
    return int(values[5])
