import time
import random
import requests

TEST_URL = 'http://localhost:5000/test/'
ERROR_URL = 'http://localhost:5000/test1/'

while True:
    num = random.randint(0, 1)
    if num == 0:
        print('Calling ', TEST_URL)
        requests.get(TEST_URL)
    else:
        print('Calling ', ERROR_URL)
        requests.get(ERROR_URL)

    time.sleep(2)
