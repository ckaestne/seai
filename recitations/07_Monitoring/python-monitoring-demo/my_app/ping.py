# usr/bin/python

"""
Script to randomly make requests to our webapp endpoints
"""

import random
import time

import requests

TEST_URL = 'http://localhost:5000/test/'
ERROR_URL = 'http://localhost:5000/test1/'

while True:
    a = random.randint(0, 1)
    if a == 0:
        print('Sending request to test url...')
        requests.get(TEST_URL)
    else:
        print('Sending request to error url...')
        requests.get(ERROR_URL)
    print('Done! Continuing...')
    time.sleep(1)
