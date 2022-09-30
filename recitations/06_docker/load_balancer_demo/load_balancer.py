import sys
import os
from flask import jsonify
from flask import Flask
import pickle
import json
from flask import request, make_response
import requests
import numpy as np
import random

app = Flask('load-balancer-server')

probability = 0.7

def checkHealth(ip_addr):
    return os.system('nc -vz '+ip_addr) == 0

@app.route('/')
def welcome():
    # add health check
    A_server_up = checkHealth('0.0.0.0 7004')
    B_server_up = checkHealth('0.0.0.0 7005')

    if not B_server_up and A_server_up:
        response = requests.get('http://0.0.0.0:7004/')
    elif B_server_up and not A_server_up:
        response = requests.get('http://0.0.0.0:7005/')
    elif A_server_up and B_server_up:
        if random.uniform(0, 1) < probability:
            response = requests.get('http://0.0.0.0:7004/')
        else:
            response = requests.get('http://0.0.0.0:7005/')
    else:
        response = ''
    return str(response)

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=8082, debug=False)
    welcome()