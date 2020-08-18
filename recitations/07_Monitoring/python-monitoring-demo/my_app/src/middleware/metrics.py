import time

from flask import request
from prometheus_client import Counter, Histogram

"""
* request_count
    The name of the metric you refer to it by
    
* App Request Count
    Description of what the metric indicates
    
* ['app_name', 'method', 'endpoint', 'http_status']
    The third argument is a list of labels associated with the metric.

    We can think of labels as metadata we attach to the metric,
    which are stored along with the value of the metric. 
     
    Here, we attach the application name 'app_name' so that our application is identifiable
    the HTTP method (method) of the current request, the endpoint (endpoint)
    for which the request was made, and the response status(http_status).
"""
REQUEST_COUNT = Counter(
    'request_count', 'App Request Count',
    ['app_name', 'method', 'endpoint', 'http_status']
)

REQUEST_LATENCY = Histogram('request_latency_seconds', 'Request latency',
                            ['app_name', 'endpoint'])


def start_timer():
    """
    - Attaches a starting timestamp for the incoming request
    """
    request.start_time = time.time()


def record_request_data(response):
    """
    - Updates the REQUEST_COUNT metric
    """
    REQUEST_COUNT.labels('webapp', request.method, request.path,
                         response.status_code).inc()
    return response


def stop_timer(response):
    """
    - Stops a timer for the request which was just processed.
    - Sets the latency as the difference between start and stop times
    - Returns the response to the user
    """
    resp_time = time.time() - request.start_time
    REQUEST_LATENCY.labels('webapp', request.path).observe(resp_time)
    return response


def setup_metrics(app):
    """
    - Attaches the middleware hooks to the flask apps
    """
    print('Setting up monitoring hooks for app...')

    # Pre request hooks
    app.before_request(start_timer)

    # Post request hooks
    app.after_request(record_request_data)
    app.after_request(stop_timer)
