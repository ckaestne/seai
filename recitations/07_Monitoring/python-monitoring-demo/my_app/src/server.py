import prometheus_client
from flask import Flask, Response

from middleware.metrics import setup_metrics

app = Flask(__name__)
setup_metrics(app)


@app.route('/test/')
def test():
    """
    An endpoint which returns the string 'Hello world' on successfully being called
    :return:
    """
    return 'Hello world!'


@app.route('/test1/')
def test1():
    """
    A endpoint to simulate an error in server processing
    :return:
    """
    1 / 0
    return 'impossible'


@app.errorhandler(500)
def handle_500(error):
    """
    Flask error handler for internal server error
    """
    return str(error), 500


CONTENT_TYPE_LATEST = str('text/plain; version=0.0.4; charset=utf-8')


@app.route('/metrics/')
def metrics():
    """
    Endpoint to expose metrics for prometheus to pull
    """
    return Response(prometheus_client.generate_latest(), mimetype=CONTENT_TYPE_LATEST)


if __name__ == '__main__':
    app.run(host='0.0.0.0')
