from flask import Flask

app = Flask('demo-flask-server')

@app.route('/')
def healthcheck():
    return 'Server UP!'

def main():
    app.run(host='0.0.0.0', port=8082, debug=False)

if __name__ == '__main__':
    main()