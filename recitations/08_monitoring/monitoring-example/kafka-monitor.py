from kafka import KafkaConsumer
from prometheus_client import Counter, Histogram, start_http_server

start_http_server(8765)

REQUEST_COUNT = Counter(
    'request_count', 'Recommendation Request Count',
    ['http_status']
)

REQUEST_LATENCY = Histogram('request_latency_seconds', 'Request latency')


def main():
    consumer = KafkaConsumer(
        'movielog3',
        bootstrap_servers='localhost:9092',
        auto_offset_reset='earliest',
        group_id='movielog3-monitor',
        enable_auto_commit=True,
        auto_commit_interval_ms=1000
    )

    for message in consumer:
        event = message.value.decode('utf-8')
        values = event.split(',')

        if 'recommendation request' in values[2]:
            status = values[3].strip().split(" ")[1]
            REQUEST_COUNT.labels(status).inc()

            time_taken = float(values[-1].strip().split(" ")[0])
            REQUEST_LATENCY.observe(time_taken / 1000)


if __name__ == "__main__":
    main()
