from kafka import KafkaConsumer
from json import loads

consumer = KafkaConsumer(
    'numtest-kartikri',
    bootstrap_servers=['localhost:9092'],
    auto_offset_reset='earliest',
    # Consumer group id
    group_id='numtest-group-kartikri',
    # Commit that an offset has been read
    enable_auto_commit=True,
    # How often to tell Kafka, an offset has been read
    auto_commit_interval_ms=1000
)

# Prints messages once, then only new ones!
for message in consumer:
    print(loads(message.value))