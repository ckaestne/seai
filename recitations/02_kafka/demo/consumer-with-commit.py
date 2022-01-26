from kafka import KafkaConsumer
from json import loads

consumer = KafkaConsumer(
    'test-nidhi',
    bootstrap_servers=['localhost:9092'],
    auto_offset_reset='earliest',
    # Consumer group id
    group_id='test-group-nidhi',
    # Commit that an offset has been read
    enable_auto_commit=True,
    # How often to tell Kafka, an offset has been read
    auto_commit_interval_ms=1000
)

print('In consumer-with-commit.py')
# Prints messages once, then only new ones!
for message in consumer:
    print(loads(message.value))