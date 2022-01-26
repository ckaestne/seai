from kafka import KafkaConsumer
from json import loads

# Create a consumer to read data from kafka
consumer = KafkaConsumer(
    'test-nidhi',
    bootstrap_servers=['localhost:9092'],
    # Read from the start of the topic; Default is latest
    auto_offset_reset='earliest'
)

print('In consumer.py')
# Prints all messages, again and again!
for message in consumer:
    # Default message.value type is bytes!
    print(loads(message.value))