
from time import sleep
from json import dumps
from kafka import KafkaProducer

# Create a producer to write data to kafka
producer = KafkaProducer(bootstrap_servers=['localhost:9092'],
                        value_serializer=lambda x: dumps(x).encode('utf-8'))

# Write data via the producer
for e in range(10):
    data = {'number' : e}
    producer.send(topic='numtest-kartikri', value=data)
    sleep(1)