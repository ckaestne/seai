import sys
from kafka import KafkaConsumer, TopicPartition


def create_consumer(topic):
# Create a consumer to read data from kafka
    consumer = KafkaConsumer(
        topic, #consumer from this topic
        bootstrap_servers=['localhost:9092'],
        group_id='test-group-example',
        # Read from the start of the topic; Default is latest
        auto_offset_reset='earliest'
    )
    consumer.subscribe([topic])
    return consumer


def get_data_from_kafka(consumer, topic):
    records = consumer.poll(timeout_ms=6000)
    consumer.seek(partition=TopicPartition(topic,0), offset=5)
    records = consumer.poll(timeout_ms=6000)
    return records


if __name__ == '__main__':
    #create consumer to read data from Kafka
    params = sys.argv[1:]
    topic = "test-tashee3" #str(params[0])

    consumer = create_consumer(topic)
    records = get_data_from_kafka(consumer, topic)

    #print messages
    for k, v in records.items():
        for record in v:
            print(record.value)  # byte string