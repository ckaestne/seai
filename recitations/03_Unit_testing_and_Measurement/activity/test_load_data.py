import unittest
from unittest import mock
from load_data import create_consumer, get_data_from_kafka


class TestLoadData(unittest.TestCase):

    # Arrange, Act, Assert

    @mock.patch('load_data.KafkaConsumer', autospec=True)  # Act
    def test_get_kafka_consumer(self, kafka_consumer_mock):
        kafka_consumer_instance = create_consumer('test-tashee3')  # Arrange

        kafka_consumer_mock.assert_called_once_with(  # assert
            'test-tashee3',
            bootstrap_servers=['localhost:9092'],
            group_id='test-group-example',
            auto_offset_reset='earliest'
        )
        #assert(kafka_consumer_instance is  None)

    #Test Case II
    def test_get_data_from_kafka(self):
        kafka_consumer_instance = create_consumer('test-tashee3')
        kafka_data = get_data_from_kafka(kafka_consumer_instance, 'test-tashee3')
        assert (kafka_data is not None)


if __name__ == '__main__':
    unittest.main()