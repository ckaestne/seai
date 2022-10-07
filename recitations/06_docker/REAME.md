# Setup
[Install](https://docs.docker.com/get-docker/) and Start docker on your machine, either the docker application on Mac/Windows.
Install requirements
```
pip install -r requirements.py
```

# Running Docker 
```
cd docker_demo
docker-compose up
```
Now you can see the server up message on two different ports by two different containerised apps running simultaneously:
* http://localhost:7004
* http://localhost:7005

Press Ctrl+C to stop the containers
# Load Balancer
While the docker conatiners are running, do the following:
```
cd load_balancer
python3 load_balancer.py
```
Open:
http://localhost:8082 \
With 70% chance you will see Server A and with 30% Server B. This is an example of load balancing.
# Remove all Docker Images
```
docker system prune -a
```