# Python Monitoring Demo

This project demonstrates how to setup a simple python webapp with monitoring using Prometheus and Grafana.

## To run

Have docker installed and setup.

* `docker-compose up` runs the app, prometheus and grafana in that order.
* Run `pinger.py` script in a separate terminal which issues random requests to working and erroneous endpoints in the webapp to build up metric data.

### Notes

* The default username for Grafana is `admin`, with the password set as an env variable in the compose file.
* For persistent storage, you use the `/monitoring/vols/prom` and `/monitoring/vols/graf` by mounting them as volumes for the app in the compose file.
