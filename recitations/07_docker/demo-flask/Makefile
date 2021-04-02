build-container:
	tag=$$(sed '1q;d' ./version); \
	docker build -t kartikri/demo-flask-server:$$tag -t kartikri/demo-flask-server:latest .