FROM python:3.6-alpine

RUN mkdir /app

# Copy over and install requirements to create the base layer for this server
COPY requirements.txt /app

# Sets default directory to the /src folder in the image
WORKDIR /app

# Install requirements
RUN python3 -m pip install -r requirements.txt --no-cache-dir

# Copy over the rest of the service into the src directory
COPY . .

EXPOSE 5000

WORKDIR /app/src

CMD ["python", "server.py"]
