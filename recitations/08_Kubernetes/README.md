## Kubernetes Setup

## Installation

* Install your Hypervision
  * `sudo apt-get install virtualbox`

* Install Kubectl
  * `wget https://storage.googleapis.com/kubernetes-release/release/v1.4.4/bin/linux/amd64/kubectl`
  * `chmod +x kubectl`
  * `sudo mv kubectl /usr/local/bin/kubectl`

* Install Minikube
  * `curl -Lo minikube https://storage.googleapis.com/minikube/releases/latest/minikube-linux-amd64 \
  && chmod +x minikube && sudo mv minikube /usr/local/bin/`

* Start Minikube
  * `minikube start`

* List of useful kubectl commands
  * `kubectl get pods`
  * `kubectl describe pod <pod_name>`
  * `kubectl get deployments`
  * `kubectl get services`
  * `kubectl rollout restart deployment <deployment_name>`
