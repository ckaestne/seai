package main

import (
	"encoding/json"
	"fmt"
	"github.com/gorilla/mux"
	"io/ioutil"
	"math/rand"
	"net/http"
	"os"
)

type LBConfig struct {
	EndpointA   string  `json:"endpoint_a"`
	EndpointB   string  `json:"endpoint_b"`
	Probability float32 `json:"probability"`
}

var cfg LBConfig

func main() {
	cfgFile, err := ioutil.ReadFile("./config.json")
	if err != nil {
		fmt.Print(err)
		os.Exit(1)
	}

	err = json.Unmarshal(cfgFile, &cfg)
	if err != nil {
		fmt.Print(err)
		os.Exit(1)
	}

	r := mux.NewRouter()
	r.HandleFunc("/", serviceHealthCheck).Methods("GET")
	r.HandleFunc("/recommend/{userId}", recommend).Methods("GET")

	_ = http.ListenAndServe(":8082", r)
}

func serviceHealthCheck(w http.ResponseWriter, r *http.Request) {
	healthCheckA, healthCheckB := "Endpoint A is UP!", "Endpoint B is UP!"

	res, err := http.Get(cfg.EndpointA + r.RequestURI)
	if err != nil || res == nil {
		healthCheckA = "Endpoint A is DOWN!"
	} else {
		hca, err := ioutil.ReadAll(res.Body)
		if err != nil || "Server is UP!" != string(hca) {
			healthCheckA = "Endpoint A is DOWN!"
		}
		_ = res.Body.Close()
	}

	res, err = http.Get(cfg.EndpointB + "/")
	if err != nil || res == nil {
		healthCheckB = "Endpoint B is DOWN!"
	} else {
		hcb, err := ioutil.ReadAll(res.Body)
		if err != nil || "Server is UP!" != string(hcb) {
			healthCheckB = "Endpoint B is DOWN!"
		}
		_ = res.Body.Close()
	}

	_, _ = fmt.Fprintf(w, healthCheckA+"\n"+healthCheckB)
}

func recommend(w http.ResponseWriter, r *http.Request) {
	var endpoint string
	if rand.Float32() < cfg.Probability {
		endpoint = cfg.EndpointA
	} else {
		endpoint = cfg.EndpointB
	}

	res, err := http.Get(endpoint + r.RequestURI)

	if err != nil {
		http.Error(w, err.Error(), 500)
	} else if res == nil {
		http.Error(w, "Null result", 500)
	} else if res.StatusCode == 406 {
		http.Error(w, "Invalid userid", 406)
	} else {
		recommendations, err := ioutil.ReadAll(res.Body)
		if err != nil {
			http.Error(w, err.Error(), 500)
		}
		_, err = w.Write(recommendations)
		if err != nil {
			http.Error(w, err.Error(), 500)
		}
	}
}
