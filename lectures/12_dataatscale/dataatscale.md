---
author: Christian Kaestner
title: "17-445: Managing and Processing Large Datasets"
semester: Spring 2021
footer: "17-445 Machine Learning in Production, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---

# Managing and Processing Large Datasets

Christian Kaestner

<!-- references -->

Required watching: Molham Aref. [Business Systems with Machine Learning](https://www.youtube.com/watch?v=_bvrzYOA8dY). Guest lecture, 2020.

Suggested reading: Martin Kleppmann. [Designing Data-Intensive Applications](https://dataintensive.net/). OReilly. 2017. 

---

# Learning Goals

* Organize different data management solutions and their tradeoffs
* Understand the scalability challenges involved in large-scale machine learning and specifically deep learning
* Explain the tradeoffs between batch processing and stream processing and the lambda architecture
* Recommend and justify a design and corresponding technologies for a given system

---
# Case Study

![Google Photos Screenshot](gphotos.png)

Notes:
* Discuss possible architecture and when to predict (and update)
* in may 2017: 500M users, uploading 1.2billion photos per day (14k/sec)
* in Jun 2019 1 billion users


----

## "Zoom adding capacity"

<iframe src="https://giphy.com/embed/3oz8xtBx06mcZWoNJm" width="480" height="362" frameBorder="0" class="giphy-embed" allowFullScreen></iframe>

---

# Data Management and Processing in ML-Enabled Systems

----
# Kinds of Data

* Training data
* Input data
* Telemetry data
* (Models)

*all potentially with huge total volumes and high throughput*

*need strategies for storage and processing*


----
## Data Management and Processing in ML-Enabled Systems

* Store, clean, and update training data
* Learning process reads training data, writes model
* Prediction task (inference) on demand or precomputed
* Individual requests (low/high volume) or large datasets?
* 
* Often both learning and inference data heavy, high volume tasks


----
## Scaling Computations

<!-- colstart -->
Efficent Algorithms
<!-- col -->
Faster Machines
<!-- col -->
More Machines
<!-- colend -->

----
## Distributed X

* Distributed data cleaning
* Distributed feature extraction
* Distributed learning
* Distributed large prediction tasks
* Incremental predictions
* Distributed logging and telemetry




----
## Reliability and Scalability Challenges in AI-Enabled Systems?

<!-- discussion -->



----
## Distributed Systems and AI-Enabled Systems

* Learning tasks can take substantial resources
* Datasets too large to fit on single machine
* Nontrivial inference time, many many users
* Large amounts of telemetry
* Experimentation at scale
* Models in safety critical parts
* Mobile computing, edge computing, cyber-physical systems






---
# Excursion: Distributed Deep Learning with the Parameter Server Architecture

<!-- references -->
Li, Mu, et al. "[Scaling distributed machine learning with the parameter server](https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-li_mu.pdf)." OSDI, 2014.


----
## Recall: Backpropagation

![Multi Layer Perceptron](mlperceptron.svg)
<!-- .element: class="stretch" -->

----
## Training at Scale is Challenging

* 2012 at Google: 1TB-1PB of training data, $10^9-10^{12}$ parameters
* Need distributed training; learning is often a sequential problem
* Just exchanging model parameters requires substantial network bandwidth
* Fault tolerance essential (like batch processing), add/remove nodes
* Tradeoff between convergence rate and system efficiency

<!-- references -->
Li, Mu, et al. "[Scaling distributed machine learning with the parameter server](https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-li_mu.pdf)." OSDI, 2014.

----
## Distributed Gradient Descent

[![Parameter Server](parameterserver.png)](https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-li_mu.pdf)
<!-- .element: class="stretch" -->


----
## Parameter Server Architecture

[![Parameter Server](parameterserver2.png)](https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-li_mu.pdf)
<!-- .element: class="stretch" -->

Note:
Multiple parameter servers that each only contain a subset of the parameters, and multiple workers that each require only a subset of each

Ship only relevant subsets of mathematical vectors and matrices, batch communication

Resolve conflicts when multiple updates need to be integrated (sequential, eventually, bounded delay)

Run more than one learning algorithm simulaneously


----
## SysML Conference


Increasing interest in the systems aspects of machine learning

e.g., building large scale and robust learning infrastructure

https://mlsys.org/














---
# Data Storage Basics

* Relational vs document storage
* 1:n and n:m relations
* Storage and retrieval, indexes
* Query languages and optimization

----
## Relational Data Models

|user_id|Name|Email|dpt|
|-|-|-|-|
|1|Christian|kaestner@cs.|1|
|2|Eunsuk|eskang@cmu.|1|
|2|Tom|...|2|



|dpt_id|Name|Address|
|-|-|-|
|1|ISR|...|
|2|CSD|...|

```sql
select d.name from user u, dpt d where u.dpt=d.dpt_id
```

----

## Document Data Models

```js
{
    "id": 1,
    "name": "Christian",
    "email": "kaestner@cs.",
    "dpt": [
        {"name": "ISR", "address": "..."}
    ],
    "other": { ... }
}

```

```js
db.getCollection('users').find({"name": "Christian"})
```

----
## Log files, unstructured data

```
2020-06-25T13:44:14,601844,GET /data/m/goyas+ghosts+2006/17.mpg
2020-06-25T13:44:14,935791,GET /data/m/the+big+circus+1959/68.mpg
2020-06-25T13:44:14,557605,GET /data/m/elvis+meets+nixon+1997/17.mpg
2020-06-25T13:44:14,140291,GET /data/m/the+house+of+the+spirits+1993/53.mpg
2020-06-25T13:44:14,425781,GET /data/m/the+theory+of+everything+2014/29.mpg
2020-06-25T13:44:14,773178,GET /data/m/toy+story+2+1999/59.mpg
2020-06-25T13:44:14,901758,GET /data/m/ignition+2002/14.mpg
2020-06-25T13:44:14,911008,GET /data/m/toy+story+3+2010/46.mpg
```


----
## Tradeoffs

<!-- discussion -->

----
## Data Encoding

* Plain text (csv, logs)
* Semi-structured, schema-free (JSON, XML)
* Schema-based encoding (relational, Avro, ...)
* Compact encodings (protobuffer, ...)

---
# Distributed Data Storage

----
## Replication vs Partitioning

<!-- discussion -->

----
## Partitioning

Divide data:

* Horizontal partitioning: Different rows in different tables; e.g., movies by decade, hashing often used
* Vertical partitioning: Different columns in different tables; e.g., movie title vs. all actors

**Tradeoffs?**

```mermaid
graph TD
    Client --> Frontend
    Client2[Client] --> Frontend2[Frontend]
    Frontend --> Database1[Database West]
    Frontend --> Database2[Database East]
    Frontend --> Database3[Database Europe]
    Frontend2 --> Database1
    Frontend2 --> Database2
    Frontend2 --> Database3
```


----
## Replication Strategies: Leaders and Followers

```mermaid
graph TD
    Client --> Frontend
    Frontend --> Database
    Client2[Client] --> Frontend2[Frontend]
    Frontend2 --> Database[Primary Database]
    Database --> Database2[Backup DB 1]
    Database --> Database3[Backup DB 2]
    Database2 --> Database
    Database3 --> Database
```

----
## Replication Strategies: Leaders and Followers

* Write to leader
    * propagated synchronously or async.
* Read from any follower
* Elect new leader on leader outage; catchup on follower outage
*
* Built in model of many databases (MySQL, MongoDB, ...)

**Benefits and Drawbacks?**



----
## Multi-Leader Replication

* Scale write access, add redundancy
* Requires coordination among leaders
    * Resolution of write conflicts
* Offline leaders (e.g. apps), collaborative editing



----
## Leaderless Replication

* Client writes to all replica
* Read from multiple replica (quorum required)
    * Repair on reads, background repair process
* Versioning of entries (clock problem)
* e.g. Amazon Dynamo, Cassandra, Voldemort

```mermaid
graph TD
    Client --> Database
    Client --> Database2
    Client --> Database3
    Client2 --> Database
    Client2 --> Database2
    Client2 --> Database3
    Database ==> Client
    Database2 ==> Client
```

----
## Transactions

* Multiple operations conducted as one, all or nothing
* Avoids problems such as
  * dirty reads
  * dirty writes
* Various strategies, including locking and optimistic+rollback
* Overhead in distributed setting


---
# Data Processing (Overview)

* Services (online)
    * Responding to client requests as they come in
    * Evaluate: Response time
* Batch processing (offline)
    * Computations run on large amounts of data
    * Takes minutes to days
    * Typically scheduled periodically
    * Evaluate: Throughput
* Stream processing (near real time)
    * Processes input events, not responding to requests
    * Shortly after events are issued


---
# Batch Processing

----
## Large Jobs

* Analyzing TB of data, typically distributed storage
* Filtering, sorting, aggregating
* Producing reports, models, ...

```sh
cat /var/log/nginx/access.log |
    awk '{print $7}' |
    sort |
    uniq -c |
    sort -r -n |
    head -n 5
```

----
## Distributed Batch Processing

* Process data locally at storage
* Aggregate results as needed
* Separate pluming from job logic

*MapReduce* as common framework

![MapReduce](mapreduce.png)

<!-- references -->
Image Source: Ville Tuulos (CC BY-SA 3.0)

----
## MapReduce -- Functional Programming Style 

* Similar to shell commands: Immutable inputs, new outputs, avoid side effects
* Jobs can be repeated (e.g., on crashes)
* Easy rollback
* Multiple jobs in parallel (e.g., experimentation)

----
## Machine Learning and MapReduce

<!-- discussion -->

Notes: Useful for big learning jobs, but also for feature extraction

----
## Dataflow Engines (Spark, Tez, Flink, ...)

* Single job, rather than subjobs
* More flexible than just map and reduce
* Multiple stages with explicit dataflow between them
* Often in-memory data
* Pluming and distribution logic separated

----
## Key Design Principle: Data Locality

> Moving Computation is Cheaper than Moving Data -- [Hadoop Documentation](https://hadoop.apache.org/docs/stable/hadoop-project-dist/hadoop-hdfs/HdfsDesign.html#aMoving_Computation_is_Cheaper_than_Moving_Data)

* Data often large and distributed, code small
* Avoid transfering large amounts of data
* Perform computation where data is stored (distributed)
* Transfer only results as needed
* 
* "The map reduce way"



---
# Stream Processing

* Event-based systems, message passing style, publish subscribe

----
## Messaging Systems

* Multiple producers send messages to topic
* Multiple consumers can read messages
* Decoupling of producers and consumers
* Message buffering if producers faster than consumers
* Typically some persistency to recover from failures
* Messages removed after consumption or after timeout
* With or without central broker
* Various error handling strategies (acknowledgements, redelivery, ...)

----
## Common Designs

Like shell programs: Read from stream, produce output in other stream. Loose coupling


![](issueanalysis.svg)
<!-- .element: class="stretch" -->

----
## Stream Queries

* Processing one event at a time independently
* vs incremental analysis over all messages up to that point
* vs floating window analysis across recent messages
* Works well with probabilistic analyses

----
## Consumers

* Multiple consumers share topic for scaling and load balancing
* Multiple consumers read same message for different work
* Partitioning possible

----
## Design Questions

* Message loss important? (at-least-once processing)
* Can messages be processed repeatedly (at-most-once processing)
* Is the message order important?
* Are messages still needed after they are consumed?

----
## Stream Processing and AI-enabled Systems?

<!-- discussion -->

Notes: Process data as it arrives, prepare data for learning tasks,
use models to annotate data, analytics

----
## Event Sourcing

* Append only databases
* Record edit events, never mutate data
* Compute current state from all past events, can reconstruct old state
* For efficiency, take state snapshots
* Similar to traditional database logs

```text
createUser(id=5, name="Christian", dpt="SCS")
updateUser(id=5, dpt="ISR")
deleteUser(id=5)
```

----
## Benefits of Immutability (Event Sourcing)

* All history is stored, recoverable
* Versioning easy by storing id of latest record
* Can compute multiple views
* Compare *git*

*On a shopping website, a customer may add an item to their cart and then
remove it again. Although the second event cancels out the first event from the point
of view of order fulfillment, it may be useful to know for analytics purposes that the
customer was considering a particular item but then decided against it. Perhaps they
will choose to buy it in the future, or perhaps they found a substitute. This information is recorded in an event log, but would be lost in a database that deletes items
when they are removed from the cart.*

<!-- references -->

Source: Greg Young. [CQRS and Event Sourcing](https://www.youtube.com/watch?v=JHGkaShoyNs). Code on the Beach 2014 via Martin Kleppmann. Designing Data-Intensive Applications. OReilly. 2017.

----
## Drawbacks of Immutable Data

<!-- discussion -->

Notes: 
* Storage overhead, extra complexity of deriving state
* Frequent changes may create massive data overhead
* Some sensitive data may need to be deleted (e.g., privacy, security)


---
# The Lambda Architecture

![Lambda Architecture](lambda.png)

<!-- references -->
Source: [Textractor](https://commons.wikimedia.org/wiki/File:Diagram_of_Lambda_Architecture_(named_components).png) (CC BY-SA 4.0)

----
## Lambda Architecture: 3 Layer Storage Architecture


* Batch layer: best accuracy, all data, recompute periodically
* Speed layer: stream processing, incremental updates, possibly approximated
* Serving layer: provide results of batch and speed layers to clients
*
* Assumes append-only data
* Supports tasks with widely varying latency
* Balance latency, throughput and fault tolerance

----
## Lambda Architecture and Machine Learning

![Lambda Architecture](lambdaml.png)
<!-- .element: class="stretch" -->


* Learn accurate model in batch job
* Learn incremental model in stream processor

----
## Data Lake

* Trend to store all events in raw form (no consistent schema)
* May be useful later
* Data storage is comparably cheap

<!-- discussion -->

----
## Reasoning about Dataflows

Many data sources, many outputs, many copies

Which data is derived from what other data and how? 

Is it reproducible? Are old versions archived?

How do you get the right data to the right place in the right format?

**Plan and document data flows**

----
![](issueanalysis.svg)
<!-- .element: class="stretch" -->

----

[![Lots of data storage systems](etleverywhere.png)](https://youtu.be/_bvrzYOA8dY?t=1452)

<!-- reference -->
Molham Aref "[Business Systems with Machine Learning](https://www.youtube.com/watch?v=_bvrzYOA8dY)"


---
# Excursion: ETL Tools

Extract, tranform, load

----
## Data Warehousing (OLAP)

* Large denormalized databases with materialized views for large scale reporting queries
* e.g. sales database, queries for sales trends by region
* 
* Read-only except for batch updates: Data from OLTP systems loaded periodically, e.g. over night


![Data warehouse](datawarehouse.jpg)

Note: Image source: https://commons.wikimedia.org/wiki/File:Data_Warehouse_Feeding_Data_Mart.jpg

----
## ETL: Extract, Transform, Load

* Transfer data between data sources, often OLTP -> OLAP system
* Many tools and pipelines
    - Extract data from multiple sources (logs, JSON, databases), snapshotting
    - Transform: cleaning, (de)normalization, transcoding, sorting, joining
    - Loading in batches into database, staging
* Automation, parallelization, reporting, data quality checking, monitoring, profiling, recovery
* Often large batch processes
* Many commercial tools

<!-- references -->
Examples of tools in [several](https://www.softwaretestinghelp.com/best-etl-tools/) [lists](https://www.scrapehero.com/best-data-management-etl-tools/)

----
[![XPlenty Web Page Screenshot](xplenty.png)](https://www.xplenty.com/)


----

[![ETL everywhere](etleverywhere.png)](https://youtu.be/_bvrzYOA8dY?t=1452)

<!-- reference -->
Molham Aref "[Business Systems with Machine Learning](https://www.youtube.com/watch?v=_bvrzYOA8dY)"




---
# Complexity of Distributed Systems

----
![Stop Fail](bluescreen.png)

----
## Common Distributed System Issues

* Systems may crash
* Messages take time
* Messages may get lost
* Messages may arrive out of order
* Messages may arrive multiple times
* Messages may get manipulated along the way
* Bandwidth limits
* Coordination overhead
* Network partition
* ...

----
## Types of failure behaviors

* Fail-stop
* Other halting failures
* Communication failures
    * Send/receive omissions
    * Network partitions
    * Message corruption
* Data corruption
* Performance failures
    * High packet loss rate
    * Low throughput
    * High latency
* Byzantine failures

----
## Common Assumptions about Failures

* Behavior of others is fail-stop 
* Network is reliable 
* Network is semi-reliable but asynchronous
* Network is lossy but messages are not corrupt
* Network failures are transitive
* Failures are independent
* Local data is not corrupt
* Failures are reliably detectable
* Failures are unreliably detectable

----
## Strategies to Handle Failures

* Timeouts, retry, backup services
* Detect crashed machines (ping/echo, heartbeat)
* Redundant + first/voting
* Transactions
*
* Do lost messages matter?
* Effect of resending message?

----
## Test Error Handling

* Recall: Testing with stubs
* Recall: Chaos experiments








---
# Performance Planning and Analysis


----
## Performance Planning and Analysis

* Ideally architectural planning upfront
  * Identify key components and their interactions
  * Estimate performance parameters
  * Simulate system behavior (e.g., queuing theory)

* Existing system: Analyze performance bottlenecks
  * Profiling of individual components
  * Performance testing (stress testing, load testing, etc)
  * Performance monitoring of distributed systems

----
## Performance Analysis

* What is the average waiting?
* How many customers are waiting on average? 
* How long is the average service time?
* What are the chances of one or more servers being idle? 
* What is the average utilization of the servers?
*
* Early analysis of different designs for bottlenecks
* Capacity planning

----
## Queuing Theory

* Queuing theory deals with the analysis of lines where customers wait to receive a service
    * Waiting at Quiznos
    * Waiting to check-in at an airport
    * Kept on hold at a call center
    * Streaming video over the net
    * Requesting a web service
* A queue is formed when request for services outpace the ability of the server(s) to service them immediately
    * Requests arrive faster than they can be processed (unstable queue)
    * Requests do not arrive faster than they can be processed but their processing is delayed by some time (stable queue)
* Queues exist because infinite capacity is infinitely expensive and excessive capacity is excessively expensive

----
## Queuing Theory

![Simple Queues](queuingth.png)

----
## Analysis Steps (roughly)

* Identify system abstraction to analyze (typically architectural level, e.g. services, but also protocols, datastructures and components, parallel processes, networks)
* Model connections and dependencies
* Estimate latency and capacity per component (measurement and testing, prior systems, estimates, …)
* Run simulation/analysis to gather performance curves
* Evaluate sensitivity of simulation/analysis to various parameters (‘what-if questions’)


----
## Simulation (e.g., JMT)

![JMT screenshot](jmt1.png)

<!-- references -->

G.Serazzi Ed. Performance Evaluation Modelling with JMT: learning by examples. Politecnico di Milano - DEI, TR 2008.09, 366 pp., June 2008 


----
## Profiling 

Mostly used during development phase in single components

![VisualVM profiler](profiler.jpg)

----
## Performance Testing

* Load testing: Assure handling of maximum expected load
* Scalability testing: Test with increasing load
* Soak/spike testing: Overload application for some time, observe stability
* Stress testing: Overwhelm system resources, test graceful failure + recovery
*
* Observe (1) latency, (2) throughput, (3) resource use
* All automateable; tools like JMeter

----
## Performance Monitoring of Distributed Systems

[![](distprofiler.png)](distprofiler.png)

<!-- references -->
Source: https://blog.appdynamics.com/tag/fiserv/


----
## Performance Monitoring of Distributed Systems

* Instrumentation of (Service) APIs
* Load of various servers
* Typically measures: latency, traffic, errors, saturation
* 
* Monitoring long-term trends
* Alerting
* Automated releases/rollbacks
* Canary testing and A/B testing






---

# Summary

* Large amounts of data (training, inference, telemetry, models)
* Distributed storage and computation for scalability
* Common design patterns (e.g., batch processing, stream processing, lambda architecture)
* Design considerations: mutable vs immutable data
* Distributed computing also in machine learning
* Lots of tooling for data extraction, transformation, processing
* Many challenges through distribution: failures, debugging, performance, ...


Recommended reading: Martin Kleppmann. [Designing Data-Intensive Applications](https://dataintensive.net/). OReilly. 2017.



