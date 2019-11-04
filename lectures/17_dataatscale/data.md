---
author: Christian Kaestner
title: "17-445: Managing and Processing Large Datasets"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---

# Managing and Processing Large Datasets

Christian Kaestner

<!-- references -->

Required reading: Martin Kleppmann. [Designing Data-Intensive Applications](https://dataintensive.net/). OReilly. 2017. Chapter 1

---

# Learning Goals

* Organize different data management solutions and their tradeoffs
* Explain the tradeoffs between batch processing and stream processing and the lambda architecture
* Recommend and justify a design and corresponding technologies for a given system

---
# Case Study

![Google Photos Screenshot](gphotos.png)

---
## Data Storage Basics

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
## Tradeoffs

<!-- discussion -->

----
## Data Encoding

* Semi-structured, schema-free (JSON, XML)
* Schema-based encoding (CSV, binary)
* Compact encodings

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

![](deletedissues.svg)

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

> On a shopping website, a customer may add an item to their cart and then
> remove it again. Although the second event cancels out the first event from the point
> of view of order fulfillment, it may be useful to know for analytics purposes that the
> customer was considering a particular item but then decided against it. Perhaps they
> will choose to buy it in the future, or perhaps they found a substitute. This information is recorded in an event log, but would be lost in a database that deletes items
> when they are removed from the cart.

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
![](deletedissues.svg)

---

# Summary

* Data storage strategies and their tradeoffs
* Partitioning and replication for scalability
* Design considerations: mutable vs immutable data
* Common design patterns (e.g., batch processing, stream processing, lambda architecture)

Recommended reading: Martin Kleppmann. [Designing Data-Intensive Applications](https://dataintensive.net/). OReilly. 2017.



