---
author: Christian Kaestner
title: "17-445: Data Quality"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---

# Data Quality

Christian Kaestner

<!-- references -->

Required reading: Schelter, S., Lange, D., Schmidt, P., Celikel, M., Biessmann, F. and Grafberger, A., 2018. [Automating large-scale data quality verification](http://www.vldb.org/pvldb/vol11/p1781-schelter.pdf). Proceedings of the VLDB Endowment, 11(12), pp.1781-1794.

---

# Learning Goals

* Design and implement automated quality assurance steps that check data schema conformance and distributions 
* Devise thresholds for detecting data drift and schema violations
* Describe common data cleaning steps and their purpose and risks
* Evaluate the robustness of AI components with regard to noisy or incorrect data


---

# Data-Quality Challenges

----
## Case Study: Aggiculture management to increase crop yields

![Fields](fields.jpg)

Notes:

Sketch ideas what's possible.
Collect typical data sources.

Image: https://www.maxpixel.net/Agriculture-Campaign-Green-Aerial-View-Drone-4048496

----
## Data is noisy

* Unreliable sensors
* Wrong results and computations, crashes
* Duplicate data, near-duplicate data
* Out of order data
* Data format invalid
*
* **Examples?**

----
## Data changes

* Sensors replaced
* Software components replaced
* Other models change
* Quality of supplied data changes
* User behavior changes
*
* **Examples?**

----
## Users may deliberately change data

* Users react to model predictions
* Users try to attack the model
*
* **Examples?**

----
## Dimensions of Data Quality (excerpt)

* Uniqueness (deduplication)
* Completeness
* Consistency
* Conformity
* Relevance
* Precision
* Timeliness
*
* **Examples?**

---

# Data Cleaning

----
## Data Cleaning Overview

* Error detection
  * Error types: e.g. schema constraints, referential integrity, duplication 
  * Single-source vs multi-source problems
  * Detection in input data vs detection in later stages (more context)
* Error repair
  * Repair data vs repair rules, one at a time or holistic
  * Automated vs human guided

----

![Quality Problems Taxonomy](qualityproblems.png)

<!-- References -->

Source: Rahm, Erhard, and Hong Hai Do. [Data cleaning: Problems and current approaches](http://dc-pubs.dbs.uni-leipzig.de/files/Rahm2000DataCleaningProblemsand.pdf). IEEE Data Eng. Bull. 23.4 (2000): 3-13.


---
# Summary

* Introduction to *data cleaning*
* Introduction to *data schema* and unit testing for data
* Comparing data distributions and detecting data drift
* Quality assurance for the data processing pipelines
* Measures of noise, accuracy, and precision, and consequences for AI components (robustness)
 