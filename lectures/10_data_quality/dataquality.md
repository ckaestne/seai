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
## Case Study: Predicting Delivery Time

![Door Dash](doordash.png)

----
## Order Delivery Database

![Restaurant data](restaurant-data.jpg)

----
## What makes good quality data?

* Accuracy
  * The data was recorded correctly.
* Completeness
  * All relevant data was recorded.
* Uniqueness
  * The entries are recorded once.
* Consistency
  * The data agrees with itself.
* Timeliness
  * The data is kept up to date.

----
## Data is noisy

* Unreliable sensors or data entry
* Wrong results and computations, crashes
* Duplicate data, near-duplicate data
* Out of order data
* Data format invalid
*
* **Examples?**

----
## Data changes

* System objective changes over time
* Software components are upgraded or replaced
* Prediction models change
* Quality of supplied data changes
* User behavior changes
*
* **Examples?**

----
## Users may deliberately change data

* Users react to model output
* Users try to game/deceive the model
*
* **Examples?**

---

# Data Cleaning

![Data cleaning](data-cleaning.jpg)

----

![Quality Problems Taxonomy](qualityproblems.png)

<!-- references -->

Source: Rahm, Erhard, and Hong Hai Do. [Data cleaning: Problems and current approaches](http://dc-pubs.dbs.uni-leipzig.de/files/Rahm2000DataCleaningProblemsand.pdf). IEEE Data Eng. Bull. 23.4 (2000): 3-13.


----
## Single-Source Problem Examples

* Schema level:
<!-- .element: class="fragment" -->
    * Illegal attribute values: `bdate=30.13.70`
    * Violated attribute dependencies: `age=22, bdate=12.02.70`
    * Uniqueness violation: `(name=”John Smith”, SSN=”123456”), (name=”Peter Miller”, SSN=”123456”)`
    * Referential integrity violation: `emp=(name=”John Smith”, deptno=127)` if department 127 not defined
* Instance level:
<!-- .element: class="fragment" -->
	* Missing values: `phone=9999-999999`
    * Misspellings: `city=Pittsburg`
    * Misfielded values: `city=USA`
    * Duplicate records: `name=John Smith, name=J. Smith`
    * Wrong reference: `emp=(name=”John Smith”, deptno=127)` if department 127 defined but wrong

<!-- references -->

Further readings: Rahm, Erhard, and Hong Hai Do. [Data cleaning: Problems and current approaches](http://dc-pubs.dbs.uni-leipzig.de/files/Rahm2000DataCleaningProblemsand.pdf). IEEE Data Eng. Bull. 23.4 (2000): 3-13.

----
## Dirty Data: Example

![Dirty data](dirty-data-example.jpeg)

Q. Can you spot the problems with the data?

----
## Data Cleaning Overview

* Data analysis / Error detection
  * Error types: e.g. schema constraints, referential integrity, duplication 
  * Single-source vs multi-source problems
  * Detection in input data vs detection in later stages (more context)
* Error repair
  * Repair data vs repair rules, one at a time or holistic
  * Data transformation or mapping
  * Automated vs human guided

----
## Error Detection

* Illegal values: min, max, variance, deviations, cardinality
* Misspelling: sorting + manual inspection, dictionary lookup
* Missing values: null values, default values
* Duplication: sorting, edit distance, normalization

----
## Error Detection: Example

![Dirty data](dirty-data-example.jpeg)

Q. Can we (automatically) detect errors? Which errors are problem-dependent?

----
## Common Strategies

* Enforce schema constraints
  * e.g., delete rows with missing data or use defaults
* Explore sources of errors 
  * e.g., debugging missing values, outliers
* Remove outliers
  * e.g., Testing for normal distribution, remove > 2σ
* Normalization
  * e.g., range [0, 1], power transform
* Fill in missing values

----
## Data Cleaning Tools

![Open Refine](openrefine.jpg)

OpenRefine (formerly Google Refine), Trifacta Wrangler, Drake, etc.,

---

# Data Schema

----
## Data Schema

* Define expected format of data
  * expected fields and their types
  * expected ranges for values
  * constraints among values (within and across sources)
* Data can be automatically checked against schema
* Protects against change; explicit interface between components

----
## Schema in Relational Databases

```sql
CREATE TABLE employees (
    emp_no      INT             NOT NULL,
    birth_date  DATE            NOT NULL,
    name        VARCHAR(30)     NOT NULL,
    PRIMARY KEY (emp_no));
CREATE TABLE departments (
    dept_no     CHAR(4)         NOT NULL,
    dept_name   VARCHAR(40)     NOT NULL,
    PRIMARY KEY (dept_no), UNIQUE  KEY (dept_name));
CREATE TABLE dept_manager (
   dept_no      CHAR(4)         NOT NULL,
   emp_no       INT             NOT NULL,
   FOREIGN KEY (emp_no)  REFERENCES employees (emp_no),
   FOREIGN KEY (dept_no) REFERENCES departments (dept_no),
   PRIMARY KEY (emp_no,dept_no)); 
```

----
## Schema-Less Data Exchange

* CSV files
* Key-value stores (JSon, XML, Nosql databases)
* Message brokers
* REST API calls
* R/Pandas Dataframes

```csv
1::Toy Story (1995)::Animation|Children's|Comedy
2::Jumanji (1995)::Adventure|Children's|Fantasy
3::Grumpier Old Men (1995)::Comedy|Romance
```

```csv
10|53|M|lawyer|90703
11|39|F|other|30329
12|28|F|other|06405
13|47|M|educator|29206
```

----
## Example: Apache Avro

```json
{   "type": "record",
    "namespace": "com.example",
    "name": "Customer",
    "fields": [{
            "name": "first_name",
            "type": "string",
            "doc": "First Name of Customer"
        },        
        {
            "name": "age",
            "type": "int",
            "doc": "Age at the time of registration"
        }
    ]
}
```

----
## Example: Apache Avro

* Schema specification in JSON format
* Serialization and deserialization with automated checking
* Native support in Kafka
* 
* Benefits
  * Serialization in space efficient format
  * APIs for most languages (ORM-like)
  * Versioning constraints on schemas
* Drawbacks
  * Reading/writing overhead
  * Binary data format, extra tools needed for reading
  * Requires external schema and maintenance
  * Learning overhead

Notes: Further readings eg https://medium.com/@stephane.maarek/introduction-to-schemas-in-apache-kafka-with-the-confluent-schema-registry-3bf55e401321, https://www.confluent.io/blog/avro-kafka-data/, https://avro.apache.org/docs/current/

----
## Many Schema Formats

Examples
* Avro
* XML Schema
* Protobuf
* Thrift
* Parquet
* ORC
---

# Detecting Data Drift
----
## Data Drift & Model Decay

Data changes over time

* Structural drift
  * Data schema changes, sometimes by infrastructure changes
  * e.g., `4124784115` -> `412-478-4115`
* Semantic drift
  * Meaning of data changes, same schema
  * e.g., Netflix switches from 5-star to +/- rating, but still uses 1 and 5
* User/environment behavior changes
  * e.g., credit card fraud differs to evade detection
  * e.g., marketing affects sales of certain items
*
* **Other examples?**

----
## Detecting Data Drift

* Compare distributions over time (e.g., t-test)
* Detect both sudden jumps and gradual changes
* Distributions can be manually specified or learned (see invariant detection)

<!-- colstart -->
![Two distributions](twodist.png)
<!-- col -->
![Time series with confidence intervals](timeseries.png)
<!-- colend -->

----
## Excursion: Daikon for dynamic detection of likely invariants

* Software engineering technique to find invariants
  * e.g., `i>0`, `a==x`, `this.stack != null`, `db.query() after db.prepare()`
  * Pre- and post-conditions of functions, local variables
* Uses for documentation, avoiding bugs, debugging, testing, verification, repair
* Idea: Observe many executions (instrument code), log variable values, look for relationships (test many possible invariants)
----
## Daikon Example
<!-- colstart -->
```c
int ABS(int x) {
    if (x>0) return x;
    else return (x*(-1));
}
int main () {
    int i=0;
    int abs_i;
    for (i=-5000;i<5000;i++)
        abs_i=ABS(i);
}
```

Expected: `Return value of ABS(x) == (x>0) ? x: -x;`
<!-- col -->
```text
==================
std.ABS(int;):::ENTER
==================
std.ABS(int;):::EXIT1
x == return
==================
std.ABS(int;):::EXIT2
return == - x
==================
std.ABS(int;):::EXIT
x == orig(x)
x <= return
==================
```
<!-- colend -->

Notes: many examples in https://www.cs.cmu.edu/~aldrich/courses/654-sp07/tools/kim-daikon-02.pdf

----
## Dealing with Data Drift

* Regularly retrain model on recent data
  * Use evaluation in production to detect decaying model performance
* Involve humans when increasing inconsistencies detected
  - Monitoring thresholds, automation

---
# Data Linter

<!-- references -->
Further readings: Hynes, Nick, D. Sculley, and Michael Terry. (The data linter: Lightweight, automated sanity checking for ML data sets](http://learningsys.org/nips17/assets/papers/paper_19.pdf). NIPS MLSys Workshop. 2017.
----
## Excursion: Static Analysis and Code Linters

* Automate routine inspection tasks

```js
if (user.jobTitle = "manager") {
   ...
}
```

```js
function fn() {
    x = 1;
    return x;
    x = 3; // dead code
}
```

```java
PrintWriter log = null;
if (anyLogging) log = new PrintWriter(...);
if (detailedLogging) log.println("Log started");
```

----
## Static Analysis

* Analyzes the structure/possible executions of the code, without running it
* Different levels of sophistication
  * Simple heuristic and code patterns (linters)
  * Sound reasoning about all possible program executions
* Tradeoff between false positives and false negatives
* Often supporting annotations needed (e.g., `@Nullable`)
* Tools widely available, open source and commercial

![Eslint IDE integration](eslint.png)

----
## A Linter for Data?

<!-- discussion -->

----
## Data Linter at Google

* Miscoding
    * Number, date, time as string
    * Enum as real
    * Tokenizable string (long strings, all unique)
    * Zip code as number
* Outliers and scaling
    * Unnormalized feature (varies widely)
    * Tailed distributions
    * Uncommon sign
* Packaging
    * Duplicate rows
    * Empty/missing data

---
# Quality Assurance for the Data Processing Pipelines

----
## Error Handling and Testing in Pipeline

Avoid silent failures!

* Write testable data acquisition and feature extraction code
* Test this code (unit test, positive and negative tests)
* Test retry mechanism for acquisition + error reporting
* Test correct detection and handling of invalid input
* Catch and report errors in feature extraction
* Test correct detection of data drift
* Test correct triggering of monitoring system
* Detect stale data, stale models

More in the next lecture.

---
# Summary

* Introduction to *data cleaning*
* Introduction to *data schema* and unit testing for data
* Comparing data distributions and detecting data drift
* Quality assurance for the data processing pipelines

 
