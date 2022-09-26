---
author: Christian Kaestner
title: "17-645: Deploying a Model"
semester: Fall 2022
footer: "17-645 Machine Learning in Production • Christian Kaestner, Carnegie Mellon University • Fall 2022"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---  
<!-- .element: class="titleslide"  data-background="../_chapterimg/09_deployment.jpg" -->
<div class="stretch"></div>

## Machine Learning in Production

# Deploying a Model


---
## Deeper into architecture and design...

![Overview of course content](../_assets/overview.svg)
<!-- .element: class="plain stretch" -->



---
## Midterm

Next week Wednesday, here

Questions based on shared scenario, apply concepts

Past midterms [online](https://github.com/ckaestne/seai/tree/F2022/exams), similar style

All lectures and readings in scope, focus on concepts with opportunity to practice (e.g., recitations, homeworks, in-class exercises)

Closed book, but 6 sheets of notes



----

## Learning Goals

<div class="smallish">

* Understand important quality considerations when deploying ML components
* Follow a design process to explicitly reason about alternative designs and their quality tradeoffs
* Gather data to make informed decisions about what ML technique to use and where and how to deploy it
* Understand the power of design patterns for codifying design knowledge
*
* Create architectural models to reason about relevant characteristics
* Critique the decision of where an AI model lives (e.g., cloud vs edge vs hybrid), considering the relevant tradeoffs 
* Deploy models locally and to the cloud
* Document model inference services

</div>

----
## Readings

Required reading: 
* 🕮 Hulten, Geoff. "[Building Intelligent Systems: A Guide to Machine Learning Engineering.](https://www.buildingintelligentsystems.com/)" Apress, 2018, Chapter 13 (Where Intelligence Lives).
* 📰 Daniel Smith. "[Exploring Development Patterns in Data Science](https://www.theorylane.com/2017/10/20/some-development-patterns-in-data-science/)." TheoryLane Blog Post. 2017.

Recommended reading: 
* 🕮 Rick Kazman, Paul Clements, and Len Bass. [Software architecture in practice.](https://www.oreilly.com/library/view/software-architecture-in/9780132942799/?ar) Addison-Wesley Professional, 2012, Chapter 1




---
# Deploying a Model is Easy

----
## Deploying a Model is Easy

Model inference component as function/library

```python
from sklearn.linear_model import LogisticRegression
model = … # learn model or load serialized model ...
def infer(feature1, feature2):
    return model.predict(np.array([[feature1, feature2]])
```

----
## Deploying a Model is Easy

Model inference component as a service


```python
from flask import Flask, escape, request
app = Flask(__name__)
app.config['UPLOAD_FOLDER'] = '/tmp/uploads'
detector_model = … # load model…

# inference API that returns JSON with classes 
# found in an image
@app.route('/get_objects', methods=['POST'])
def pred():
    uploaded_img = request.files["images"]
    coverted_img = … # feature encoding of uploaded img
    result = detector_model(converted_img)
    return jsonify({"response":
                result['detection_class_entities']})

```

----
## Deploying a Model is Easy

Packaging a model inference service in a container


```docker
FROM python:3.8-buster
RUN pip install uwsgi==2.0.20
RUN pip install tensorflow==2.7.0
RUN pip install flask==2.0.2
RUN pip install gunicorn==20.1.0
COPY models/model.pf /model/
COPY ./serve.py /app/main.py
WORKDIR ./app
EXPOSE 4040
CMD ["gunicorn", "-b 0.0.0.0:4040", "main:app"]
```

----
## Deploying a Model is Easy

Model inference component as a service in the cloud

* Package in container or other infrastructure
* Deploy in cloud infrastructure
* Auto-scaling with demand ("*Stateless Serving Functions Pattern*")
* MLOps infrastructure to automate all of this (more on this later)
    * [BentoML](https://github.com/bentoml/BentoML) (low code service creation, deployment, model registry), 
    * [Cortex](https://github.com/bentoml/BentoML) (automated deployment and scaling of models on AWS), 
    * [TFX model serving](https://www.tensorflow.org/tfx/guide/serving) (tensorflow GRPC services)
    * [Seldon Core](https://www.seldon.io/tech/products/core/) (no-code model service and many many additional services for monitoring and operations on Kubernetes)




----
## But is it really easy?

Offline use?

Deployment at scale?

Hardware needs and operating cost?

Frequent updates?

Integration of the model into a system?

Meeting system requirements?

**Every system is different!**

----
## Every System is Different

Personalized music recommendations for Spotify

Transcription service startup

Self-driving car

Smart keyboard for mobile device

----
## Inference is a Component within a System

![Transcription service architecture example](transcriptionarchitecture2.svg)
<!-- .element: class="stretch plain" -->





---
# Recall: Thinking like a Software Architect 

![Architecture between requirements and implementation](req-arch-impl.svg)
<!-- .element: class="plain" -->


----
## Recall: Systems Thinking

![](system.svg)
<!-- .element: class="plain stretch" -->

> A system is a set of inter-related components that work together in a particular environment to perform whatever functions are required to achieve the system's objective -- Donella Meadows



---

# Architectural Modeling and Reasoning
----
![](pgh.jpg)
Notes: Map of Pittsburgh. Abstraction for navigation with cars.
----
![](pgh-cycling.jpg)
Notes: Cycling map of Pittsburgh. Abstraction for navigation with bikes and walking.
----
![](pgh-firezones.png)
Notes: Fire zones of Pittsburgh. Various use cases, e.g., for city planners.
----
## Analysis-Specific Abstractions

All maps were abstractions of the same real-world construct

All maps were created with different goals in mind
   - Different relevant abstractions
   - Different reasoning opportunities
 
Architectural models are specific system abstractions, for reasoning about specific qualities

No uniform notation

----

## What can we reason about?

![](lan-boundary.png)
<!-- .element: class="stretch" -->

----

## What can we reason about?

![](gfs.png)<!-- .element: style="width:1050px" -->


<!-- references -->
Ghemawat, Sanjay, Howard Gobioff, and Shun-Tak Leung. "[The Google file system.](https://ai.google/research/pubs/pub51.pdf)" ACM SIGOPS operating systems review. Vol. 37. No. 5. ACM, 2003.

Notes: Scalability through redundancy and replication; reliability wrt to single points of failure; performance on edges; cost

----
## What can we reason about?

![Apollo Self-Driving Car Architecture](apollo.png)
<!-- .element: class="stretch" -->

<!-- references_ -->
Peng, Zi, Jinqiu Yang, Tse-Hsun Chen, and Lei Ma. "A first look at the integration of machine learning models in complex autonomous driving systems: a case study on Apollo." In Proc. FSE, 2020.

----

## Suggestions for Graphical Notations

Use notation suitable for analysis

Document meaning of boxes and edges in legend

Graphical or textual both okay; whiteboard sketches often sufficient

Formal notations available















---

# Case Study: Augmented Reality Translation


![Seoul Street Signs](seoul.jpg)
<!-- .element: class="stretch" -->


Notes: Image: https://pixabay.com/photos/nightlife-republic-of-korea-jongno-2162772/

----
## Case Study: Augmented Reality Translation
![Google Translate](googletranslate.png)
<!-- .element: class="stretch" -->

----
## Case Study: Augmented Reality Translation
![Google Glasses](googleglasses.jpg)
<!-- .element: class="stretch" -->

Notes: Consider you want to implement an instant translation service similar toGoogle translate, but run it on embedded hardware in glasses as an augmented reality service.
----
## System Qualities of Interest?

<!-- discussion -->


---
# Design Decision: Selecting ML Algorithms

What ML algorithms to use and why? Tradeoffs?

![](googletranslate.png)
<!-- .element: class="stretch" -->


Notes: Relate back to previous lecture about AI technique tradeoffs, including for example
Accuracy
Capabilities (e.g. classification, recommendation, clustering…)
Amount of training data needed
Inference latency
Learning latency; incremental learning?
Model size
Explainable? Robust?

---
# Design Decision: Where Should the Model Live?

(Deployment Architecture)

----
## Where Should the Models Live?

![AR Translation Architecture Sketch](ar-architecture.svg)
<!-- .element: class="plain" -->

Cloud? Phone? Glasses?

What qualities are relevant for the decision?

Notes: Trigger initial discussion


----
## Considerations

* How much data is needed as input for the model?
* How much output data is produced by the model?
* How fast/energy consuming is model execution?
* What latency is needed for the application?
* How big is the model? How often does it need to be updated?
* Cost of operating the model? (distribution + execution)
* Opportunities for telemetry?
* What happens if users are offline?

----
## Breakout: Latency and Bandwidth Analysis


1. Estimate latency and bandwidth requirements between components
2. Discuss tradeoffs among different deployment models


![AR Translation Architecture Sketch](ar-architecture.svg)
<!-- .element: class="plain stretch" -->


As a group, post in `#lecture` tagging group members:
* Recommended deployment for OCR (with justification):
* Recommended deployment for Translation (with justification):



Notes: Identify at least OCR and Translation service as two AI components in a larger system. Discuss which system components are worth modeling (e.g., rendering, database, support forum). Discuss how to get good estimates for latency and bandwidth.

Some data:
200ms latency is noticable as speech pause; 
20ms is perceivable as video delay, 10ms as haptic delay;
5ms referenced as cybersickness threshold for virtual reality
20ms latency might be acceptable

bluetooth latency around 40ms to 200ms

bluetooth bandwidth up to 3mbit, wifi 54mbit, video stream depending on quality 4 to 10mbit for low to medium quality

google glasses had 5 megapixel camera, 640x360 pixel screen, 1 or 2gb ram, 16gb storage


----

![Example of an architectural diagram](arch-diagram-example.svg)
<!-- .element: class="stretch plain" -->


----
## From the Reading: When would one use the following designs?

* Static intelligence in the product
* Client-side intelligence (user-facing devices)
* Server-centric intelligence
* Back-end cached intelligence
* Hybrid models
*
* Consider: Offline use, inference latency, model updates, application updates, operating cost, scalability, protecting intellectual property


Notes:
From the reading:
* Static intelligence in the product
    - difficult to update
    - good execution latency
    - cheap operation
    - offline operation
    - no telemetry to evaluate and improve
* Client-side intelligence
    - updates costly/slow, out of sync problems
    - complexity in clients
    - offline operation, low execution latency
* Server-centric intelligence
    - latency in model execution (remote calls)
    - easy to update and experiment
    - operation cost
    - no offline operation
* Back-end cached intelligence
    - precomputed common results
    - fast execution, partial offline 
    - saves bandwidth, complicated updates
* Hybrid models


----
## Where Should Feature Encoding Happen?

![Feature Encoding](featureencoding.svg)
<!-- .element: class="plain" -->

*Should feature encoding happen server-side or client-side? Tradeoffs?*

Note: When thinking of model inference as a component within a system, feature encoding can happen with the model-inference component or can be the responsibility of the client. That is, the client either provides the raw inputs (e.g., image files; dotted box in the figure above) to the inference service or the client is responsible for computing features and provides the feature vector to the inference service (dashed box). Feature encoding and model inference could even be two separate services that are called by the client in sequence. Which alternative is preferable is a design decision that may depend on a number of factors, for example, whether and how the feature vectors are stored in the system, how expensive computing the feature encoding is, how often feature encoding changes, how many models use the same feature encoding, and so forth. For instance, in our stock photo example, having feature encoding being part of the inference service is convenient for clients and makes it easy to update the model without changing clients, but we would have to send the entire image over the network instead of just the much smaller feature vector for the reduced 300 x 300 pixels.


----
## Reusing Feature Engineering Code


![Feature encoding shared between training and inference](shared-feature-encoding.svg)
<!-- .element: class="plain stretch" -->


Avoid *training–serving skew*

----
## The Feature Store Pattern

* Central place to store, version, and describe feature engineering code
* Can be reused across projects
* Possible caching of expensive features


Many open source and commercial offerings, e.g.,  Feast, Tecton, AWS SageMaker Feature Store

----
## Tecton Feature Store

<iframe width="1200" height="600" src="https://www.youtube.com/embed/u_L_V2HQ_nQ" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

----
## More Considerations for Deployment Decisions

Coupling of ML pipeline parts

Coupling with other parts of the system

Ability for different developers and analysts to collaborate

Support online experiments

Ability to monitor


----
## Real-Time Serving; Many Models

![Apollo Self-Driving Car Architecture](apollo.png)
<!-- .element: class="stretch" -->

<!-- references_ -->
Peng, Zi, Jinqiu Yang, Tse-Hsun Chen, and Lei Ma. "A first look at the integration of machine learning models in complex autonomous driving systems: a case study on Apollo." In Proc. FSE. 2020.


----
## Infrastructure Planning (Facebook Examp.)

![Example of Facebook’s Machine Learning Flow and Infrastructure](facebook-flow.png)
<!-- .element: class="stretch" -->

<!-- references_ -->

Hazelwood, Kim, Sarah Bird, David Brooks, Soumith Chintala, Utku Diril, Dmytro Dzhulgakov, Mohamed Fawzy et al. "Applied machine learning at facebook: A datacenter infrastructure perspective." In Int'l Symp. High Performance Computer Architecture. IEEE, 2018.

----
## Capacity Planning (Facebook Example)

<div class="small">

| Services | Relative Capacity | Compute | Memory |
|--|--|--|--|
| News Feed | 100x | Dual-Socket CPU | High |
| Facer (face recognition) | 10x | Single-Socket CPU | Low |
| Lumos (image understanding) | 10x | Single-Socket CPU | Low |
| Search | 10x | Dual-Socket CPU | High |
| Lang. Translation | 1x | Dual-Socket CPU | High |
| Sigma (anomaly and spam detection) | 1x | Dual-Socket CPU | High |

* Trillions of inferences per day, in real time
* Preference for cheap single-CPU machines whether possible
* Different latency requirements, some "nice to have" predictions
* Some models run on mobile device to improve latency and reduce communication cost

</div>

<!-- references -->

Hazelwood, et al. "Applied machine learning at facebook: A datacenter infrastructure perspective." In Int'l Symp. High Performance Computer Architecture. IEEE, 2018.


----
## Operational Robustness

Redundancy for availability?

Load balancer for scalability?

Can mistakes be isolated?
   - Local error handling?
   - Telemetry to isolate errors to component?

Logging and log analysis for what qualities?



---
# Preview: Telemetry Design

----
## Telemetry Design

How to evaluate system performance and mistakes in production?

![](googletranslate.png)
<!-- .element: class="stretch" -->

Notes: Discuss strategies to determine accuracy in production. What kind of telemetry needs to be collected?

----
## The Right and Right Amount of Telemetry

<div class="smallish">

Purpose:
   - Monitor operation
   - Monitor mistakes (e.g., accuracy)
   - Improve models over time (e.g., detect new features)

Challenges:
   - too much data, no/not enough data
   - hard to measure, poor proxy measures
   - rare events
   - cost
   - privacy

**Interacts with deployment decisions**

</div>

----
## Telemetry Tradeoffs

What data to collect? How much? When?

Estimate data volume and possible bottlenecks in system.

![](googletranslate.png)
<!-- .element: class="stretch" -->

Notes: Discuss alternatives and their tradeoffs. Draw models as suitable.

Some data for context:
Full-screen png screenshot on Pixel 2 phone (1080x1920) is about 2mb (2 megapixel); Google glasses had a 5 megapixel camera and a 640x360 pixel screen, 16gb of storage, 2gb of RAM. Cellar cost are about $10/GB.





---
# Integrating Models into a System

----
## Recall: Inference is a Component within a System

![Transcription service architecture example](transcriptionarchitecture2.svg)
<!-- .element: class="plain stretch" -->

----
## Separating Models and Business Logic

![3-tier architecture integrating ML](3tier-with-ml.svg)
<!-- .element: class="stretch plain" -->

<!-- references_ -->
Based on: Yokoyama, Haruki. "Machine learning system architectural pattern for improving operational stability." In Int'l Conf. Software Architecture Companion, pp. 267-274. IEEE, 2019.

----
## Separating Models and Business Logic

Clearly divide responsibilities

Allows largely independent and parallel work, assuming stable interfaces

Plan location of non-ML safeguards and other processing logic



----
## Composing Models: Ensemble and metamodels

![Ensemble models](ensemble.svg)
<!-- .element: class="plain" -->

----
## Composing Models: Decomposing the problem, sequential

![](sequential-model-composition.svg)
<!-- .element: class="plain" -->

----
## Composing Models: Cascade/two-phase prediction

![](2phase-prediction.svg)
<!-- .element: class="plain" -->









---
# Documenting Model Inference Interfaces



----
## Why Documentation

Model inference between teams:
  * Data scientists developing the model
  * Other data scientists using the model, evolving the model
  * Software engineers integrating the model as a component
  * Operators managing model deployment

Will this model work for my problem?

What problems to anticipate?

----
## Classic API Documentation


```java
/**
 * compute deductions based on provided adjusted 
 * gross income and expenses in customer data.
 *
 * see tax code 26 U.S. Code A.1.B, PART VI
 */
float computeDeductions(float agi, Expenses expenses);
```



----
## What to document for models?

<!-- discussion -->

----
## Documenting Input/Output Types for Inference Components

```js
{
  "mid": string,
  "languageCode": string,
  "name": string,
  "score": number,
  "boundingPoly": {
    object (BoundingPoly)
  }
}
```
From Google’s public [object detection API](https://cloud.google.com/vision/docs/object-localizer).

----
## Documentation beyond I/O Types

Intended use cases, model capabilities and limitations

Supported target distribution (vs preconditions)

Accuracy (various measures), incl. slices, fairness

Latency, throughput, availability (service level agreements)

Model qualities such as explainability, robustness, calibration

Ethical considerations (fairness, safety, security, privacy)


**Example for OCR model? How would you describe these?**

----
## Model Cards 

* Proposal and template for documentation from Google
  * Intended use, out-of-scope use
  * Training and evaluation data
  * Considered demographic factors
  * Accuracy evaluations
  * Ethical considerations
* 1-2 page summary
* Focused on fairness
* Widely discussed, but not frequently adopted

<!-- references -->
Mitchell, Margaret, et al. "[Model cards for model reporting](https://arxiv.org/abs/1810.03993)." In *Proceedings of the Conference on Fairness, Accountability, and Transparency*, 2019.

----
![Model card example](modelcard.png)
<!-- .element: class="stretch" -->

<!-- references_ -->
Example from Model Cards paper

----
![Model card screenshot from Google](modelcard2.png)
<!-- .element: class="stretch" -->

<!-- references_ -->
From: https://modelcards.withgoogle.com/object-detection

----
## FactSheets 

<div class="smallish">

Proposal and template for documentation from IBM; intended to communicate intended qualities and assurances

Longer list of criteria, including
  * Service intention, intended use
  * Technical description
  * Target distribution
  * Own and third-party evaluation results
  * Safety and fairness considerations, explainability
  * Preparation for drift and evolution
  * Security, lineage and versioning

</div>

<!-- references -->
Arnold, Matthew, et al. "[FactSheets: Increasing trust in AI services through supplier's declarations of conformity](https://arxiv.org/pdf/1808.07261.pdf)." *IBM Journal of Research and Development* 63, no. 4/5 (2019): 6-1.

----
## Recall: Correctness vs Fit

Without a clear specification a model is difficult to document

Need documentation to allow evaluation for *fit*

Description of *target distribution* is a key challenge












---
# Design Patterns for AI Enabled Systems

(no standardization, *yet*)

----
## Design Patterns are Codified Design Knowl.

Vocabulary of design problems and solutions

![Observer pattern](observer.png)
<!-- .element: class="stretch" -->


Example: *Observer pattern* object-oriented design pattern describes a solution how objects can be notified when another object changes without strongly coupling these objects to each other

----
## Common System Structures

Client-server architecture

Multi-tier architecture

Service-oriented architecture and microservices

Event-based architecture

Data-flow architecture

----
## Multi-Tier Architecture

![3-tier architecture integrating ML](3tier-with-ml.svg)
<!-- .element: class="stretch plain" -->

<!-- references_ -->
Based on: Yokoyama, Haruki. "Machine learning system architectural pattern for improving operational stability." In Int'l Conf. Software Architecture Companion, pp. 267-274. IEEE, 2019.


----
## Microservices

![Microservice illustration](microservice.svg)
<!-- .element: class="stretch plain" -->


(more later)



----
## Patterns for ML-Enabled Systems

* Stateless/serverless Serving Function Pattern
* Feature-Store Pattern
* Batched/precomuted serving pattern
* Two-phase prediction pattern
* Batch Serving Pattern
* Decouple-training-from-serving pattern


----
## Anti-Patterns

* Big Ass Script Architecture
* Dead Experimental Code Paths
* Glue code
* Multiple Language Smell
* Pipeline Jungles
* Plain-Old Datatype Smell
* Undeclared Consumers



<!-- references -->

See also: 🗎 Washizaki, Hironori, Hiromu Uchida, Foutse Khomh, and Yann-Gaël Guéhéneuc. "[Machine Learning Architecture and Design Patterns](http://www.washi.cs.waseda.ac.jp/wp-content/uploads/2019/12/IEEE_Software_19__ML_Patterns.pdf)." Draft, 2019; 🗎 Sculley, et al. "[Hidden technical debt in machine learning systems](http://papers.nips.cc/paper/5656-hidden-technical-debt-in-machine-learning-systems.pdf)." In NeurIPS, 2015.














---

# Summary

<div class="smallish">

Model deployment seems easy, but involves many design decisions
   * What models to use?
   * Where to deploy?
   * How to design feature encoding and feature engineering?
   * How to compose with other components?
   * How to document?
   * How to collect telemetry?

Problem-specific modeling and analysis: Gather estimates, consider design alternatives, make tradeoffs explicit

Codifying design knowledge as patterns

</div>

----
## Further Readings
<div class="small">

* 🕮 Lakshmanan, Valliappa, Sara Robinson, and Michael Munn. Machine learning design patterns. O’Reilly Media, 2020.
* 🗎 Mitchell, Margaret, Simone Wu, Andrew Zaldivar, Parker Barnes, Lucy Vasserman, Ben Hutchinson, Elena Spitzer, Inioluwa Deborah Raji, and Timnit Gebru. “Model cards for model reporting.” In Proceedings of the conference on fairness, accountability, and transparency, pp. 220–229. 2019. 
* 🗎 Arnold, Matthew, Rachel KE Bellamy, Michael Hind, Stephanie Houde, Sameep Mehta, Aleksandra Mojsilović, Ravi Nair, Karthikeyan Natesan Ramamurthy, Darrell Reimer, Alexandra Olteanu, David Piorkowski, Jason Tsay, and Kush R. Varshney. “FactSheets: Increasing trust in AI services through supplier’s declarations of conformity.” IBM Journal of Research and Development 63, no. 4/5 (2019): 6–1.
* 🗎 Yokoyama, Haruki. “Machine learning system architectural pattern for improving operational stability.” In 2019 IEEE International Conference on Software Architecture Companion (ICSA-C), pp. 267–274. IEEE, 2019.

</div>