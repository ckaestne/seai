---
author: Christian Kaestner and Eunsuk Kang
title: "17-445: Components of an AI-Enabled System"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---  

# Components of an AI-Enabled System

Eunsuk Kang

<!-- references -->

Required reading: Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 2, 5, and 20.

---

# Learning Goals

* Understand when (not) to use AI
* Understand the major components of a typical AI-enabled system and design
  decisions to be made
* Understand the major steps in a typical ML pipeline and their goals

---
# When to use AI?

----
# When to use AI?

# For everything!

----
# When to use AI?

# ~~For everything!~~

![Wrong tool for the job](wrong-tool.jpg)
<!-- .element: class="stretch" -->

----
## When to use AI?

* Difficult for computers, but easy for humans
<!-- .element: class="fragment" -->
	* e.g., "Hotdog or not hotdog?"

![hotdog](hotdog.jpg)
<!-- .element: class="fragment" -->

----
## When to use AI?

* Difficult for computers, but easy for humans
  * Object detection
  * Speech recognition & transcription
* Complex/unknown patterns, difficult even for humans
<!-- .element: class="fragment" -->  
	* Medical diagnosis, drug discovery
	* Sports data analytics
* A large amount of data processing required
<!-- .element: class="fragment" -->
	* Search engines
	* Movie recommendations
* Dynamic, oft-changing environment
<!-- .element: class="fragment" -->
  * (Systems need to learn and adapt)

----

## Use of AI?

![stock exchange](stockexchange.jpg)
<!-- .element: class="stretch" -->

CC BY-NC 2.0
[Travel Aficionado](https://www.flickr.com/photos/travel_aficionado/2396814840)

Notes: 
* Should it be used for the display panel of a stock exchange?
* For the bookkeeping and trading algorithms that determine prices and sign trades?
* For price prediction and automated trading?

----

## Use of AI?

![flash crash](flash-crash.png)
<!-- .element: class="stretch" -->

----

## Use of AI?

![AI judge](AI-judge.jpg)
<!-- .element: class="stretch" -->

----

## Use of AI?

![criminal detection](criminal-detection.png)
<!-- .element: class="stretch" -->

_"Automated Inference on Criminality using Face Images", Wu & Zhang (2016)_

----
## When to use AI: Caveat

* Difficult for computers, but easy for humans
* Complex/unknown patterns, difficult even for humans
* A large amount of data processing required
* BUT  just because AI looks suitable, doesn't mean you always should
use it!
<!-- .element: class="fragment" -->
   * Analyze potential risks of AI failures
   * Weigh them against benefits
   * Use AI only if risks are manageable or acceptably low
   * (We will come back to this topic later!)

---
# Components of an AI-Enabled System

----
## Components of an AI-Enabled System

* Objectives: What is the system trying to achieve?
<!-- .element: class="fragment" -->
* Experience: What does it allow users to do? How does it receive
feedback?
<!-- .element: class="fragment" -->
* Intelligence: How does it achieve its objectives?
<!-- .element: class="fragment" -->
* Orchestration: How is everything put together? How does it evolve
over time?
<!-- .element: class="fragment" -->
* (We will cover each of these topics in more detail later)
<!-- .element: class="fragment" -->

----
## Case Study: Safe Browsing Feature

![Safe Browsing](safe-browsing.png)

----
## Objectives

* What is the system trying to achieve?
* Properties of "good" objectives
  <!-- .element: class="fragment" -->
  * Measurable: Enables tracking & objective comparison
  * Achievable: Possible to achieve in time-to-market
  * Communicable: Transparent & comprehensible to stakeholders
* Q. What are the objectives of a safe browsing feature?
  <!-- .element: class="fragment" -->
  * "Prevent users from being hacked"
  <!-- .element: class="fragment" -->
  * "Minimize users' inconvenience"
  <!-- .element: class="fragment" -->
  * (Are these good? Can we do better?)
  <!-- .element: class="fragment" -->

  
Note: How different are these properties in nature? Quantitative vs qualitative.

----
## Measurable

![Safe Browsing Statistics](safe-browsing-stats.png)

----
## Achievable?

![No Perfect Security](100percent-secure.jpg)

----
## Communicable 

![Google Safe Browsing](google-safe-browsing-objective.png)

----
## Experience

* What does the system allow users to do? How does it receive feedback?
<!-- .element: class="fragment" -->
* Aspects of a user experience/interaction
<!-- .element: class="fragment" -->
  * Presenting intelligence
  * Collecting feedback
  * Minimizing errors

----
## Presenting Intelligence

* Automate: Take action on user's behalf
<!-- .element: class="fragment" -->
* Prompt: Ask the user if an action should be taken
<!-- .element: class="fragment" -->
* Organize: Display a set of items in an order
<!-- .element: class="fragment" -->
* Annotate: Add information to a display
<!-- .element: class="fragment" -->
* Q. What are design choices for safe browsing?
<!-- .element: class="fragment" -->

----
## Collecting Feedback

* Feedback mechanisms to collect:
  <!-- .element: class="fragment" -->
	* Context of the interaction
	* Action taken by the user
	* Outcome (success, failure, in-between...)
* Q. What information would you collect for safe browsing?
	<!-- .element: class="fragment" -->

----
## Collecting Feedback

![Safe Browsing Feedback](safe-browsing-feedback.png)

----
## Minimizing (Impact of) Errors

* Avoid performing risky actions
<!-- .element: class="fragment" -->
* Control and restrict user interactions
<!-- .element: class="fragment" -->
* Take less forceful actions (prompt vs automate)
<!-- .element: class="fragment" -->
* Provide guidance for recovering from errors
<!-- .element: class="fragment" -->

----
## Controling User Interactions

![Safe browsing warning](warning.png)

----
## Safe Interactions in Self-Driving Cars

![Self driving cars](self-driving.png)

----
## Intelligence

* How does it achieve its objectives?
<!-- .element: class="fragment" -->
  * Rules & heuristics
  * Symbolic AI methods
  * Machine learning
  * Hybrid approach
* Q. What kind of intelligence would you use for safe browsing?
<!-- .element: class="fragment" -->

----
## Orchestration

* How is everything put together?
<!-- .element: class="fragment" -->
* How does it manage changes in:
<!-- .element: class="fragment" -->
  * Objective (e.g., a new metric to optimize)
  * Intelligence (a different ML model)
  * Experience (new users, usage patterns)
  * Errors (unexpected failures, abuse)
* Q. What are possible changes to safe browsing? 
<!-- .element: class="fragment" -->

----
## Managing Changes

* Design mechanisms to:
  * Monitor objectives
  <!-- .element: class="fragment" -->
  * Inspect & modify interaction
  <!-- .element: class="fragment" -->
  * Update intelligence
  <!-- .element: class="fragment" -->
  * Override intelligence when needed
  <!-- .element: class="fragment" -->
  
---
# ML-based Intelligent Systems

----
#  AI != ML

![AI vs ML](AIvsML.jpg)

----
## Another Case Study: Food Delivery

![Door Dash](doordash.png)

----
## Predicting Delivery Time

* What are its objective? How do we measure success?
<!-- .element: class="fragment" -->
* How do we present intelligence & receive feedback?
<!-- .element: class="fragment" -->
* How do we build the intelligence?
  <!-- .element: class="fragment" -->
  * What factors does it depend on?
  * What can be used for learning & prediction?

----
## Typical Machine Learning Pipeline

![ML Pipeline](ML-pipeline.png)

Figure by [Semi Koen](https://towardsdatascience.com/not-yet-another-article-on-machine-learning-e67f8812ba86)

----
## ML Tasks by Phase

* Before deployment:
<!-- .element: class="fragment" -->
  * Obtain labeled data
  <!-- .element: class="fragment" -->
  * Identify and extract features
  <!-- .element: class="fragment" -->
  * Split data into training and evaluation set
  <!-- .element: class="fragment" -->
  * Learn model from training data
  <!-- .element: class="fragment" -->
  * Evaluate model on evaluation data
  <!-- .element: class="fragment" -->
  * Repeat, revising features
  <!-- .element: class="fragment" -->
* After deployment:
<!-- .element: class="fragment" -->
  * Evaluate model on production data; monitor
  <!-- .element: class="fragment" -->
  * Select production data for retraining
  <!-- .element: class="fragment" -->
  * Update model regularly
  <!-- .element: class="fragment" -->

<!-- ---- -->
<!-- ## Design Decisions in ML-based Systems -->

<!-- * Data collection and preparation -->
<!--   * Training vs test sets, sizes -->
<!-- * Feature engineering -->
<!-- * Model selection & configuration -->
<!--   * Structure: No. layers, decision tree depth, etc.,  -->
<!--   * Search algorithms -->
<!-- * (More in later lectures) -->

----

<!-- small -->

## Example Data

| RestaurantID | Order| OrderTime|ReadyTime|PickupTime|
|-|-|-|-|-|
| 5 |5A;3;10;11C;C:No onion| 18:11|18:23|18:31|
|...|
|...|
|...|

----

## Data Processing

* Data cleaning
  <!-- .element: class="fragment" -->
  * Remove outliers
  * Normalize data
  * Fill in missing values
  * Remove misleading/useless items
* Feature Engineering
  <!-- .element: class="fragment" -->
  * Identify parameters of interest that a model can learn on
  * Convert initial data into feature set
  * Select relevant subset of features
* Q. What features would you use for delivery prediction?
<!-- .element: class="fragment" -->

----

## Features?

![Door Dash](doordash.png)

----

## Features for delivery prediction

* Order time, day of week
* Average number of orders in that hour
* Order size
* Special requests
* Order items
* Preparation time

----

## Learning

Build a predictor that best describes an outcome for the observed features

| RestaurantID | Order3 | SpecialRequest | DayOfWeek | PreparationTime |
|-|-|-|-|-|
|5|yes| yes|2|12|
|...|
|...|
|...|

----

## Evaluation

* Accuracy on learned data vs accuracy on unseen data
  * Separate learning set, not used for training
![data sets](data-sets.png)

----

## Evaluation Methods

* For binary predictors: False positives vs false negatives, recall, precision
<!-- .element: class="fragment" -->
* For numeric predictors: Average (relative) distance between real & predicted values
<!-- .element: class="fragment" -->
* For ranking predictors: Top-K algorithms, etc., 
<!-- .element: class="fragment" -->
* (More details in later lectures!)
<!-- .element: class="fragment" -->

----
## Evaluation Method?

![](doordash.png)

----
## Recall vs Precision

![Recall vs Precision](recallprecision.png)

----

## Underfitting vs Overfitting

* Overfitting: Model learns exactly the input data, but does not
generalize to unseen data
<!-- .element: class="fragment" -->
* Underfitting: Model makes very general observations but poorly
fits to data
<!-- .element: class="fragment" -->
* Adjust degrees of freedom in the model to balance between
overfitting and underfitting
	<!-- .element: class="fragment" -->
	* Challenging to get right in practice! 

----
## Underfitting example
<!-- .element: class="fragment" -->

<!-- colstart -->

|Text|Genre|
|-|-|
|When the earth stood ... |Science fiction|
|Two households, both alike...|Romance|
|To Sherlock Holmes she...|Adventure|

<!-- col -->
![](underfitting.png)
<!-- colend -->

----
## Overfitting example
<!-- .element: class="fragment" -->

<!-- colstart -->

|Text|Genre|
|-|-|
|When the earth stood ... |Science fiction|
|Two households, both alike...|Romance|
|To Sherlock Holmes she...|Adventure|

<!-- col -->
![](overfitting.png)
<!-- colend -->

----
## Learning and Evaluating in Production

* Beyond static data sets, build telemetry
<!-- .element: class="fragment" -->
  * (This week's recitation on Apache Kafka)
* Use sample of live data for evaluation
<!-- .element: class="fragment" -->
* Retrain models with sampled live data regularly
<!-- .element: class="fragment" -->
* Monitor objectives and intervene if necessary
<!-- .element: class="fragment" -->

---
# Summary

* Recognize when (not) to use AI
  * Even if AI looks suitable, think about potential risks!
* Consider & evaluate design decisions in all aspects of an AI-based system
  * Objectives, experiences, intelligence, orchestration
* Understand typical ML tasks & evaluation methods
