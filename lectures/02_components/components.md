---
author: Christian Kaestner
title: "17-445: Components of an AI-Enabled System"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
---  

# Components of an AI-Enabled System

Eunsuk Kang

<!-- references -->

Required reading: Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 2, 5, and 20.

---

# Learning Goals

* Understand the major components of a typical AI-enabled system and design
  decisions involved
* Understand the components of a typical ML pipeline and their responsibilities
* Illustrate the design space for AI-enabled systems for a given case study

---
# When to use AI?
----
## When to use AI?

* Big problems, requiring lots of work
* Open-ended problems, continuing to grow over time
* Time-changing problems, where the right answer changes over time
* Intrinsically hard problems, pushing boundaries of what's considered possible

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

![stock exchange](plane.jpg)
<!-- .element: class="stretch" -->

Picture by [David Mark](https://pixabay.com/users/12019-12019/?utm_source=link-attribution&amp;utm_medium=referral&amp;utm_campaign=image&amp;utm_content=100624)

---
# Components of an AI-Enabled System

----
## Components of an AI-Enabled System

* Objectives: What is the system trying to achieve?
* Experience: What does it allow users to do? How does it receive feedback?
* Intelligence: How does it achieve its objectives?
* Orchestration: How is everything put together? How does it evolve
over time?

----
## Example: Smart Light Switch

[Figure of a light switch]

----
## Objectives

* What is the system trying to achieve?
  * Measurable, achievable, 
* Q. What are the objectives of a smart light switch?
  * Bad: Turn off light when no one is home
  * OK: Maximize user's comfort
  * Better: Minimize the amount of electricity
  
Note: How different are these properties in nature? Quantitative vs qualitative.

----
## Experience

* What does it allow users to do? How does it receive feedback?
* Aspects of a user interaction
  * Presenting intelligence
  * Collecting feedback
  * Minimizing errors

----
## Presenting Intelligence

* Automate: Take action on user's behalf
* Prompt: Ask the user if an action should be taken
* Organize: Display a set of items in an order
* Annotate: Add information to a display

----
## Collecting Feedback

* Feedback mechanisms to collect:
	* Context of the interaction
	* Action taken by the user
	* Outcome (success, failure, in-between...)

----
## Minimizing Errors

* Avoid performing risky actions
* Control and restrict user interactions
* Take less forceful actions (prompt vs automate)
* Provide guidance for recovering from errors

----
## Intelligence

* How does it achieve its objectives?
  * Rules & heuristics
  * Machine learning
  * Hybrid approach

----
## Orchestration

* How is everything put together?
* How does it manage changes in:
  * Objective (e.g., a new metric to optimize)
  * Intelligence (a different ML model)
  * Experience (new users, usage patterns)
  * Errors (unexpected failures, abuse)

----
## Managing Changes

* Design mechanisms to:
  * Monitor objectives
  * Inspect & modify interaction
  * Update intelligence
  * Override intelligence when needed

---
# Exercise: A Sample AI Problem

[Figure: Illustrative photo]

* How would to design its:
  * Objectives?
  * Experience (presentation, feedback, errors)?
  * Intelligence?
  * Mechanisms to manage possible changes?

---
# ML-based Intelligent System

----
##  AI != ML

----
## Machine Learning Pipeline

![ML Pipeline](ML-pipeline.png)

[Semi Koen](https://towardsdatascience.com/not-yet-another-article-on-machine-learning-e67f8812ba86)

[Need a CC figure]

----
## Design Decisions in ML-based Systems

* Data collection and preparation
  * Training vs test sets, sizes
* Feature engineering
	* Often the most time-consuming part!
	* Requires in-depth domain knowledge
* Model selection & configuration
	* Structure: No. layers, decision tree depth...
	* Search algorithms

---
# Summary




