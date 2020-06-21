---
author: Christian Kaestner, Eunsuk Kang
semester: Summer 2020
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---  

# Recitation: Decomposing Requirements

Christian Kaestner

Slides adopted from Eunsuk Kang


----
## The Role of Requirements Engineering

* Requirements engineering essential to understand risks and mistake mitigation
* Understand 
    * user interactions
    * safety requirements
    * security and privacy requirements
    * fairness requirements
    * possible feedback loops

----
## Machine vs World

![machine-world](machine-world.png)

* No software lives in vacuum; every system is deployed as part of the world
* A requirement describes a desired state of the world (i.e., environment)
* Machine (software) is _created_ to manipulate the environment into
  this state 

----
## Shared Phenomena

![phenomena](phenomena.jpg)

* Shared phenomena: Interface between the world & machine (actions,
  events, dataflow, etc.,)
* Requirements (REQ) are expressed only in terms of world phenomena 
* Assumptions (ENV) are expressed in terms of world & shared phenomena
* Specifications (SPEC) are expressed in terms of machine & shared phenomena


----
## Task 1: Machine vs World

![machine-world](machine-world.png)

**Task: In groups, identify Requirements, Assumptions and Specifications for (1) Amazon product recommendations, (2) predictive policing, (3) screening applicants for Masters program**


----
## What could go wrong?

![machine-world](machine-world.png)

* Missing/incorrect environmental assumptions (ENV)
* Wrong specification (SPEC)
* Inconsistency in assumptions & spec (ENV ∧ SPEC = False)
* Inconsistency in requirements (REQ = False)


----
## Non-AI Example: Lufthansa 2904 Runway Crash

![Plane Crash](lufthansacrash.jpg)
<!-- .element: class="stretch" -->


* Reverse thrust (RT): Decelerates plane during landing
* What was required (REQ): RT enabled if and only if plane on the ground
* What was implemented (SPEC): RT enabled if and only if wheel turning
* But: Runway wet + wind, wheels did not turn, pilot overridden by software



----
## Feedback Loops and Adversaries

![machine-world](machine-world.png)
<!-- .element: class="stretch" -->

* Feedback loops: Behavior of the machine affects the world, which affects inputs to the machine
* Data drift: Behavior of the world changes over time, assumptions no longer valid
* Adversaries: Bad actors deliberately may manipulate inputs, violate environment assumptions

----
## Task 2: Identify potential problems

* Missing/incorrect environmental assumptions (ENV)
* Wrong specification (SPEC)
* Inconsistency in assumptions & spec (ENV ∧ SPEC = False)
* Inconsistency in requirements (REQ = False)
* Resulting in problems with feedback loops, data drift, adversaries

**Task: In groups, identify examples of problems in (1) Amazon product recommendations, (2) predictive policing, (3) screening applicants for Masters program**



