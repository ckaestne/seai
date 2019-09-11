---
author: Eunsuk Kang and Christian Kaestner
title: "17-445: Requirements and Risks"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---  

# Requirements and Risks

Eunsuk Kang

<!-- references -->

Required reading: Hulten, Geoff. "Building Intelligent Systems: A
Guide to Machine Learning Engineering." (2018), Chapters 6, 7, and 24.

---
# Learning Goals

* Understand the importance of requirements in software engineering.
* Understand the role of environmental assumptions in establishing requirements.
* Understand ways in which mistakes in an AI-based system can undermine
  a requirement.
* Identify and evaluate risks in AI systems using fault tree analysis.

---
# Software Requirements

----
## Requirements

Describe what the system will do (and not how it will do them)

![requirements](requirements.png)
<!-- .element: class="stretch" -->

----
## Importance of Requirements

![mythical-man-month](mythical.jpg)

_"The hardest single part of building a software system is deciding
precisely what to build...No other part of the work so cripples the resulting system if done wrong."_
-- Fred Brooks, Mythical Man Month (1975)

----
## Importance of Requirements

![national academies study](nas.jpg)

Only 3% of fatal software accidents due to coding errors; rest due to
**poor requirements** or usability issues (National Research Council, 2007)

----
## Types of Requirements

* Functional requirements
<!-- .element: class="fragment" -->
  * What the system should do in terms of functionality
  * Input & output, response to events
* Quality (non-functional) requirements
<!-- .element: class="fragment" -->
  * How well the system delivers its functionality
  * Performance, reliability, security, safety, availability...

----
## Examples of Requirements

**Privacy**: _The dietary restrictions of a participant may never be disclosed to other invited participants without his or her consent._

**Reliability**: _The train acceleration control software shall have a mean time between failures of the order of 109 hours._

**Performance**: _Responses to bibliographical queries shall take less than 2 seconds._

**Development**: _The overall cost of the new library software should
  not exceed X USD._

----
## Discussion: Product Recommendation

![Product recommendations](recommendations.png)

Q. What are functional & quality requirements?

----
## Machine vs World

![machine-world](machine-world.png)

* No software lives in vacuum; every system is deployed as part of the world
* A requirement describes a desired state of the world (i.e., environment)
* Machine (software) is _created_ to manipulate the environment into
  this state

----
## Machine vs World

![machine-world](machine-world.png)

* Q. What is the environment for the following systems?
  * Self-driving car: ??
  * Smart home thermostats: ?? 
  * Movie recommender: ??

----
## Requirement vs Specification

![requirement-vs-spec](env-spec.png)

* Requirement (REQ): What customer needs, as desired effects on the environment
* Assumptions (ENV): What’s assumed about the behavior/properties of
  the environment (based on domain knowledge)
* Specification (SPEC): What machine must do in order to satisfy REQ

----
## Shared Phenomena

![phenomena](phenomena.jpg)

* Shared phenomena: Interface between the world & machine (actions,
  events, dataflow, etc.,)
* Requirements (REQ) are expressed only in terms of world phenomena 
* Assumptions (ENV) are expressed in terms of world & shared phenomena
* Specifications (SPEC) are expressed in terms of machine & shared phenomena

----
## Example: Adaptive Cruise Control

![requirement-vs-spec](acc.png)

* Requirement (REQ): The ego vehicle must always maintain some minimum safe
distance to the leading vehicle. 
* Assumptions (ENV): ?
* Specification (SPEC): ?

----
## Example: Adaptive Cruise Control

![requirement-vs-spec](acc.png)

* REQ: The ego vehicle must always maintain some minimum safe
distance to the leading vehicle. 
* ENV: Engine is working as intended; sensors are providing
  accurate information about the leading car (current speed, distance...)
* SPEC: Depending on the sensor readings, the controller must
  issue an actuator command to accelerate/decelerate the vehicle as needed.

----
## What could go wrong?

![requirement-vs-spec](env-spec.png)

* Missing/incorrect environmental assumptions (ENV)
<!-- .element: class="fragment" -->
* Wrong specification (SPEC)
<!-- .element: class="fragment" -->
* Inconsistency in assumptions & spec (ENV ∧ SPEC = False)
<!-- .element: class="fragment" -->
* Inconsistency in requirements (REQ = False)
<!-- .element: class="fragment" -->

----
## Lufthansa 2904 Runaway Crash

![lufthansa2094](swiss2904.png)

* Reverse thrust (RT): Decelerates plane during landing
<!-- .element: class="fragment" -->
* What was required (REQ): RT enabled if and only if plane on the
ground
<!-- .element: class="fragment" -->
* What was implemented (SPEC): RT enabled if and only if wheel turning
<!-- .element: class="fragment" -->
* But runway wet due to rain
<!-- .element: class="fragment" -->
  * Wheel fails to turn, even though the plane is on the ground
  * Pilot attempts to enable RT; overridden by the software
  * Plane goes off the runway!

----
## Implications on Software Development

* Software/AI alone cannot establish system requirements
<!-- .element: class="fragment" -->
  * They are just one part of the system!
* Environmental assumptions are just as critical
<!-- .element: class="fragment" -->
  * But typically you can't modify these
  * Must design SPEC while treating ENV as given
* If you ignore/misunderstand these, your system may fail to satisfy
  its requirements!
<!-- .element: class="fragment" -->

----
## Deriving SPEC from REQ

1. Identify environmental entities and machine components
<!-- .element: class="fragment" -->
2. State a desired requirement (REQ) over the environment
<!-- .element: class="fragment" -->
3. Identify the interface between the environment & machines
<!-- .element: class="fragment" -->
4. Identify the environmental assumptions (ENV)
<!-- .element: class="fragment" -->
5. Develop software specifications
(SPEC) that are sufficient to establish REQ
<!-- .element: class="fragment" -->
6. Check whether ENV ∧ SPEC ⊧ REQ
<!-- .element: class="fragment" -->
7. If NO, strengthen SPEC & repeat Step 5
<!-- .element: class="fragment" -->

----
## Example: Infusion Pump

![infusion-pump-pic](infusion-pump-pic.jpg)

----
## Exercise: Infusion Pump

![infusion-pump](infusion-pump.png)

* REQ: Patients should be delivered the correct amount
  of dose as prescribed.
  * What are environmental entities? Machine components?
  * What are interfaces between them?
  * What are environmental assumptions? (ENV)
  * What specifications must be implemented by machines? (SPEC)
  
---
# Risk Analysis

----
## What is Risk Analysis?

*  What can possibly go wrong in my system, and what are potential 
impacts on system requirements?
<!-- .element: class="fragment" -->
* Risk = Likelihood * Impact
<!-- .element: class="fragment" -->
* A number of methods:
<!-- .element: class="fragment" -->
  * Failure mode & effects analysis (FMEA)
  * Hazard analysis
  * Why-because analysis
  * Fault tree analysis (FTA) <= Today's focus!
  * ...
  
----
## Fault Tree Analysis (FTA)

* Fault tree: A top-down diagram that displays the relationships
between a system failure (i.e., requirement violation) and its potential causes.  
<!-- .element: class="fragment" -->
  * Identify sequences of events that result in a failure
  * Prioritize the contributors leading to the failure
  * Inform decisions about how to (re-)design the system
  * Investigate an accident & identify the root cause 
* Often used for safety & reliability, but can also be used for
other types of requirement (e.g., poor performance, security attacks...)
<!-- .element: class="fragment" -->

![fta-sample](fta-sample.png)

----
## Fault Tree Analysis & AI

* Increaseingly used in automotive, aeronautics, industrial control systems, etc.,
* AI is just one part of the system
<!-- .element: class="fragment" -->
* AI will EVENTUALLY make mistakes
<!-- .element: class="fragment" -->
  * Ouput wrong predictions/values
  * Fail to adapt to changing environment
  * Confuse users, etc.,
* How do mistakes made by AI contribute to system failures? How do we
  ensure their mistakes do not result in a catastrophe?
<!-- .element: class="fragment" -->

----
## Fault Trees:: Basic Building Blocks

![fta-blocks](fta-blocks.png)

* Event: An occurrence of a fault or an undesirable action
<!-- .element: class="fragment" -->
  * (Intermediate) Event: Explained in terms of other events
  * Basic Event: No further development or breakdown; leafs of the tree
* Gate: Logical relationship between an event & its immedicate subevents
<!-- .element: class="fragment" -->
  * AND: All of the sub-events must take place
  * OR: Any one of the sub-events may result in the parent event

<!-- references -->
Figure from _Fault Tree Analysis and Reliability Block Diagram_
(2016), Jaroslav Menčík. 

----
## Fault Tree Example

![fta-example](fta-example.png)

* Every tree begins with a TOP event (typically a violation of a requirement)
<!-- .element: class="fragment" -->
* Every branch of the tree must terminate with a basic event
<!-- .element: class="fragment" -->

<!-- references -->
Figure from _Fault Tree Analysis and Reliability Block Diagram_
(2016), Jaroslav Menčík. 

----
## Analysis

* What can we do with fault trees?
  * Qualitative analysis: Determine potential root causes of a
    failiure through _minimal cut set analysis_
  * Quantitative analysis: Compute the probablity of a failure

----
## Minimal Cut Set Analysis

![fta-example](fta-example.png)

* Cut set: A set of basic events whose simultaneous occurrence is
  sufficient to guarantee that the TOP event occurs.
* _Minimal_ cut set: A cut set from which a smaller cut set can be
obtained by removing a basic event.
* Q. What are minimal cut sets in the above tree?

----
## Failure Probability Analysis

* To compute the probability of the top event:
<!-- .element: class="fragment" -->
  * Assign probabilities to basic events (based on domain knowledge)
  * Apply probability theory to compute prob. of intermediate events
	through AND & OR gates
  * (Alternatively, as sum of prob. of minimal cut sets) 
* In this class, we won't ask you to do this.
<!-- .element: class="fragment" -->
  * Why is this especially challenging for software? 

----
## FTA Process

1. Specify the system structure
<!-- .element: class="fragment" -->
   * Environment entities & machine componetns
   * Assumptions (ENV) & specifications (SPEC)
2. Identify the top event as a violation of REQ
<!-- .element: class="fragment" -->
3. Construct the fault tree
<!-- .element: class="fragment" -->
  * Derive intermeiate events from violation of SPEC/ENV
4. Analyze the tree
<!-- .element: class="fragment" -->
  * Identify all possible minimal cut sets
5. Consider design modifications to eliminate certain cut sets
<!-- .element: class="fragment" -->
6. Repeat
<!-- .element: class="fragment" -->

----
## Example: Adaptive Cruise Control

![adaptive-cruise-control](acc.png)

* REQ: The ego vehicle must always maintain some minimum safe
distance to the leading vehicle. 
* ENV: Engine is working as intended; sensors are providing
  accurate information about the leading car (current speed, distance...)
* SPEC: Depending on the sensor readings, the controller must
  issue an actuator command to accelerate/decelerate the vehicle as needed.

----
## Example: Adaptive Cruise Control

![adaptive-cruise-control-fta](acc-fta.jpg)

----
## Exercise: Infusion Pump

![infusion-pump](infusion-pump.png)

* Perform FTA to identify potential causes for the following safety
  violation: Patient receives a lower amount of drug than prescribed
  (i.e., underdose)

----
## Individual Assignment #2

![uber-crash](uber-crash.png)

* Case Study: 2018 Uber accident in Tempe, Arizona
  * Derive specifications & environmental assumptions for
    safety req.
  * Perform FTA to identify potential causes

---
# Summary

* Software requirements
  * Machine vs World; specification vs requirements
  * Role of environmental assumptions in establishing requirements
* Risk analysis
  * Fault tree analysis for identifying root causes of a failure
