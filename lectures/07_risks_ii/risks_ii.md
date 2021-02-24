---
author: Christian Kaestner and Eunsuk Kang
title: "17-445: Risk and Planning for Mistakes"
semester: Summer 2020
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner & Eunsuk Kang"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---  

# Risk and Planning for Mistakes II

Eunsuk Kang

<!-- references -->


<!-- references -->

Required reading: Hulten, Geoff. "Building Intelligent Systems: A
Guide to Machine Learning Engineering." (2018), Chapters 6–7 (Why
creating IE is hard, balancing IE) and 24 (Dealing with mistakes)

---
## Learning goals:

* Evaluate the risks of mistakes from AI components using the fault tree
analysis (FTA)
* Design strategies for mitigating the risks of failures due to AI mistakes

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

<!-- ---- -->
<!-- ## Risks? -->

<!-- * Lane assist system -->
<!-- * Credit rating -->
<!-- * Amazon product recommendation -->
<!-- * Audio transcription service -->
<!-- * Cancer detection -->
<!-- * Predictive policing -->

<!-- **Discuss potential risks, including impact and likelyhood** -->

<!-- <\!-- discussion -\-> -->

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
<!-- .element: class="stretch" -->

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
   * Environment entities & machine components
   * Assumptions (ENV) & specifications (SPEC)
2. Identify the top event as a violation of REQ
<!-- .element: class="fragment" -->
3. Construct the fault tree
<!-- .element: class="fragment" -->
  * Intermediate events can be derived from violation of SPEC/ENV
4. Analyze the tree
<!-- .element: class="fragment" -->
  * Identify all possible minimal cut sets
5. Consider design modifications to eliminate certain cut sets
<!-- .element: class="fragment" -->
6. Repeat
<!-- .element: class="fragment" -->

----
## Example: FTA for Lane Assist

![lane-assist](lane.jpg)

* REQ: The vehicle must be prevented from veering off the lane.
* ENV: Sensors are providing accurate information about the lane;
  driver responses when given warning; steering wheel is functional
* SPEC: Lane detection accurately identifies lane markings in image; the
  controller generates steering commands to keep the vehicle
  within lane

----
## Breakout: FTA for Lane Assist

![lane-assist](lane.jpg)

Draw a fault tree for the lane assist system with the top event as “Vehicle fails to stay within lane”

<!-- ---- -->
<!-- ## Example: FTA for Lane Assist -->

<!-- ![lane-assist-fta](lane-assist-fta.png) -->

---
# Mitigation Strategies

----
## Elements of Fault-Tolerant Design

* __Assume__: Components will fail at some point
* __Goal__: Minimize the impact of failures
* __Detection__
  * Monitoring
* __Response__
  * Graceful degradation (fail-safe)
  * Redundancy (fail over)
* __Containment__
  * Decoupling & isolation

----
## Detection: Monitoring

![](doer-checker.jpg)
<!-- .element: class="stretch" -->

* __Goal__: Detect when a component failure occurs
* __Monitor__: Periodically checks the output of a component for errors
  * Challenge: Need a way to recognize errors 
  * e.g., corrupt sensor data, slow or missing response
* __Doer-Checker__ pattern
  * Doer: Perform primary function; untrusted and potentially faulty
  * Checker: If doer output faulty, perform corrective action
    (e.g., default safe output, shutdown); trusted and verifiable

----
## Doer-Checker Example: Autonomous Vehicle
<!-- .element: class="stretch" -->

![](safety-controller.jpg)

* ML-based controller (__doer__): Generate commands to maneuver vehicle
  * Complex DNN; makes performance-optimal control decisions
* Safe controller (__checker__): Checks commands from ML controller; overrides it
  with a safe default command if maneuver deemed risky
  * Simpler, based on verifiable, transparent logic; conservative control

----
## Doer-Checker Example: Autonomous Vehicle

![](safety-controller-scenario.png)

* Yellow region: Slippery road, causes loss of traction
* ML-based controller (__doer__): Model ignores traction loss; generates
 unsafe maneuvering commands  (a)
* Safe controller (__checker__): Overrides with safe steering commands
  (b)

<!-- references -->
_Runtime-Safety-Guided Policy Repair_, Intl. Conference on Runtime Verification (2020)

----
## Response: Graceful Degradation (Fail-safe)

<video>
    <source data-src="rc-car.mp4" type="video/mp4" />
</video>

* __Goal__: When a component failure occurs, continue to provide
  safety (possibly at reduced functionality and performance)
* Relies on a monitor to detect component failures
* Example: Perception in autonomous vehicles
  * If Lidar fails, switch to a lower-quality detector; be more
  conservative
  * __But what about other types of ML failures? (e.g., misclassification)__

----
## Response: Redundancy (Failover)

![](redundancy.jpg)

* __Goal__: When a component fails, continue to provide the same
  functionality 
* __Hot Standby__: Standby watches & takes over when primary fails
* __Voting__: Select the majority decision
* Caution: Do components fail independently?
  * Reasonable assumption for hardware/mechanical failures
  * __Q. What about software?__

----
## Response: Redundancy (Failover)

![](redundancy.jpg)

* __Goal__: When a component fails, continue to provide the same
  functionality 
* __Hot Standby__: Standby watches & takes over when primary fails
* __Voting__: Select the majority decision
* Caution: Do components fail independently?
  * Reasonable assumption for hardware/mechanical failures
  * Software: Difficult to achieve independence even when built by
    different teams (e.g., N-version programming)
  * __Q. ML components?__

----
## Response: Human in the Loop

*Less forceful interaction, making suggestions, asking for confirmation*

* AI and humans are good at predictions in different settings
	* AI better at statistics at scale and many factors
	* Humans understand context and data generation process and often better with thin data 
* AI for prediction, human for judgment?
* But be aware of:
    * Notification fatigue, complacency, just following predictions; see *Tesla autopilot*
    * Compliance/liability protection only?
* Deciding when and how to interact
* Lots of UI design and HCI problems

**Examples?**

Notes: Cancer prediction, sentencing + recidivism, Tesla autopilot, military "kill" decisions, powerpoint design suggestions

----
## Response: Undoable Actions

*Design system to reduce consequence of wrong predictions, allowing humans to override/undo*

**Examples?**

Notes: Smart home devices, credit card applications, Powerpoint design suggestions

----
## Example: Lane Assist

**Q. Possible mitigation strategies?**

![lane-assist-fta](lane-assist-fta.png)
<!-- .element: class="stretch" -->

----
## Containment: Decoupling & Isolation

* __Goal__: Faults in a low-critical (LC) components should not impact
  high-critical (HC) components

----
## Poor Decoupling: USS Yorktown (1997)

![](yorktown.png)

* Invalid data entered into DB; divide-by-zero crashes entire network
* Required rebooting the whole system; ship dead in water for 3 hours 
* __Lesson__: Handle expected component faults; prevent propagation

----
## Poor Decoupling: Automotive Security

![](invehicle.png)

* Main components connected through a common CAN bus
  * Broadcast; no access control (anyone can read/write)
* Can control brake/engine by playing a malicious MP3 (Stefan Savage, UCSD)

----
## Containment: Decoupling & Isolation

* Goal: Faults in a low-critical (LC) components should not impact
  high-critical (HC) components
* Apply the principle of least privilege
  * LC components should be allowed to access min. necessary functions
* Limit interactions across criticality boundaries
  * Deploy LC & HC components on different networks
  * Add monitors/checks at interfaces
* Is AI in my system performing an LC or HC task?
  * If HC, can we "demote" it into LC?
  * Alternatively, replace HC AI components with non-AI ones
  * **Q. Examples?**

---
# Summary

* Accept that ML components will make mistakes
* Use risk analysis to identify and mitigate potential problems
* Design strategies for detecting and mitigating the risks from mistakes by AI
