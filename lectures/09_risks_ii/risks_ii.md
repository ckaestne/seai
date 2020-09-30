---
author: Christian Kaestner
title: "17-445: Risk and Planning for Mistakes"
semester: Summer 2020
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---  

# Risk and Planning for Mistakes II

Eunsuk Kang

<!-- references -->

Required reading: "How Big Data Transformed Applying to College", Cathy O'Neil 

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

----
## Risks?

* Lane assist system
* Credit rating
* Amazon product recommendation
* Audio transcription service
* Cancer detection
* Predictive policing

**Discuss potential risks, including impact and likelyhood**

<!-- discussion -->


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
* SPEC: Lane detection accurately identifies the lane markings; the
  controller generates correct steering commands to keep the vehicle
  within lane

----
## Example: FTA for Lane Assist

<!---
![lane-assist-fta](lane-assist-fta.png)
--->
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

* __Goal__: Detect when a component failure occurs
* __Heartbeat__ pattern
  * Periodically sends diagnostic message to monitor
* __Doer-Checker__ pattern
  * Doer: Perform primary function; untrusted and potentially faulty
  * Checker: If doer output faulty, perform corrective action
    (e.g., default safe output, shutdown); trusted and verifiable

----
## Doer-Checker Example: Autonomous Vehicle

![](safety-controller.jpg)

* ML-based controller (__doer__): Generate commands to maneuver vehicle
  * Complex DNN; makes performance-optimal control decisions
* Safe controller (__checker__): Checks commands from ML controller; overrides it
  with a safe default command if maneuver deemed risky
  * Simpler, based on verifiable, transparent logic; conservative control

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
* But:
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
  * LC components should be allowed to access min. necessary data 
* Limit interactions across criticality boundaries
  * Deploy LC & HC components on different networks
  * Add monitors/checks at interfaces
* Identify and eliminate implicit interactions
  * Memory: Shared memory, global variables
  * CPU resources: LC tasks running at high-priority, starving HC tasks
* Is AI in my system performing an LC or HC task?
  * If HC, can we "demote" it into LC?

----
## Example: Radiation Therapy

![](mgh.png)

* __Safety requirement__: If door opens during treatment, insert beam block.

----
## Existing Design

* Which components are responsible for establishing this safety requirement
(e.g., high critical)?
* Existing design includes:
  * Pub/sub event handler: 3rd-party library; missing source code;
    company went bankrupt
  * Event logging: May throw an error if disk full
  * Event handler/logging used by all tasks, including LC ones
* Is it possible to achieve high confidence that these HC components don't fail?

<!-- split -->

![](mgh-original.png)

----
## Alternative Design

* Build in an emergency unit
  * Bypass event handler for HC tasks
* Still needs to rely on door & beam controllers
  * Can't eliminate the risk of failure, but significantly reduce it
  * Emergency unit simpler, can be verified & tested
  
<!-- split -->

![](mgh-redesign.png)

---
# Summary

* Accept that ML components will make mistakes
* Use risk analysis to identify and mitigate potential problems
* Design strategies for detecting and mitigating the risks from mistakes by AI
