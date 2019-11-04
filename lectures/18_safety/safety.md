---
author: Eunsuk Kang
title: "17-445: Safety"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---

# Safety

Eunsuk Kang

<!-- references -->

Required reading: _Ironies of Automation_, Lisanne Bainbridge (1983) 

---
# Learning Goals

* Understand major safety challenges in AI-enabled systems
* Discuss the benefits and limitations of hazard analysis techniques
* Discuss ways to design systems to be safe against potential failures

---
# Safety

----
## What is Safety?

* Prevention of a system failure or malfunction that results in:
  * Death or serious injury to people
  * Loss or severe damage to equipment/property
  * Harm to the environment or society

----
## Case Study: Self-Driving Car

![](self-driving.jpeg)

----
## How did traditional vehicles become safe?

![](nader-report.png)

* National Traffic & Motor Safety Act (1966)
  * Mandatory design changes (head rests, shatter-resistant
  windshields, safety belts); road improvements (center lines,
  reflectors, guardrails)

----
## Autonomous Vehicles: What's different?

![](av-hype.png)

* In traditional vehicles, humans ultimately responsible for safety
<!-- .element: class="fragment" -->
  * Some safety features (lane keeping, emergency braking) designed to
  help & reduce risks
  * i.e., safety = human control + safety mechanisms
* Use of AI in autonomous vehicles: Perception, control, routing,
etc.,
<!-- .element: class="fragment" -->
  * Inductive training: No explicit requirements or design insights
  * __Q. Can ML achieve safe design solely through lots of data?__

----
## Challenge: Edge/Unknown Cases

![](av-weird-cases.jpg)

* Gaps in training data; ML will unlikely to cover all unknown cases
* __Q. Why is this a unique problem for AI__? What about humans?

----
## Demonstrating Safety

![](av-miles.jpg)

__Q. More miles tested => safer?__

----
## Approach for Demonstrating Safety

* Identify relevant hazards & safety requirements
* Identify potential root causes for hazards
* For each hazard, develop a mitigation strategy
* Provide evidence that mitigations are properly implemented

---
# Hazard Analysis

----
## What is Hazard Analysis?

![requirement-vs-spec](acc.png)

* __Hazard__: A condition or event that may result in undesirable outcome
  * e.g., "Ego vehicle is in risk of a collision with another vehicle."
* __Safety requirement__: Intended to eliminate or reduce one or more hazards
  * "Ego vehicle must always maintain some minimum safe distance to the leading vehicle."
* __Hazard analysis__: Methods for identifying hazards & potential root causes 

<!-- ---- -->
<!-- ## Recall: Requirement vs Specification -->

<!-- ![requirement-vs-spec](acc.png) -->

<!-- * __REQ__: Ego vehicle must always maintain some minimum safe -->
<!-- distance to the leading vehicle.  -->
<!-- * __ENV__: Engine is working as intended; sensors are providing -->
<!--   accurate information about the leading car (current speed, distance...) -->
<!-- * __SPEC__: Depending on the sensor readings, the controller must -->
<!--   issue an actuator command to accelerate/decelerate the vehicle as needed. -->

----
## Review: Fault Tree Analysis (FTA)

![](fta-example.png)

* Top-down, __backward__ search method for root cause analysis
  * Start with a given hazard (top event), derive a set of component
    faults (basic events)
  * Compute minimum cutsets as potential root causes
  * __Q. But how do we identify relevant hazards in the first place?__

----
## Forward vs Backward Search

![](search-types.png)

----
## Failure Mode and Effects Analysis (FMEA)

![](fmea-radiation.png)

* A __forward search__ technique to identify potential hazards
* Widely used in aeronautics, automotive, healthcare, food services,
  semiconductor processing, and (to some extent) software

----
## FMEA Process

* Identify system components
* Enumerate potential failure modes
* For each failure mode, identify:
  * Potential hazardous effect on the system
  * Method for detecting the failure
  * Potential mitigation strategy

----
## FMEA Example: Autonomous Vehicles

![](apollo.png)

* Architecture of the Apollo autonomous driving platform 

----
## FMEA Example: Autonomous Vehicles

| Component | Failure Mode | Failure Effects | Detection | Mitigation |
|---|---|---|---|---|
| Perception | Failure to detect an object | Risk of collision | Human operator (if present) | Deploy secondary classifier |
| Perception | Detected but misclassified | " | " | " |
| Lidar Sensor | Mechanical failure | Inability to detect objects | Monitor | Switch to manual control mode |
| ... | ... | ... | ... |  ... | 

----
## FMEA Process

* Identify system components
* Enumerate potential failure modes
* For each failure mode, identify:
  * Potential hazardous effect on the system
  * Method for detecting the failure
  * Potential mitigation strategy
* __Q. What are potential limitations of FMEA?__
  * Single component failures only; ignores component interactions
  <!-- .element: class="fragment" -->
  * Where do failure modes come from?
  <!-- .element: class="fragment" -->

----
## Hazard and Operability Study (HAZOP)

![](hazop.png)

* A __forward search__ method to identify potential hazards
* For each component, use a set of __guide words__ to generate
possible deviations from expected behavior
* Consider the impact of each generated deviation: Can it
  result in a system-level hazard?

----
## HAZOP Example: Emergency Braking (EB)

![](hazop-eb.jpg)

* Specificaton: EB must apply a maximum braking
command to the engine.
  * __NONE__: EB does not generate any braking command.
  * __LESS__: EB applies less than max. braking.
  * __LATE__: EB applies max. braking but after a delay of 2
  seconds.
  * __REVERSE__: EB generates an acceleration command instead of braking.
  * __BEFORE__: EB applies max. braking before a possible crash is detected.

----
## HAZOP Exercise: Autonomous Vehicles

![](apollo.png)

* Architecture of the Apollo autonomous driving platform 

----
## HAZOP Exercise: Perception

![](hazop-perception.jpg)

* What is the specifcation of the perception component?
* Use HAZOP to answer:
  * What are possible deviations from the specification?
  * What are potential hazards resulting from these deviatations?

----
## HAZOP: Benefits & Limitations

![](hazop.png)

* Easy to use; encourages systematic reasoning about component faults
* Can be combined with FTA/FMEA to generate faults (i.e., basic
events in FTA)
* Potentially labor-intensive; relies on engineer's judgement
* Does not guarantee to find all hazards (but also true for other techniques)

----
## Remarks: Hazard Analysis

* None of these method guarantee completeness
  * You may still be missing important hazards, failure modes
* Intended as structured approaches to thinking about failures
  * But cannot replace human expertise and experience
* When available, leverage prior domain knowledge 
  * __Safety standards__: A set of design and process guidelines for
    establishing safety
  * ISO 26262, ISO 21448, IEEE P700x, etc., 
  * Most do not consider AI; new standards being developed (e.g., UL
    4600)

----
## Safety Standards

---
# Designing for Safety

----
## Elements of Safe Design

* __Assume__: Components will fail at some point
* __Goal__: Minimize the impact of failures on safety
* __Detection__
  * Monitoring
* __Control__
  * Graceful degradation (fail-safe)
  * Redundancy (fail over)
* __Prevention__
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
* Safety controller (__checker__): Checks commands from ML controller; overrides it
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
* __Hot Standby__: Stanby watches & takes over when primary fails
* __Voting__: Select the majority decision
* Caution: Do components fail independently?
  * Reasonable assumption for hardware/mechanical failures
  * __Q. What about software?__

----
## Response: Redundancy (Failover)

![](redundancy.jpg)

* __Goal__: When a component fails, continue to provide the same
  functionality 
* __Hot Standby__: Stanby watches & takes over when primary fails
* __Voting__: Select the majority decision
* Caution: Do components fail independently?
  * Reasonable assumption for hardware/mechanical failures
  * Software: Difficult to achieve independence even when built by
    different teams (e.g., N-version programming)
  * __Q. ML components?__

----
## Prevention: Decoupling & Isolation

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
## Prevention: Decoupling & Isolation

* Goal: Faults in a low-critical (LC) components should not impact
  high-critical (HC) components
* Apply the principle of least privilege
  * LC components should be allowed to access min. necessary data 
* Limit interactions across criticality boundaries
  * Deploy LC & HC components on different networks
  * Add monitors/checks at interfaces
* Identify and eliminate implicit interactions
  * Memory: Shared memory, global variables
  * CPU resources: LC tasks running at high-priorty, starving HC tasks
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

* __Key takeaway__: Adopt a safety mindset!
  * Assume all components will eventually fail in one way or another
  * No AI is perfect, and it will make mistakes
  * Design your system to explicitly reduce the impact of these mistakes

