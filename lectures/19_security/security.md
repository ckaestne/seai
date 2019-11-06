---
author: Eunsuk Kang
title: "17-445: Security"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---

# Security

Eunsuk Kang

<!-- references -->

Required reading: _Uncover Security Design Flaws Using The STRIDE
Approach_ by Hernan, Lambert, Ostwald, and Shostack (MSDN, 2007).

---
# Learning Goals

* Understand key ingredients to achieving security
* Understand the process of threat modeling
* Understand emerging threat models for AI-enabled systems

---
# Security

----
## Elements of Security

* Security requirements (policies)
  * What does it mean for my system to be secure?
* Threat model
  * What are the attacker's goal, capability, and incentive?
* Attack surface
  * Which parts of the system are exposed to the attacker?
* Protection mechanisms
  * How do we prevent the attacker from compromising a security requirement?

----
## Security Requirements

![](cia-triad.png)

* "CIA triad" of information security
* __Confidentiality__: Sensitive data must be accessed by authorized users only
* __Integrity__: Sensitive data must be modifiable by authorized users only
* __Availability__: Critical services must be available when needed by clients


----
## Example: College Admission System

![](admission-hack.png)

----
## Confidentiality, integrity, or availability?

* _Applications to the program can only be viewed by staff and faculty in the department._
* _The application site should be able to handle requests on the
  day of the application deadline._
* _Application decisions are recorded only by the faculty and staff._ 
* _The application site should backup all applications in case of a server failure._
* _The acceptance notices can only be sent out by the program director._

---
# Threat Modeling

----
## Why Threat Model?

![](gate.png)

----
## What is Threat Modeling?

* Threat model: A profile of an attacker
  * __Goal__: What is the attacker trying to achieve?
  * __Capability__:
	* Knowledge: What does the attacker know?
	* Actions: What can the attacker perform?
	* Resources: How much effort can it spend? 
  * __Incentive__: Why does the attacker want to do this?

![](art-of-war.png)

----
## Attacker Goal

* What is the attacker trying to achieve?
* Example: College admission 
  * Access other applicants info without being authorized
  * Modify application status to “accepted”
  * Cause website shutdown to sabotage other applicants
* Relationship to security requirements
  * Attacker’s goal achieved => requirement violated
  * If not, the threat might not be relevant/important
  * e.g., hack a website to display cat photos on front page; annoying, but not critical 

----
## Attacker Capability

![](admission-threat-model.jpg)

* What are the attacker’s actions?
  * Highly depends on system boundary & its exposed interfaces
  * Use a system diagram to identify attack surface & actions
* Example: College admission
  * Physical: Break into building & access server
  * Cyber: Send malicious HTTP requests for SQL injection,
    DoS attack
  * Social: Send phishing e-mail, bribe an insider for access

----
## System Diagram


![](admission-threat-model.jpg)

* You can use any notation, as long as:
  * its constructs (e.g., boxes and lines) have clear meanings; use legend!
  * it clearly shows potentially malicious/untrusted agent(s) & interactions
    with the system

----
## STRIDE Threat Modeling

![](stride.png)

* A systematic approach to identifying threats & attacker actions
  * For each component, enumerate & identify potential threats 
  * e.g., Admission Server & DoS: Applicant may flood it with requests
* Tool available (Microsoft Threat Modeling Tool)
* Limitations:
  * May end up with a long list of threats, not all of them relevant
  * False sense of security: STRIDE does not imply completeness!

----
## Open Web Application Security Project

![](owasp.png)

* OWASP: Community-driven source of knowledge & tools for web security

---
# Threat Modeling for ML 

----
## ML Attacker Goal

* Confidentiality (privacy) attack
  * Infer a sensitive label for a data point (e.g., hospital record)
* Integrity attacks
  * Induce a model to misclassify data points from one class to another
  * e.g., Spam filter: Classify a spam as a non-spam
* Availability attacks
  * Reduce the accuracy of a model
  * Induce a model to misclassify many data points

----
## Attacker Capability

![](ml-cycle.png)

* Knowledge: Does the attacker have access to the model?
  * Training data? Learning algorithm used? Parameters?
* Actions:
  * Training time: __Poisoning attack__
  * Inference time: __Evasion attack__

<!-- references -->
_Understanding Machine Learning_, Bhogavalli (2019)

----
## Poisoning Attack: Availability

![](virus.png)

* Availability: Inject mislabeled training data to damage model quality
  * 3% poisoning => 11% decrease in accuracy (Steinhardt, 2017)
* Attacker must have some access to the training set
  * e.g., models trained on public data set (e.g., ImageNet)
* Example: Anti-virus (AV) scanner
  * Online platform for submission of potentially malicious code
  * Some AV company (allegedly) poisoned competitor's model
  

----
## Poisoning Attack: Integrity

![](spam.jpg)

* Insert training data with seemingly correct labels
* More targeted than availability attacks
  * Cause misclassification from one specific class to another

<!-- references -->
_Poison Frogs! Targeted Clean-Label Poisoning Attacks on Neural
Networks_, Shafahi et al. (2018)

----
## Example: Self-Driving Vehicles

![](self-driving.jpeg)

* What's the security (integrity) requirement?
* What are possible poisoning attacks?
* What does the attacker need to know/access?

----
## Defense against Poisoning Attacks

![](data-sanitization.png)

* Anomaly detection & data sanitization
  * Identify and remove outliers in training set
* Quality control over your training data
  * Who can modify or add to my training set? Do I trust the data
  source?
  * Use security mechanisms (e.g., authentication) and logging to
    track data provenance

<!-- references -->

_Stronger Data Poisoning Attacks Break Data Sanitization Defenses_,
Koh, Steinhardt, and Liang (2018).

----
## Evasion Attack (Adversarial Examples)

![](evasion-attack.png)

* Add noise to an existing sample & cause misclassification
* Attack at inference time
  * Typically assumes knowledge of the model (algorithm, parameters)
  * Recently, shown to be possible even when the attacker only has access to
    model output ("blackbox" attack)

<!-- references -->

_Accessorize to a Crime: Real and Stealthy Attacks on State-of-the-Art
Face Recognition_, Sharif et al. (2016).

----
## Example: Self-Driving Vehicles

![](self-driving.jpeg)

* Are evasion attacks possible?
* What are potential consequences?

----
## Defense against Evasion Attack

![](stop-sign.png)

* Adversarial training
  * Generate/find a set of adversarial examples
  * Re-train your model with correct labels
* Input sanitization
  * "Clean" & remove noise from input samples 
  * e.g., Color depth reduction, spatial smoothing, JPEG compression
* Redundancy: Design multiple mechanisms to detect an attack
  * Stop sign: Insert a barcode as a checksum; harder to bypass


<!-- references -->

_Reliable Smart Road Signs_, Sayin et al. (2019).

----
## State of ML Security

![](arms-race.jpg)

* On-going arms race (mostly among researchers)
  * Defenses proposed & quickly broken by noble attacks
* Assume ML component is likely vulnerable
  * Design your system to minimize impact of an attack
* Remember: There may be easier ways to compromise system
  * e.g., poor security misconfiguration (default password), lack of
    encryption, code vulnerabilities, etc., 

---
# Designing for Security

----
## Secure Design Principles 

* Principle of Least Privilege
  * A component should be given the minimal privileges needed to fulfill its functionality
  * Goal: Minimize the impact of a compromised component
* Isolation
  * Components should be able to interact with each other no more than necessary
  * Goal: Reduce the size of trusted computing base (TCB) 
  * TCB: Components responsible for establishing a security requirement(s)
	* If any of TCB compromised => security violation
	* Conversely, a flaw in non-TCB component => security still preserved!
  * In poor system designs, TCB = entire system

----
## Monolithic Design

![](monolithic1.png)

----
## Monolithic Design

![](monolithic2.png)

Flaw in any part of the system =>  Security impact on the entire system!

----
## Compartmentalized Design

![](component-design1.png)

----
## Compartmentalized Design

![](component-design2.png)

Flaw in one component =>  Limited impact on the rest of the system!

----
## Example: Mail Client

* Requirements
  * Receive & send email over external network
  * Place incoming email into local user inbox files
* Sendmail
  * Monolithic design
  * Historical source of many vulnerabilities
* Qmail: “Security-aware” mail agent
  * Compartmentalized design
  * Isolation based on OS process isolation
	* Separate modules run as separate “users” (UID)
	* Each user only has access to specific resources (files, network sockets, …)
  * Least privilege 
	* Minimal privileges for each UID
	* Only one “root” user (with all privileges); in comparison, entire sendmail runs as root

----
## Qmail Architecture

![](qmail1.png)

----
## Qmail Architecture

![](qmail2.png)

----
## Qmail Architecture

![](qmail3.png)

---
# Summary

* __Key takeaway__: Adopt a security mindset!
  * Assume all components may be vulnerable in one way or another
  * Consider new threat models emerging for AI-enabled systems
  * Design your system to explicitly reduce the impact of potential attacks
