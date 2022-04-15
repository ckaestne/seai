---
author: Eunsuk Kang
title: "17-445: Security"
semester: Fall 2020
footer: "17-445 ML in Production, Christian
Kaestner & Eunsuk Kang"
---

# Security

Eunsuk Kang

<!-- references -->
Required reading:
	_Building Intelligent Systems: A Guide to Machine Learning Engineering_, G. Hulten (2018), Chapter 25: Adversaries and Abuse.
	_The Top 10 Risks of Machine Learning Security_, G. McGraw et al., IEEE Computer (2020).

---
# Learning Goals

* Explain key concerns in security (in general and with regard to ML models)
* Identify security requirements with threat modeling
* Analyze a system with regard to attacker goals, attack surface, attacker capabilities 
* Describe common attacks against ML models, including poisoning and evasion attacks
* Understand design opportunities to address security threats at the system level
* Apply key design principles for secure system design

---
# Security: (Very Brief) Overview

----
## Elements of Security

* Security requirements (also called "policies")
<!-- .element: class="fragment" -->
  * What does it mean for my system to be secure?
* Threat model
  <!-- .element: class="fragment" -->
  * What are the attacker's goals, capabilities, and incentives?
* Attack surface
<!-- .element: class="fragment" -->
	* Which parts of the system are exposed to the attacker?
* Defense mechanisms (mitigiations)
<!-- .element: class="fragment" -->
	* How do we prevent the attacker from compromising a security requirement?

----
## Security Requirements

![](cia-triad.png)

* What do we mean by "secure"?
* Common security requirements: "CIA triad" of information security
* __Confidentiality__: Sensitive data must be accessed by authorized users only
* __Integrity__: Sensitive data must be modifiable by authorized users only
* __Availability__: Critical services must be available when needed by clients

----
## Example: College Admission System

![](admission-hack.png)

----
## Confidentiality, integrity, or availability?

* Applications to the program can only be viewed by staff and faculty
in the department.
<!-- .element: class="fragment" -->
* The application site should be able to handle requests on the
day of the application deadline.
<!-- .element: class="fragment" -->
* Application decisions are recorded only by the faculty and staff.
<!-- .element: class="fragment" -->
* The acceptance notices can only be sent out by the program director.
<!-- .element: class="fragment" -->

----
## Other Security Requirements 

* Authentication: Users are who they say they are
* Non-repudiation: Certain changes/actions in the system can be traced to who was responsible for it
* Authorization: Only users with the right permissions can access a resource/perform an action

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
	* Actions: What can the attacker do?
	* Resources: How much effort can it spend? 
  * __Incentive__: Why does the attacker want to do this?

![](art-of-war.png)

----
## Attacker Goal

* What is the attacker trying to achieve?
  * Typically, undermine one or more security requirements
<!-- .element: class="fragment" -->
* Example: College admission
<!-- .element: class="fragment" -->
	* Access other applicants info without being authorized
	<!-- .element: class="fragment" -->
	* Modify application status to “accepted”
	<!-- .element: class="fragment" -->
	* Cause website shutdown to sabotage other applicants
	<!-- .element: class="fragment" -->

----
## Attacker Capability

![](admission-threat-model.jpg)
<!-- .element: class="stretch" -->

* What actions are available to the attacker (to achieve its goal)?
  * Depends on system boundary & interfaces exposed to external actors
  * Use an architecture diagram to identify attack surface & actions

<!-- ---- -->
<!-- ## Architecture Diagram for Threat Modeling -->

<!-- ![](admission-threat-model.jpg) -->

<!-- * You can use any notation, as long as: -->
<!--   * its constructs (e.g., boxes and lines) have clear meanings; use legend! -->
<!--   * it clearly shows potentially malicious/untrusted agent(s) & interactions -->
<!--     with the system -->

----
## STRIDE Threat Modeling

![](stride.png)
<!-- .element: class="stretch" -->

* A systematic approach to identifying threats (i.e., attacker actions)
  * Construct an architectural diagram with components & connections
  * Designate the trust boundary 
  * For each untrusted component/connection, identify potential threats
  * For each potential threat, devise a mitigation strategy

[More info: STRIDE approach](https://docs.microsoft.com/en-us/archive/msdn-magazine/2006/november/uncover-security-design-flaws-using-the-stride-approach)

----
## STRIDE: College Admission

![](admission-threat-model.jpg)
<!-- .element: class="stretch" -->

* Spoofing: ?
* Tampering: ? 
* Information disclosure: ?
* Denial of service: ?

----
## STRIDE: College Admission

![](admission-threat-model.jpg)
<!-- .element: class="stretch" -->

* Spoofing: Attacker pretends to be another applicant by logging in
* Tampering: Attacker modifies applicant info using browser exploits
* Information disclosure: Attacker intercepts HTTP requests from/to
    server to read applicant info
* Denial of service: Attacker creates a large number of bogus
    accounts and overwhelms system with requests

----
## STRIDE: Mitigations

![](admission-threat-model.jpg)
<!-- .element: class="stretch" -->

* Spoofing: Attacker pretends to be another applicant by logging in -> __Require stronger passwords__
* Tampering: Attacker modifies applicant info using browser exploits -> __Add server-side security tokens__
* Information disclosure: Attacker intercepts HTTP requests from/to server to read applicant info -> __Use encryption (HTTPS)__
* Denial of service: Attacker creates many bogus accounts and overwhelms system with requests -> __Limit requests per IP address__

----
## STRIDE & Other Threat Modeling Methods

![](stride.png)

* A systematic approach to identifying threats & attacker actions
* Limitations:
  * May end up with a long list of threats, not all of them critical
  * False sense of security: STRIDE does not imply completeness!
* Consider cost vs. benefit trade-offs: Implementing mitigations add
    to development cost and complexity
	* Focus on most critical/likely threats


---
# Threat Modeling for ML 

----
## ML Attacker Goal

* Confidentiality attacks: Exposure of sensitive data
<!-- .element: class="fragment" -->
  * Infer a sensitive label for a data point (e.g., hospital record)
  <!-- .element: class="fragment" -->
* Integrity attacks: Unauthorized modification of data
<!-- .element: class="fragment" -->
  * Induce a model to misclassify data points from one class to another
  <!-- .element: class="fragment" -->
  * e.g., Spam filter: Classify a spam as a non-spam
  <!-- .element: class="fragment" -->
* Availability attacks: Disruption to critical services
<!-- .element: class="fragment" -->
  * Reduce the accuracy of a model
  <!-- .element: class="fragment" -->
  * Induce a model to misclassify many data points
  <!-- .element: class="fragment" -->

----
## ML Attacker Capability

![](ml-cycle.png)

* Knowledge: Does the attacker have access to the model?
  * Training data? Learning algorithm used? Parameters?
* Attacker actions:
  * Training time: __Poisoning attacks__
  * Inference time: __Evasion attacks__, __model inversion attacks__

<!-- references -->
_Understanding Machine Learning_, Bhogavalli (2019)

----
## Poisoning Attacks: Availability

![](virus.png)

* Availability: Inject mislabeled training data to damage model
quality
  <!-- .element: class="fragment" -->
  * 3% poisoning => 11% decrease in accuracy (Steinhardt, 2017)
* Attacker must have some access to the training set
    <!-- .element: class="fragment" -->
  * e.g., models trained on public data set (e.g., ImageNet)
* Example: Anti-virus (AV) scanner
  <!-- .element: class="fragment" -->
  * Online platform for submission of potentially malicious code
  * Some AV company (allegedly) poisoned competitor's model
  

----
## Poisoning Attacks: Integrity

![](spam.jpg)

* Insert training data with seemingly correct labels
* More targeted than availability attacks
  * Cause misclassification from one specific class to another

<!-- references -->
_Poison Frogs! Targeted Clean-Label Poisoning Attacks on Neural
Networks_, Shafahi et al. (2018)

----
## Defense against Poisoning Attacks

* __Q. How would you mitigate poisoning attacks?__

----
## Defense against Poisoning Attacks

![](data-sanitization.png)

* Anomaly detection & data sanitization
<!-- .element: class="fragment" -->
  * Identify and remove outliers in training set (see [data quality lecture](https://ckaestne.github.io/seai/F2020/slides/11_dataquality/dataquality.html#/3))
  * Identify and understand drift from telemetry
* Quality control over your training data
  <!-- .element: class="fragment" -->
  * Who can modify or add to my training set? Do I trust the data
  source?
  * Use security mechanisms (e.g., authentication) and logging to
    track data provenance

<!-- references -->
_Stronger Data Poisoning Attacks Break Data Sanitization Defenses_,
Koh, Steinhardt, and Liang (2018).

----
## Evasion Attacks (Adversarial Examples)

![](evasion-attack.png)

* Add noise to an existing sample & cause misclassification
<!-- .element: class="fragment" -->
* Attack at inference time
<!-- .element: class="fragment" -->
  * Typically assumes knowledge of the model (algorithm, parameters)
  * Recently, shown to be possible even when the attacker only has access to
    model output ("blackbox" attack)

<!-- references -->
_Accessorize to a Crime: Real and Stealthy Attacks on State-of-the-Art
Face Recognition_, Sharif et al. (2016).

----
## Evasion Attacks: Another Example

![](stop-sign-attacks.png)

<!-- references -->
_Robust Physical-World Attacks on Deep Learning Visual
Classification_,
Eykholt et al., in CVPR (2018).

----
## Task Decision Boundary vs Model Boundary

[![Decision boundary vs model boundary](decisionboundary.png)](decisionboundary.png)

* Decision boundary: Ground truth; often unknown and not specifiable
* Model boundary: What is learned; an _approximation_ of
decision boundary

<!-- references -->
From Goodfellow et al (2018). [Making machine learning robust against adversarial inputs](https://par.nsf.gov/servlets/purl/10111674). *Communications of the ACM*, *61*(7), 56-66. 

----
## Defense against Evasion Attacks

* __Q. How would you mitigate evasion attacks?__

----
## Defense against Evasion Attacks

![](stop-sign.png)

* Adversarial training
  <!-- .element: class="fragment" -->
  * Generate/find a set of adversarial examples
  * Re-train your model with correct labels
* Input sanitization
    <!-- .element: class="fragment" -->
  * "Clean" & remove noise from input samples 
  * e.g., Color depth reduction, spatial smoothing, JPEG compression
* Redundancy: Design multiple mechanisms to detect an attack
  <!-- .element: class="fragment" -->
  * Stop sign: Insert a barcode as a checksum; harder to bypass


<!-- references -->
_Reliable Smart Road Signs_, Sayin et al. (2019).

----
## Generating Adversarial Examples

* Q. How do we generate adversarial examples?
  
----
## Generating Adversarial Examples

* See [counterfactual explanations](https://ckaestne.github.io/seai/F2020/slides/17_explainability/explainability.html#/7/1)
* Find similar inputs with different predictions
  - Can be targeted (specific prediction) or  untargeted (any wrong prediction)
* Many similarity measures (e.g., change one feature vs small changes to many features) 
  - $x^* = x + arg min \\{ |\epsilon| : f(x+\epsilon)  \neq f(x) \\}$
* Attacks more effective with access to model internals, but black-box
  attacks also feasible 
  - With model internals: Follow the model's gradient
  - Without model internals: Learn [surrogate model](https://ckaestne.github.io/seai/F2020/slides/17_explainability/explainability.html#/6/2)
  - With access to confidence scores: Heuristic search (e.g., hill climbing)

----
## Model Inversion: Confidentiality

![](model-inversion-image.png)

* Given a model output (e.g., name of a person), infer the
corresponding, potentially sensitive input (facial image of the
person)
* One method: Gradient descent on input space
  * Assumes that the model produces a confidence score for prediction
  * Start with a random input vector & iterate towards input values
    with higher confidence level

<!-- references -->
_Model Inversion Attacks that Exploit Confidence Information and Basic
Countermeasures_, M. Fredrikson et al. in CCS (2015).

----
## Defense against Model Inversion Attacks

![](differential-privacy-example.png)

* Limit attacker access to confidence scores
  * e.g., reduce the precision of the scores by rounding them off
  * But also reduces the utility of legitimate use of these scores!
* Differential privacy in ML
	* Limit what attacker can learn about the model (e.g., parameters)
      based on an individual training sample
	* Achieved by adding noise to input or output (e.g., DP-SGD)
	* More noise => higher privacy, but also lower model accuracy!

<!-- references -->
_Biscotti: A Ledger for Private and Secure Peer-to-Peer Machine
Learning_, M. Shayan et al., arXiv:1811.09904 (2018).

----
## Breakout: Dashcam System

![](dashcam-architecture.jpg)
<!-- .element: class="stretch" -->

* Recall: Dashcam system from I2
* Post on #lecture in Slack:
  * What are the security requirements?
  * What are possible (ML) attacks on the system?
  * What are some possible mitigations against these attacks?

<!-- ---- -->
<!-- ## Breakout: Home Assistant Robot -->

<!-- ![](home-assistant-robot.png) -->
<!-- <\!-- .element: class="stretch" -\-> -->

<!-- * Dialogue system to interact with family members -->
<!-- * Use perception & speech to identify the person -->
<!-- * Notify owner if stranger detected in the house -->
<!-- * Log & upload interactions; re-train & update models for all robots -->

<!-- ---- -->
<!-- ## Breakout: Home Assistant Robot -->

<!-- ![](home-robot-architecture.png) -->
<!-- <\!-- .element: class="stretch" -\-> -->

<!-- * What are the security requirements? -->
<!-- * What are possible attacks on the system? -->
<!-- * How can we defend against some of them? -->

----
## State of ML Security

![](arms-race.jpg)

* On-going arms race (mostly among researchers)
  <!-- .element: class="fragment" -->
  * Defenses proposed & quickly broken by noble attacks
* Assume ML component is likely vulnerable
  <!-- .element: class="fragment" -->
  * Design your system to minimize impact of an attack
* Remember: There may be easier ways to compromise system
  <!-- .element: class="fragment" -->
  * e.g., poor security misconfiguration (default password), lack of
    encryption, code vulnerabilities, etc., 

---
# Designing for Security

----
## Security Mindset

![](security-phone.jpg)

* Assume that all components may be compromised at one point or
another
* Don't assume users will behave as expected; assume all inputs to the system as potentially malicious
* Aim for risk minimization, not perfect security; reduce the chance of catastrophic
  failures from attacks

----
## Secure Design Principles 

* Principle of least privilege
  * A component should be given the minimal privileges needed to fulfill its functionality
* Isolation/compartmentalization
  * Components should be able to interact with each other no more than
  necessary
  * Components should treat inputs from each other as potentially
  malicious
*  Goal: Minimize the impact of a compromised component on the rest of
   the system
   * In poor system designs, vulnerability in one component => entire
     system compromised!

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
## Example: Vehicle Security

![](can-bus.png)

* Research project from UCSD: Remotely taking over vehicle control
  * Create MP3 with malicious code & burn onto CD
  * Play CD => send malicious commands to brakes, engine, locks...
* Problem: Over-privilege & lack of isolation!
  * In traditional vehicles, components share a common CAN bus
  * Anyone can broadcast & read messages

<!-- references -->
_Comprehensive Experimental Analyses of Automotive Attack Surfaces_, Checkoway et al., in USENIX Security (2011).

<!-- ---- -->
<!-- ## Example: Mail Client -->

<!-- * Requirements -->
<!-- <\!-- .element: class="fragment" -\-> -->
<!--   * Receive & send email over external network -->
<!--   * Place incoming email into local user inbox files -->
<!-- * Sendmail -->
<!--   <\!-- .element: class="fragment" -\-> -->
<!--   * Monolithic design; entire program runs as UNIX root -->
<!--   * Historical source of many vulnerabilities -->
<!-- * Qmail: “Security-aware” mail agent -->
<!--   <\!-- .element: class="fragment" -\-> -->
<!--   * Compartmentalized design -->
<!--   * Isolation based on OS process isolation -->
<!-- 	* Separate modules run as separate “users” (UID) -->
<!-- 	* Mutually distrusting processes -->
<!--   * Least privilege  -->
<!-- 	* Minimal privileges for each UID; access to specific resources (files, network sockets, …) -->
<!-- 	* Only one “root” user (with all privileges) -->

<!-- ---- -->
<!-- ## Qmail Architecture -->

<!-- ![](qmail1.png) -->

<!-- ---- -->
<!-- ## Qmail Architecture -->

<!-- ![](qmail2.png) -->

<!-- ---- -->
<!-- ## Qmail Architecture -->

<!-- ![](qmail3.png) -->

<!-- * Component running as root much smaller than in sendmail; much easier to test & verify that it's free of vulnerabilities -->

----
## Secure Design Principles for ML

* Principle of least privilege
  * Who has access to training data, model internal, system input &
  output, etc.,?
  * Does any user/stakeholder have more access than necessary?
	* If so, limit access by using authentication mechanisms

![](ml-components.png)

----
## Secure Design Principles for ML

* Principle of least privilege
  * Who has access to training data, model internal, system input &
  output, etc.,?
  * Does any user/stakeholder have more access than necessary?
	* If so, limit access by using authentication mechanisms
* Isolation & compartmentalization
<!-- .element: class="fragment" -->
	* Can a security attack on one ML component (e.g., misclassification)
  adversely affect other parts of the system?
	  * If so, compartmentalize or build in mechanisms to limit
        impact (see [risk mitigation strategies](https://ckaestne.github.io/seai/F2020/slides/09_risks_ii/risks_ii.html#/3))
* Monitoring & detection:
<!-- .element: class="fragment" -->
  * Look for odd shifts in the dataset and clean the data if needed (for poisoning attacks)
  * Assume all system input as potentially malicious & sanitize
    (evasion attacks)


---
# AI for Security

----
[![Article: 30 COMPANIES MERGING AI AND CYBERSECURITY TO KEEP US SAFE AND SOUND](30aisec.png)](https://builtin.com/artificial-intelligence/artificial-intelligence-cybersecurity)
<!-- .element: class="stretch" -->

----
## Many Defense Systems use Machine Learning

* Classifiers to learn malicious content
  - Spam filters, virus detection
* Anomaly detection
  - Identify unusual/suspicious activity, eg. credit card fraud, intrusion detection
  - Often unsupervised learning, e.g. clustering
* Game theory
  - Model attacker costs and reactions, design countermeasures
* Automate incidence response and mitigation activities
  - Integrated with DevOps
* Network analysis
  - Identify bad actors and their communication in public/intelligence data
* Many more, huge commercial interest

<!-- references -->
Recommended reading: Chandola, Varun, Arindam Banerjee, and Vipin Kumar. "[Anomaly detection: A survey](http://cucis.ece.northwestern.edu/projects/DMS/publications/AnomalyDetection.pdf)." ACM computing surveys (CSUR) 41, no. 3 (2009): 1-58.  

----
## AI Security Solutions are AI-Enabled Systems Too

* AI/ML component one part of a larger system
* Consider entire system, from training to telemetry, to user interface, to pipeline automation, to monitoring
* AI-based security solutions can be attacked themselves

----
![Equifax logo](equifax.png)

Note: One contributing factor to the Equifax attack was an expired certificate for an intrusion detection system









---
# Summary

* Security requirements: Confidentiality, integrity, availability
* Threat modeling to identify security requirements & attacker capabilities
* ML-specific attacks on training data, telemetry, or the model
  - Poisoning attack on training data to influence predictions
  - Evasion attacks to shape input data to achieve intended
  predictions (adversarial learning)
  - Model inversion attacks for privacy violations
* Security design at the system level
  - Principle of least privilege
  - Isolation & compartmentalization 
* AI can be used for defense (e.g. anomaly detection)
* __Key takeaway__: Adopt a security mindset! Assume all components may be vulnerable in one way or another. Design your system to explicitly reduce the impact of potential attacks
