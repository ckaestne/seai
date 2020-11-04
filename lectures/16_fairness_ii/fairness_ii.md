---
author: Eunsuk Kang
title: "17-445: Fairness Continued"
semester: Fall 2020
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---

# Fairness: Beyond Model

Eunsuk Kang

<!-- references -->

Required reading: Os Keyes, Jevan Hutson, Meredith Durbin. [A Mulching Proposal: Analysing and Improving an Algorithmic System for Turning the Elderly into High-Nutrient Slurry](https://dl.acm.org/doi/pdf/10.1145/3290607.3310433). CHI Extended Abstracts, 2019.

---
# Learning Goals

* Consider achieving fairness in AI-based systems as an activity throughout the entire development cycle
* Understand the role of requirements engineering in selecting ML
  fairness criteria
* Understand the process of constructing datasets for fairness
* Consider the potential impact of feedback loops on AI-based systems
  and need for continuous monitoring

---
# Fairness Criteria: Review

----
## Review of Criteria so far:

*Recidivism scenario: Should a person be detained?*

* Anti-classification: ?
* Independence: ?
* Separation: ?

<!-- split -->

![Courtroom](courtroom.jpg)

----
## Review of Criteria so far:

*Recidivism scenario: Should a defendant be detained?*

* Anti-classification: Race and gender should not be considered for the decision at all
* Independence: Detention rates should be equal across gender and race groups
* Separation: Among defendants who would not have gone on to commit a
violent crime if released, detention rates are equal across gender and race groups







---
# Building Fair ML Systems

----
## Fairness must be considered throughout the ML lifecycle!

![](fairness-lifecycle.jpg)

<!-- references -->

_Fairness-aware Machine Learning_, Bennett et al., WSDM Tutorial (2019).


----
## Practitioner Challenges

* Fairness is a system-level property
  - consider goals, user interaction design, data collection, monitoring, model interaction (properties of a single model may not matter much)
* Fairness-aware data collection, fairness testing for training data
* Identifying blind spots
  - Proactive vs reactive
  - Team bias and (domain-specific) checklists
* Fairness auditing processes and tools
* Diagnosis and debugging (outlier or systemic problem? causes?)
* Guiding interventions (adjust goals? more data? side effects? chasing mistakes? redesign?)
* Assessing human bias of humans in the loop


<!-- references -->
Holstein, Kenneth, Jennifer Wortman Vaughan, Hal Daumé III, Miro Dudik, and Hanna Wallach. "[Improving fairness in machine learning systems: What do industry practitioners need?](http://users.umiacs.umd.edu/~hal/docs/daume19fairness.pdf)" In Proceedings of the 2019 CHI Conference on Human Factors in Computing Systems, pp. 1-16. 2019.






---
# Requirements for Fairness

----
## Machine Learning Cycle

![](ml-cycle.png)

<!-- references -->

"Fairness and Machine Learning" by Barocas, Hardt,
and Narayanan (2019), Chapter 1.



----
## Recall: Machine vs World

![](machine-world.png)

* No ML/AI lives in vacuum; every system is deployed as part of the world
* A requirement describes a desired state of the world (i.e., environment)
* Machine (software) is _created_ to manipulate the environment into
this state


----
## Requirement vs Specification

![requirement-vs-spec](env-spec.png)

* Requirement (REQ): What the system should do, as desired effects on the environment
* Assumptions (ENV): What’s assumed about the behavior/properties of
  the environment (based on domain knowledge)
* Specification (SPEC): What the software must do in order to satisfy REQ


----
## Requirements for Fair ML Systems

* Identify requirements (REQ) over the environment
	* What types of harm can be caused by biased decisions?
	* Who are stakeholders? Which population groups can be harmed?
	* Are we trying to achieve equality vs. equity? 
	* What are legal requirements to consider?

----
## "Four-fifth rule" (or "80% rule")

$(P[R = 1 | A = a]) / (P[R = 1 | A = b]) \geq 0.8$

* Selection rate for a protected group (e.g., $A = a$) <
80% of highest rate => selection procedure considered as having "adverse
impact"
* Guideline adopted by Federal agencies (Department of Justice, Equal
  Employment Opportunity Commission, etc.,) in 1978
* If violated, must justify business necessity (i.e., the selection procedure is
  essential to the safe & efficient operation)
* Example: Hiring
  * 50% of male applicants vs 20% female applicants hired
  (0.2/0.5 = 0.4)
  * Is there a business justification for hiring men at a higher rate?
  

----
## Example: Loan Application

![](loans.jpg)

* Who are the stakeholders?
* Types of harm?
* Legal & policy considerations?

----
## Requirements for Fair ML Systems

* Identify requirements (REQ) over the environment
	* What types of harm can be caused by biased decisions?
	* Who are stakeholders? Which population groups can be harmed?
	* Are we trying to achieve equality vs. equity? 
	* What are legal requirements to consider?
* Define the interface between the environment & machine (ML)
	* What data will be sensed/measured by AI? Potential biases?
	* What types of decisions will the system make? Punitive or assistive?
* Identify the environmental assumptions (ENV)
	* Adversarial? Misuse? Unfair (dis-)advantages?
	* Population distributions?

----
## Example: Loan Application
 
![](loans.jpg)

* Do certain groups of stakeholders have unfair (dis-)advantages? 
* What are potential biases in the data measured by the system?
  
----
## Requirements for Fair ML Systems

* Identify requirements (REQ) over the environment
	* What types of harm can be caused by biased decisions?
	* Who are stakeholders? Which population groups can be harmed?
	* Are we trying to achieve equality vs. equity? 
	* What are legal requirements to consider?
* Define the interface between the environment & machine (ML)
	* What data will be sensed/measured by AI? Potential biases?
	* What types of decisions will the system make? Punitive or assistive?
* Identify the environmental assumptions (ENV)
  * Adversarial? Misuse? Unfair (dis-)advantages?
  * Population distributions?
* Devise machine specifications (SPEC) that are sufficient to establish REQ
	* What type of fairness definition is appropriate?

----
## Recall: Equality vs Equity

![Contrasting equality, equity, and justice](eej2.png)

----
## Type of Decision & Possible Harm

* If decision is _punitive_ in nature:
  * e.g. decide whom to deny bail based on risk of recidivism
  * Harm is caused when a protected group is given an unwarranted penalty
  * Heuristic: Use a fairness metric (separation) based on __false positive rate__
* If decision is _assistive_ in nature:
  * e.g., decide who should receive a loan or a food subsidy
  * Harm is caused when a group in need is incorrectly denied assistance
  * Heuristic: Use a fairness metric based on __false negative rate__

----
## Which fairness criteria?

![Courtroom](courtroom.jpg)

<!-- split -->

* Decision: Classify whether a defendant should be detained
* Criteria: Anti-classification, independence, or seperation w/ FPR or FNR?

----
## Which fairness criteria?

![](loans.jpg)

* Decision: Classify whether an applicant should be granted a loan. 
* Criteria: Anti-classification, independence, or seperation w/ FPR or FNR?

----
## Which fairness criteria?

![](mri.jpg)

* Decision: Classify whether a patient has a high risk of cancer
* Criteria: Anti-classification, independence, or seperation w/ FPR or FNR?

----
## Fairness Tree

![fairness-tree](fairness_tree.png)

For details on other types of fairness metrics, see:
https://textbook.coleridgeinitiative.org/chap-bias.html





---
# Dataset Construction for Fairness

----
## Data Bias

![](data-bias-stage.png)

* A __systematic distortion__ in data that compromises its use for a task
* Bias can be introduced at any stage of the data pipeline!

----
## Types of Data Bias

* __Population bias__
* __Behavioral bias__
* Content production bias
* Linking bias
* Temporal bias

<!-- references -->

_Social Data: Biases, Methodological Pitfalls, and Ethical
Boundaries_, Olteanu et al., Frontiers in Big Data (2016).

----
## Population Bias

![](gender-detection.png)

* Differences in demographics between a dataset vs a target population
* Example: Does the Twitter demographics represent the general population?
* In many tasks, datasets should match the target population
* But some tasks require equal representation for fairness (Q. example?)

----
## Behavioral Bias

![](freelancing.png)

* Differences in user behavior across platforms or social contexts
* Example: Freelancing platforms (Fiverr vs TaskRabbit)
  * Bias against certain minority groups on different platforms

<!-- references -->

_Bias in Online Freelance Marketplaces_, Hannak et al., CSCW (2017).

----
## Fairness-Aware Data Collection

* Address population bias
  * Does the dataset reflect the demographics in the target population?
* Address under- & over-representation issues
   * Ensure sufficient amount of data for all groups to avoid being
   treated as "outliers" by ML
   * But also avoid over-representation of certain groups (e.g.,
     remove historical data)
* Data augmentation: Synthesize data for minority groups
  * Observed: "He is a doctor" -> synthesize "She is a doctor"
* Fairness-aware active learning
  * Collect more data for groups with highest error rates 

<!-- references -->

_Fairness-aware Machine Learning_, Bennett et al., WSDM Tutorial (2019).

----
## Data Sheets

![](datasheet.png)

* A process for documenting datasets
* Common practice in the electronics industry, medicine
* Purpose, provenance, creation, __composition__, distribution
  * "Does the dataset relate to people?"
  * "Does the dataset identify any subpopulations (e.g., by age,
  gender)?"

<!-- references -->

_Datasheets for Dataset_, Gebru et al., (2019). https://arxiv.org/abs/1803.09010

----
## Example: Predictive Policing

![Crime Map](crime-map.jpg)


Q. How can we modify an existing dataset or change the data collection
process to reduce bias?




---
# Monitoring and Auditing


----
## Example: Predictive Policing

![Crime Map](crime-map.jpg)

* Model: Use historical data to predict crime rates by neighborhoods
* Increased patrol => more arrested made in neighborhood X
* New crime data fed back to the model
* Repeat...

----
## Feedback Loops

```mermaid
graph LR
  t[biased training data] --> o[biased outcomes]
  o --> m[biased telemetry] 
  m --> t
```

> "Big Data processes codify the past.  They do not invent the future.  Doing that requires moral imagination, and that’s something only humans can provide. " -- Cathy O'Neil in [Weapons of Math Destruction](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/6lpsnm/alma991016462699704436)

----
## Key Problems

* We trust algorithms to be objective, may not question their predictions
* Often designed by and for privileged/majority group
* Algorithms often black box (technically opaque and kept secret from public)
* Predictions based on correlations, not causation; may depend on flawed statistics
* Potential for gaming/attacks
* Despite positive intent, feedback loops may undermine the original goals


<!-- references -->

O'Neil, Cathy. [Weapons of math destruction: How big data increases inequality and threatens democracy](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/6lpsnm/alma991016462699704436). Broadway Books, 2016.

----
## Monitoring Faireness-Aware Model

* Deploying an ML model with a fairness criterion does NOT guarantee
  improvement in equality over time
* __Delayed impact__: Even if a model appears to promote fairness in
short term, it may result harm over a long-term period
	* Example: Independence may result in _over-acceptance_ (i.e.,
    positive classification) of a group, causing unintended
    harm 
* In general, impact of ML fairness criteria on the society is still
poorly understood and difficult to predict
* __Conclusion__: Continuously monitor system for fairness metrics & adjust

<!-- references -->
[Delayed Impact of Fair Machine Learning](https://arxiv.org/abs/1803.04383). Liu
et al., (2018)

----
## Monitoring & Auditing

* Continuously monitor for:
  - Match between training data, test data, and instances that you encounter in deployment
  - Fairness metrics: Is the system yielding fair results over time?
  - Population shifts: May suggest needs to adjust fairness metric/thresholds
  - User reports & complaints: Log and audit system decisions
    perceived to be unfair by users
* Deploy escalation plans: How do you respond when harm occurs due to
system?
	* Shutdown system? Temporary replacement?
	* Maintain communication lines to stakeholders
* Invite diverse stakeholders to audit system for biases

----
## Monitoring Tools: Example

![](aequitas.png)

http://aequitas.dssg.io/

----
## Monitoring Tools: Example

![](aequitas-report.png)

* Continuously make fairness measurements to detect potential shifts
  in data, population behavior, etc.,

----
## Monitoring Tools: Example

![](aequitas-process.png)

* Involve policy makers in the monitoring & auditing process

---
## Fairness Checklist

![](checklist-excerpt.png)

<!-- references -->

[_Co-Designing Checklists to Understand Organizational
Challenges and Opportunities around Fairness in AI_](http://www.jennwv.com/papers/checklists.pdf), Madaio et al (2020).

---
## Case Study: College Admission

![](college-admission.jpg)

* Aspects to consider:
  * Requirements & fairness criteria selection
  * Data collection & pre-processing
  * Impact of feedback loops
  * Monitoring & auditing

---
# Summary

* Achieving fairness as an activity throughout the entire development cycle
* Requirements engineering for fair ML systrems
  * Stakeholders, sub-populations & unfair (dis-)advantages
  * Types of harms
  * Legal requirements
* Dataset construction for fairness
* Consideration for the impact of feedback loops
* Continous montoring & auditing for fairness

