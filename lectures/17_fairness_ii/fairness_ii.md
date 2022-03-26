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
* Consider the potential impact of feedback loops on AI-based systems
  and need for continuous monitoring


---
# Building Fair ML Systems

Fairness must be considered throughout the ML lifecycle!

![](fairness-lifecycle.jpg)

<!-- references -->

_Fairness-aware Machine Learning_, Bennett et al., WSDM Tutorial (2019).


---
# Fairness Definitions: Review


----
## Review of definitions so far:

*Recidivism scenario: Should a person be detained?*

* Anti-classification: ?
* Independence: ?
* Separation: ?

<!-- split -->

![Courtroom](courtroom.jpg)
<!-- .element: class="stretch" -->


----
## Review of definitions so far:

*Recidivism scenario: Should a defendant be detained?*

* Anti-classification: Race and gender should not be considered for the decision at all
* Independence: Detention rates should be equal across gender and race groups
* Separation: Among defendants who would not have gone on to commit a
violent crime if released, detention rates are equal across gender and race groups


----
## Recidivism Revisited

![](recidivism-propublica.png)

* COMPAS system, developed by Northpointe
	* Used by judges in sentencing decisions
	* In deployment throughout numerous states (PA, FL, NY, WI, CA, etc.,)

<!-- references -->

[ProPublica article](https://www.propublica.org/article/machine-bias-risk-assessments-in-criminal-sentencing)


----
## Which fairness definition?

![](compas-metrics.png)

* ProPublica investigation: COMPAS violates separation w/ FPR & FNR
* Northpointe response: COMPAS is fair because it has similar FDRs
  across both races
  * FDR = FP / (FP + TP) = 1 - Precision
  * FPR = FP / (FP + TN)
* __Q. So is COMPAS both fair & unfair at the same time? Which definition
  is the "right" one?__

<!--references -->

[Figure from Big Data and Social Science, Ch. 11](https://textbook.coleridgeinitiative.org/chap-bias.html#ref-angwin2016b)


----
## Fairness Definitions: Pitfalls 

![](fairness-accuracy.jpeg)
<!-- .element: class="stretch" -->

* Easy to pick some definition & claim that the model is fair
  * But is the __overall system__ actually fair?
  * What are the root causes of bias in the first place?
* In general, impossible to satisfy multiple fairness definitions at
once
	* Also consider trade-offs against accuracy & other system goals
* Fairness is a __context-dependent__ notion!
	* Select the criteria that minimize harm for the given context


---
# Requirements Engineering for Fairness


----
## Recall: Machine vs World

![](machine-world.png)

* No ML/AI lives in vacuum; every system is deployed as part of the world
* A requirement describes a desired state of the world (i.e., environment)
* Machine (software) is _created_ to manipulate the environment into
this state

<!-- ---- -->
<!-- ## Requirements & Fairness -->

<!-- ![](machine-world.png) -->
<!-- <\!-- .element: class="stretch" -\-> -->

<!-- * Fairness is a __context-dependent__ notion -->
<!-- * __Again, think about requirements!__ -->
<!--   * Who are the stakeholders of the system? -->
<!-- 	* Which of these groups could be harmed? -->
<!--   * What potential harms can be caused by biased decisions? -->
<!-- 	* e.g., unfair punishments, denial to resources -->
<!--   * Are there any legal constraints or policy goals? -->
<!-- 	* e.g., 80% rule, affirmative actions  -->
<!--   * How are these decisions related to the ML model? Errors? -->
<!-- 	* e.g., false positives, false negatives -->
<!--   * Which fairness metric minimizes the harm? -->


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
## Recall: Equality vs Equity

![Contrasting equality, equity, and justice](eej2.jpeg)


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

<!-- ---- -->
<!-- ## Which fairness criteria? -->

<!-- ![Courtroom](courtroom.jpg) -->

<!-- <\!-- split -\-> -->

<!-- * Decision: Classify whether a defendant should be detained -->
<!-- * Criteria: Anti-classification, independence, or seperation w/ FPR or FNR? -->

----
## Which fairness criteria?

![](loans.jpg)

* Decision: Should an applicant be granted a loan?
* What kind of harm can be caused? Punitive or assistive?
* Criteria: Anti-classification, independence, or seperation w/ FPR or FNR?

----
## Which fairness criteria?

![](mri.jpg)

* Decision: Does the patient has a high risk of cancer?
* What kind of harm can be caused? Punitive or assistive?
* Criteria: Anti-classification, independence, or seperation w/ FPR or FNR?

----
## Breakout: Automated Hiring

![](hiring.png)

* Who are the stakeholders? 
* What kind of harm can be caused?
* Which fairness metric to use?
  * Independence, separation w/ FPR vs. FNR?

----
## Fairness Tree

![fairness-tree](fairness_tree.png)

For details on other types of fairness metrics, see:
https://textbook.coleridgeinitiative.org/chap-bias.html


---
# Feedback Loops


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
## Example: Predictive Policing

![Crime Map](crime-map.jpg)
<!-- .element: class="stretch" -->


* Model: Use historical data to predict crime rates by neighborhoods
* Increased patrol => more arrested made in neighborhood X
* New crime data fed back to the model
* Repeat...

__Q. Other examples?__

----
## Long-term Impact of ML

![](ml-cycle.png)

* ML systems make multiple decisions over time, influence the
behaviors of populations in the real world
* But most models are built & optimized assuming that the world is
static!
* Difficult to estimate the impact of ML over time
  * Need to reason about the system dynamics (world vs machine)
  * e.g., what's the effect of a loan lending policy on a population?

----
## Long-term Impact & Fairness

![](fairness-longterm.png)
* Deploying an ML model with a fairness criterion does NOT guarantee
  improvement in equality over time
* Even if a model appears to promote fairness in
short term, it may result harm over a long-term period

<!-- references -->
[Fairness is not static: deeper understanding of long term fairness via simulation studies](https://dl.acm.org/doi/abs/10.1145/3351095.3372878),
in FAT* 2020.


---
# Monitoring and Auditing

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
## Monitoring & Auditing

![](model_drift.jpg)

* Continously monitor the fairness metric (e.g., error rates for
  different groups)
* Re-train model with new data or adjust classification thresholds if needed
* Recall: Data drifts in the Data Quality lecture

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
# Building Fair ML-Based Systems: Best Practices

----
## START EARLY!

* Think about system goals and relevant fairness concerns
* Analyze risks & harms to affected groups
* Understand environment interactions, attacks, and feedback loops (world vs machine)
* Influence data acquisition
* Define quality assurance procedures
  - separate test sets, automatic fairness measurement, testing in production
  - telemetry design and feedback mechanisms
  - incidence response plan


----
## Best Practices: Task Definition

* Clearly define the task & model’s intended effects
* Try to identify and document unintended effects & biases
* Clearly define any fairness requirements
* *Involve diverse stakeholders & multiple perspectives*
* Refine the task definition & be willing to abort

<!-- references -->

Swati Gupta, Henriette Cramer, Kenneth Holstein, Jennifer Wortman Vaughan, Hal Daumé III, Miroslav Dudík, Hanna Wallach, Sravana Reddy, Jean GarciaGathright. [Challenges of incorporating algorithmic fairness into practice](https://www.youtube.com/watch?v=UicKZv93SOY), FAT* Tutorial, 2019. ([slides](https://bit.ly/2UaOmTG))




----
## Best Practices: Choosing a Data Source

* Think critically before collecting any data
* Check for biases in data source selection process
* Try to identify societal biases present in data source
* Check for biases in cultural context of data source
* Check that data source matches deployment context
* Check for biases in
  * technology used to collect the data
  * humans involved in collecting data
  * sampling strategy
* *Ensure sufficient representation of subpopulations*
* Check that collection process itself is fair & ethical

*How can we achieve fairness without putting a tax on already disadvantaged populations?*

<!-- references -->

Swati Gupta, Henriette Cramer, Kenneth Holstein, Jennifer Wortman Vaughan, Hal Daumé III, Miroslav Dudík, Hanna Wallach, Sravana Reddy, Jean GarciaGathright. [Challenges of incorporating algorithmic fairness into practice](https://www.youtube.com/watch?v=UicKZv93SOY), FAT* Tutorial, 2019. ([slides](https://bit.ly/2UaOmTG))


----
## Best Practices: Labeling and Preprocessing

* Check for biases introduced by
  - discarding data
  - bucketing values
  - preprocessing software
  - labeling/annotation software
  - human labelers
* Data/concept drift?

*Auditing? Measuring bias?*

<!-- references -->

Swati Gupta, Henriette Cramer, Kenneth Holstein, Jennifer Wortman Vaughan, Hal Daumé III, Miroslav Dudík, Hanna Wallach, Sravana Reddy, Jean GarciaGathright. [Challenges of incorporating algorithmic fairness into practice](https://www.youtube.com/watch?v=UicKZv93SOY), FAT* Tutorial, 2019. ([slides](https://bit.ly/2UaOmTG))


----
## Best Practices: Model Definition and Training

* Clearly define all assumptions about model
* Try to identify biases present in assumptions
* Check whether model structure introduces biases
* Check objective function for unintended effects
* Consider including “fairness” in objective function


<!-- references -->

Swati Gupta, Henriette Cramer, Kenneth Holstein, Jennifer Wortman Vaughan, Hal Daumé III, Miroslav Dudík, Hanna Wallach, Sravana Reddy, Jean GarciaGathright. [Challenges of incorporating algorithmic fairness into practice](https://www.youtube.com/watch?v=UicKZv93SOY), FAT* Tutorial, 2019. ([slides](https://bit.ly/2UaOmTG))


----
## Best Practices: Testing & Deployment

* Check that test data matches deployment context
* Ensure test data has sufficient representation
* Continue to involve diverse stakeholders
* Revisit all fairness requirements
* Use metrics to check that requirements are met
*
* Continually monitor
  - match between training data, test data, and instances you
encounter in deployment
  - fairness metrics
  - population shifts
  - user reports & user complaints
* Invite diverse stakeholders to audit system for biases

<!-- references -->

Swati Gupta, Henriette Cramer, Kenneth Holstein, Jennifer Wortman Vaughan, Hal Daumé III, Miroslav Dudík, Hanna Wallach, Sravana Reddy, Jean GarciaGathright. [Challenges of incorporating algorithmic fairness into practice](https://www.youtube.com/watch?v=UicKZv93SOY), FAT* Tutorial, 2019. ([slides](https://bit.ly/2UaOmTG))

----
## Fairness Checklist

![](checklist-excerpt.png)

<!-- references -->

[_Co-Designing Checklists to Understand Organizational
Challenges and Opportunities around Fairness in AI_](http://www.jennwv.com/papers/checklists.pdf), Madaio et al (2020).

---
# Summary

* Achieving fairness as an activity throughout the entire development cycle
* Requirements engineering for fair ML systrems
  * Stakeholders, sub-populations & unfair (dis-)advantages
  * Types of harms
  * Legal requirements
* Consideration for the impact of feedback loops
* Continous montoring & auditing for fairness

