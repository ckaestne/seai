---
author: Eunsuk Kang
title: "17-445: Fairness Continued"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---  

# Fairness: Definitions and Measurements

Eunsuk Kang

<!-- references -->

Required reading:"Fairness and Machine Learning" by Barocas, Hardt,
and Narayanan (2019), Chapter 1.

---
# Learning Goals

* Understand different definitions of fairness
* Discuss methods for measuring fairness

---
# Fairness: Definitions

----
### Fairness is still an actively studied & disputed concept!

![](fairness-papers.jpeg)

----
## Fairness: Definitions

* Fairness through Blindness
* Group fairness
* Equalized odds
* Predictive rate parity

----
## Fairness through Blindness

![](justice.jpeg)

* Ignore/eliminate sensitive attributes from dataset
* Example: Remove gender or race from a credit card scoring system
* __Q. Why is this potentially a bad idea__?

----
## Fairness through Blindness

![](justice.jpeg)

* Ignore/eliminate sensitive attributes from dataset
* __Q. Why is this potentially a bad idea__?
  * Sensitive attributes may be correlated with other features
  * Some ML tasks need sensitive attributes (e.g., medical diagnosis)

----
## Notations

* $X$: Feature set (e.g., age, race, education, region, income, etc.,)  
* $A$: Sensitive attribute (race)
* $R$: Regression score (predicted likelihood of recidivism)
  * $Y'$ = 1 if and only if $R$ is greater than some threshold $T$
* $Y$: Target variable (Did the person actually commit recidivism?)

----
## Group Fairness

$P[R = 1 | A = a]  = P[R = 1 | A = b]$

* Also called _statistical parity_, _demographic parity_, or the
  _independence_ criterion
* Mathematically, $R \perp A$
  * Prediction must be independent of the sensitive attribute
* Example: The predicted rate of recidivism is the same across all races
  <!-- .element: class="fragment" -->
* Q. What are limitations of group fairness?
  <!-- .element: class="fragment" -->
  * Ignores possible correlation between $Y$ and $A$
    <!-- .element: class="fragment" -->
	* Rules out perfect predictor $R = Y$ when $Y$ & $A$ are correlated
  * Permits laziness: Intentionally give high ratings to
  random people in one group
    <!-- .element: class="fragment" -->
* Q. But does this mean group fairness should never be used?
  <!-- .element: class="fragment" -->

----
## Equalized Odds

$P[R=0∣Y=1,A=a] = P[R=0∣Y=1,A=b]$
$P[R=1∣Y=0,A=a] = P[R=1∣Y=0,A=b]$

* Also called the _separation_ criterion
* $R \perp A | Y$
  * Prediction must be independent of the sensitive attribute
  _conditional_ on the target variable

----
## Review: Confusion Matrix

![](confusion-matrix.jpg)

Can we explain equalize odds in terms of errors?

$P[R=0∣Y=1,A=a] = P[R=0∣Y=1,A=b]$
$P[R=1∣Y=0,A=a] = P[R=1∣Y=0,A=b]$

----
## Equalized Odds

$P[R=0∣Y=1,A=a] = P[R=0∣Y=1,A=b]$
$P[R=1∣Y=0,A=a] = P[R=1∣Y=0,A=b]$

* Also called the _separation_ criterion
* $R \perp A | Y$
  * Prediction must be independent of the sensitive attribute
    _conditional_ on the target variable
* i.e., All groups experience the same false positive & negative rates
<!-- .element: class="fragment" -->
* Example: Credit card rating
<!-- .element: class="fragment" -->
  * R: Credit card score, A: Gender of applicant: Y: Actual credit behavior
  * A person with good (bad) credit behavior score should be assigned a
    good (bad) score, regardless of gender
* Q. What are advantages of equalized odds vs group fairness?
<!-- .element: class="fragment" -->
* Q. What are potential limitations of equalized odds?
<!-- .element: class="fragment" -->

----
## Predictive Rate Parity

$P[Y=1∣R=1,A=a] = P[Y=1∣R=1,A=b]$
$P[Y=0∣R=0,A=a] = P[Y=0∣R=0,A=b]$

* Also called the _sufficiency_ criterion
* $Y \perp A | R$
  *  Target variable must be independent of the sensitive attribute
    _conditional_ on the prediction
* i.e., $R$ is alone sufficient to identify $Y$; no need to see $A$
<!-- .element: class="fragment" -->

----
## Review: Recall vs Precision

![](confusion-matrix-full.jpg)

* Precision, or __Positive Predictive Value (PPV)__: How many of
  positively classified cases actually turned out to be positive?

----
## Predictive Rate Parity

$P[Y=1∣R=1,A=a] = P[Y=1∣R=1,A=b]$
$P[Y=0∣R=0,A=a] = P[Y=0∣R=0,A=b]$

* Also called the _sufficiency_ criterion
* $Y \perp A | R$
  *  Target variable must be independent of the sensitive attribute
    _conditional_ on the prediction
* i.e., $R$ is alone sufficient to identify $Y$; no need to see $A$
  * or, __the model is equally precise across all groups__
* Example: Credit card rating
<!-- .element: class="fragment" -->
  * R: Credit card score, A: Gender of applicant: Y: Actual credit behavior
  * A person with a good (bad) predicted score should have good (bad)
    credit behavior, regardless of gender
* Q. What are potential limitations of predictive rate parity?
<!-- .element: class="fragment" -->

----
## Impossibility Results

* Any two of the three definitions cannot be achieved simultaneously!
* e.g., Impossible to achieve equalized odds and predictive rate parity
  * $R \perp A | Y$ and $Y \perp A | R$ can't be true at the same time
  * Unless $A \perp Y$ 
  * Formal proofs: Chouldechova (2016), Kleinberg et al. (2016)

----
## Case Study: Cancer Diagnosis

![](mri.jpg)

----
## Exercise: Cancer Diagnosis

![](cancer-stats.jpg)

* 1000 data samples (500 male & 500 female patients)
* What's the overall recall & precision?
* Does the model achieve:
  * Group fairness? Equalized odds? Predictive rate parity?
* What can we conclude about the model & its usage?  

---
# Achieving Fairness Criteria

----
## Can we achieve fairness during the learning process?

* Pre-processing:
  * Clean the dataset to reduce correlation between the feature set
    and sensitive attributes
* Training time constraint
  * ML is a constraint optimization problem (minimize errors)
  * Impose additional parity constraint into ML optimization process
* Post-processing
  * Adjust the learned model to be uncorrelated with sensitive attributes
* (Still active area of research! Many new techniques published each year)

----
## Trade-offs: Accuracy vs Fairness

![](fairness-accuracy.jpeg)

* In general, accuracy is at odds with fairness
  * e.g., Impossible to achieve perfect accuracy ($R = Y$) while
  ensuring group parity

<!-- references -->

_Fairness Constraints: Mechanisms for Fair Classification_, Zafar et
al., AISTATS (2017).
  
---
# Building Fair ML Systems

----
## Fairness must be considered throughout the ML lifecycle!

![](fairness-lifecycle.jpg)

<!-- references -->

_Fairness-aware Machine Learning_, Bennett et al., WSDM Tutorial (2019).

---
# Requirements and Fairness

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

* Requirement (REQ): What customer needs, as desired effects on the environment
* Assumptions (ENV): What’s assumed about the behavior/properties of
  the environment (based on domain knowledge)
* Specification (SPEC): What machine must do in order to satisfy REQ

----
## Requirements for Fair ML Systems

1. Identify all environmental entities
<!-- .element: class="fragment" -->
  * Consider all stakeholders, their backgrounds & characteristics
2. State requirement (REQ) over the environment
<!-- .element: class="fragment" -->
   * What kind of harms are relevant/possible?
   * Requirements as the prevention/reduction of harm
3. Identify the interface between the environment & machine (ML)
<!-- .element: class="fragment" -->
  * What types of data will be sensed/measured by AI?
  * What types of actions will be performed by AI?
4. Identify the environmental assumptions (ENV)
<!-- .element: class="fragment" -->
	* How do the stakeholders interact with the ML?
	* Adversarial? Unintentional misuse?  
5. Develop software specifications (SPEC) that are sufficient to
establish REQ
<!-- .element: class="fragment" -->
	* What type of fairness definition should we try to achieve?
6. Test whether ENV ∧ SPEC ⊧ REQ
<!-- .element: class="fragment" -->
	* Continually monitor the fairness metrics and user reports
7. If NO, strengthen SPEC & repeat Step 6
<!-- .element: class="fragment" -->
	* Re-examine & modify the dataset to reduce bias

----
## Case Study: College Admission

![](college-admission.jpg)

* Who are the stakeholders (i.e., environmental entities)?
* Types of harm? 
* Assumptions about the stakeholder behavior? 
* Data measured by AI? Actions performed by AI?
* What type of fairness definition is appropriate?

---
# Summary

* Definitions of fairness
  * Group fairness, equalized odds, predictive parity
* Achieving fairness
  * Trade-offs between accuracy & fairness
* Requirements for fair ML systems
