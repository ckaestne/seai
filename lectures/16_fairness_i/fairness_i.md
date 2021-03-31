---
author: Eunsuk Kang
title: "17-445: Fairness Continued"
semester: Fall 2020
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---

# Fairness: Definitions and Measurements

Eunsuk Kang

<!-- references -->

Required reading: Holstein, Kenneth, Jennifer Wortman Vaughan, Hal
Daumé III, Miro Dudik, and Hanna
Wallach. "[Improving fairness in machine learning systems: What do industry practitioners need?](http://users.umiacs.umd.edu/~hal/docs/daume19fairness.pdf)"
In Proceedings of the 2019 CHI Conference on Human Factors in
Computing Systems, pp. 1-16. 2019.

---
# Learning Goals

* Understand different definitions of fairness
* Discuss methods for measuring fairness
* Understand the role of requirements engineering in fair ML systems

---
# Fairness: Definitions

----
### Fairness is still an actively studied & disputed concept!

![](fairness-papers.jpeg)

<!-- references -->
Source: Mortiz Hardt, https://fairmlclass.github.io/

----
## Fairness: Definitions

* Anti-classification (fairness through blindness)
* Independence (group fairness)
* Separation (equalized odds)
* ...and numerous others!

----
## Anti-Classification

![](justice.jpeg)

* Also called _fairness through blindness_
* Ignore/eliminate sensitive attributes from dataset
* Example: Remove gender or race from a credit card scoring system
* __Q. Advantages and limitations__?

----
## Recall: Proxies

*Features correlate with protected attributes*

![](neighborhoods.png)

----
## Recall: Not all discrimination is harmful

![](gender-bias.png)

* Loan lending: Gender discrimination is illegal.
* Medical diagnosis: Gender-specific diagnosis may be desirable.
* Discrimination is a __domain-specific__ concept!

**Other examples?**

----
## Anti-Classification

![](justice.jpeg)

* Ignore/eliminate sensitive attributes from dataset
* Limitations
  * Sensitive attributes may be correlated with other features
  * Some ML tasks need sensitive attributes (e.g., medical diagnosis)

----
## Testing Anti-Classification

How do we test that an ML model achieves anti-classification?

----
## Testing Anti-Classification

Straightforward invariant for classifier $f$ and protected attribute $p$: 

$\forall x. f(x[p\leftarrow 0]) = f(x[p\leftarrow 1])$

*(does not account for correlated attributes)*

Test with random input data or on any test data

Any single inconsistency shows that the protected attribute was used. Can also report percentage of inconsistencies.

<!-- references -->
See for example: Galhotra, Sainyam, Yuriy Brun, and Alexandra Meliou. "[Fairness testing: testing software for discrimination](http://people.cs.umass.edu/brun/pubs/pubs/Galhotra17fse.pdf)." In Proceedings of the 2017 11th Joint Meeting on Foundations of Software Engineering, pp. 498-510. 2017.

----
## Notations

* $X$: Feature set (e.g., age, race, education, region, income, etc.,)  
* $A \in X$: Sensitive attribute (e.g., gender)
* $R$: Regression score (e.g., predicted likelihood of loan default)
* $Y'$: Classifier output
  * $Y' = 1$ if and only if $R > T$ for some threshold $T$
  * e.g., Deny the loan ($Y' = 1$) if the likelihood of default > 30% 
* $Y$: Target variable being predicted ($Y = 1$ if the person actually
  defaults on loan)

----
## Independence

$P[Y' = 1 | A = a]  = P[Y' = 1 | A = b]$

* Also called _group fairness_ or _demographic parity_
* Mathematically, $Y' \perp A$
  * Prediction ($Y'$)  must be independent of the sensitive attribute ($A$)
* Examples:
	* The predicted rate of recidivism is the same across all races
	* Both women and men have the equal probability of being promoted
	* i.e., P[promote = 1 | gender = M] = P[promote = 1 | gender = F] 

----
## Independence

* Q. What are limitations of independence?
  <!-- .element: class="fragment" -->
  * Ignores possible correlation between $Y$ and $A$
    <!-- .element: class="fragment" -->
	* Rules out perfect predictor $Y' = Y$ when $Y$ & $A$ are correlated
  * Permits abuse and laziness: Can be satisfied by randomly assigning
    a positive outcome ($Y' = 1$) to protected groups
    <!-- .element: class="fragment" -->
	* e.g., Randomly promote people (regardless of their
      job performance) to match the rate across all groups


----
## Recall: Equality vs Equity

![Contrasting equality, equity, and justice](eej2.png)


----
## Calibration to Achieve Independence

Select different thresholds for different groups to achieve prediction parity:

$P[R > t_0 | A = 0]  = P[R > t_1 | A = 1]$

Lowers bar for some groups -- equity, not equality

----
## Testing Independence

* Separate validation/telemetry data by protected attribute
<!-- .element: class="fragment" -->
	* Or generate realistic test data, e.g. from probability distribution of population
	<!-- .element: class="fragment" -->
* Separately measure rate of positive predictions
<!-- .element: class="fragment" -->
* Report issue if rate differs beyond $\epsilon$ across groups
  <!-- .element: class="fragment" -->

----
## Separation

$P[Y'=1∣Y=0,A=a] = P[Y'=1∣Y=0,A=b]$
$P[Y'=0∣Y=1,A=a] = P[Y'=0∣Y=1,A=b]$

* Also called _equalized odds_ 
* $Y' \perp A | Y$
  * Prediction must be independent of the sensitive attribute
  _conditional_ on the target variable

----
## Review: Confusion Matrix

![](confusion-matrix.jpg)

Can we explain separation in terms of model errors?

$P[Y'=1∣Y=0,A=a] = P[Y'=1∣Y=0,A=b]$
$P[Y'=0∣Y=1,A=a] = P[Y'=0∣Y=1,A=b]$

----
## Separation

$P[Y'=1∣Y=0,A=a] = P[Y'=1∣Y=0,A=b]$ (FPR parity)
$P[Y'=0∣Y=1,A=a] = P[Y'=0∣Y=1,A=b]$ (FNR parity)

* $Y' \perp A | Y$
  * Prediction must be independent of the sensitive attribute
    _conditional_ on the target variable
* i.e., All groups are susceptible to the same false positive/negative rates
<!-- .element: class="fragment" -->
* Example: Promotion
<!-- .element: class="fragment" -->
  * Y': Promotion decision, A: Gender of applicant: Y: Actual job performance
  * Separation w/ FNR: Probability of being incorrectly denied promotion is equal
    across both male & female employees

----
## Testing Separation

* Generate separate validation sets for each group
* Separate validation/telemetry data by protected attribute
  - Or generate *realistic*  test data, e.g. from probability distribution of population
* Separately measure false positive and false negative rates

----
## Case Study: Cancer Diagnosis

![](mri.jpg)

----
## Exercise: Cancer Diagnosis

![](cancer-stats.jpg)

* 1000 data samples (500 male & 500 female patients)
* Does the model achieve independence? Separation w/ FPR or FNR?
* What can we conclude about the model & its usage?  


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
# Achieving Fairness Criteria

----
## Can we achieve fairness during the learning process?

* Data acquisition:
  - Collect additional data if performance is poor on some groups
* Pre-processing:
  * Clean the dataset to reduce correlation between the feature set
    and sensitive attributes
* Training time constraint
  * ML is a constraint optimization problem (i.e., minimize errors)
  * Impose additional parity constraint into ML optimization process
    (as part of the loss function)
* Post-processing
  * Adjust thresholds to achieve a desired fairness metric
* (Still active area of research! Many new techniques published each year)

<!-- references -->
_Training Well-Generalizing Classifiers for Fairness Metrics and
Other Data-Dependent Constraints_, Cotter et al., (2018).

----
## Trade-offs: Accuracy vs Fairness

![](fairness-accuracy.jpeg)

* In general, accuracy is at odds with fairness
  * e.g., Impossible to achieve perfect accuracy ($R = Y$) while
  ensuring independence
* Determine how much compromise in accuracy or fairness is acceptable to
  your stakeholders

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
# Requirements Engineering for Fairness


----
## Recall: Machine vs World

![](machine-world.png)

* No ML/AI lives in vacuum; every system is deployed as part of the world
* A requirement describes a desired state of the world (i.e., environment)
* Machine (software) is _created_ to manipulate the environment into
this state


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
# Summary

* Definitions of fairness
  * Anti-classification, independence, separation
* Achieving fairness
  * Trade-offs between accuracy & fairness
* Achieving fairness as an activity throughout the entire development cycle
* Requirements engineering for fair ML systems
  * Stakeholders, sub-populations & unfair (dis-)advantages
  * Types of harms
  * Legal requirements
