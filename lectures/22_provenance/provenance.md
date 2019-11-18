---
author: Christian Kaestner
title: "17-445: Data Provenance, Reproducability, and Explainability"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---

# Data Provenance, Reproducability, and Explainability

Christian Kaestner

<!-- references -->

Required reading: Halevy, Alon, Flip Korn, Natalya F. Noy, Christopher Olston, Neoklis Polyzotis, Sudip Roy, and Steven Euijong Whang. [Goods: Organizing google's datasets](http://research.google.com/pubs/archive/45390.pdf). In Proceedings of the 2016 International Conference on Management of Data, pp. 795-806. ACM, 2016.

---

# Learning Goals

* Judge the importance of data provenance, reproducibility and explainability for a given system
* Create documentation for data dependencies and provenance in a given system
* Propose versioning strategies for data and models
* Design and test systems for reproducibility
* Design strategies to make models transparent and explainable

---

# Case Study: Credit Scoring

----

[![Apple Card Tweet](applecard.png)](https://twitter.com/dhh/status/1192540900393705474)
----

[![Apple Card Tweet 2: "It's just the algorithm"](applecard.png)](https://twitter.com/dhh/status/1192945019230945280)

----

## Debugging?

What went wrong? Where? How to fix?

<!-- discussion -->

----

## Debugging Questions

* Can we reproduce the problem?
* What were the inputs to the model?
* Which exact model version was used?
* What data was the model trained with?
* What learning code (cleaning, feature extraction, ML algorithm) was the model trained with?
* Where does the data come from? How was it processed and extracted?
* Were other models involved? Which version? Based on which data?
* What parts of the input are responsible for the (wrong) answer? How can we fix the model?

---

# Data Provenance

Historical record of data and its origin

----

## Data Provenance

* Track origin of all data
    - Collected where?
    - Modified by whom, when, why?
    - Extracted from what other data or model or algorithm?
* ML models often based on data drived from many sources through many steps, including other models

----

## Tracking Data

* Document all data sources
* Model dependencies and flows
* Ideally model all data and processing code
* Avoid "visibility debt"
* 
* Advanced: Use infrastructure to automatically capture/infer dependencies and flows (e.g., [Goods](http://research.google.com/pubs/archive/45390.pdf) paper)

----

```mermaid
graph TD
    serverlogs --> extract(extract)
    extract --> actionsDB
    actionsDB --> gender(genderModel)
    gender --> genderDB
    actionsDB --> train(learning)
    genderDB --> train
    train --> recommendationModel
    requests --> recommendationModel
```

----

## Logging and Audit Traces

* Version everything
* Record every model evaluation with model version
* Append only, backed up

---

# Fixing Models

<!-- references -->

See also Hulten. Building Intelligent Systems. Chapter 21

----

## Orchestrating Multiple Models

* Try different modeling approaches in parallel
* Pick one, voting, sequencing, metamodel, or responding with worst-case prediction

<!-- colstart -->

```mermaid
graph TD
input --> model1
model1 --> model2
model2 --> model3
model1 --> yes
model2 --> yes
model3 --> yes
model3 --> no
```
<!-- col -->
```mermaid
graph TD
input --> model1
input --> model2
input --> model3
model1 --> vote
model2 --> vote
model3 --> vote
vote --> yes/no
```
<!-- col -->
```mermaid
graph TD
input --> model1
input --> model2
input --> model3
model1 --> metamodel
model2 --> metamodel
model3 --> metamodel
metamodel --> yes/no
```
<!-- colend -->

----

## Chasing Bugs

* Update, clean, add, remove data
* Change modeling parameters
* Add regression tests
* Fixing one problem may lead to others, recognizable only later

----

## Partitioning Contexts

* Separate models for different subpopulations
* Potentially used to address fairness issues
* ML approaches typically partition internally already

```mermaid
graph TD
input --> decision[pick model]
decision --> model1
decision --> model2
decision --> model3
model1 --> yes/no
model2 --> yes/no
model3 --> yes/no
```

----

## Overrides

* Hardcoded heuristics (usually created and maintained by humans) for special cases
* Whitelists, blacklists
* Guardrails
* Potential neverending attempt to fix special cases

```mermaid
graph TD
input --> blacklist
blacklist --> no
blacklist --> model
model --> yes
model --> no
```

---
# Transparency

----

![Booking.com rating](booking.png)

<!-- references -->

Source: [Motahhare Eslami](http://eslamim2.web.engr.illinois.edu/)


----
## Case Study: Facebook's Feed Curation

![Facebook with and without filtering](facebook.png)

<!-- references -->

Eslami, Motahhare, Aimee Rickman, Kristen Vaccaro, Amirhossein Aleyasen, Andy Vuong, Karrie Karahalios, Kevin Hamilton, and Christian Sandvig. [I always assumed that I wasn't really that close to [her]: Reasoning about Invisible Algorithms in News Feeds](http://eslamim2.web.engr.illinois.edu/publications/Eslami_Algorithms_CHI15.pdf). In Proceedings of the 33rd annual ACM conference on human factors in computing systems, pp. 153-162. ACM, 2015.



----
## Case Study: Facebook's Feed Curation
<!-- smallish -->

* 62% of interviewees were not aware of curation algorithm
* Surprise and anger when learning about curation

> "Participants were most upset when close friends and
family were not shown in their feeds [...] participants often attributed missing stories to their friends’ decisions to exclude them rather than to Facebook News Feed algorithm."

* Learning about algorithm did not change satisfaction level
* More active engagement, more feeling of control


<!-- references -->

Eslami, Motahhare, Aimee Rickman, Kristen Vaccaro, Amirhossein Aleyasen, Andy Vuong, Karrie Karahalios, Kevin Hamilton, and Christian Sandvig. [I always assumed that I wasn't really that close to [her]: Reasoning about Invisible Algorithms in News Feeds](http://eslamim2.web.engr.illinois.edu/publications/Eslami_Algorithms_CHI15.pdf). In Proceedings of the 33rd annual ACM conference on human factors in computing systems, pp. 153-162. ACM, 2015.

----
## Case Study: HR Application Screening

[![Twitter post](hiringai.png)](https://twitter.com/TheWrongNoel/status/1194842728862892033)

----
## Appropriate Level of Algorithmic Transparency

IP/Trade Secrets/Fairness/Perceptions/Ethics?

How to design? How much control to give?

<!-- discussion -->

---

# Explainability & Interpretability




----

[![Apple Card Tweet 2: "It's just the algorithm"](applecard.png)](https://twitter.com/dhh/status/1192945019230945280)

----

## "It's just the algorithm/model"

* Specifications can be discussed, somebody made a decision
* ML models are trained, some wrong results are to be expected 
* Assigning blame: Person making decisions, algorithm/specification, opaque model? Path to appeal?

----
## Appealing ML Decisions

* See requirements lecture: Planning for mistakes
* Allow way to override decisions or accept mistakes?
    - Automation degree vs. cost for human intervention (support)
* Review model for quality and fairness
* How to fix? One-off? Fix model?

<!-- discussion -->

----

## Explaining Decisions

Cat? Dog? Lion?

Confidence? Why?

![Cat](cat.png)

----

## Explaining Decisions

[![Slack Notifications Decision Tree](slacknotifications.jpeg)](slacknotifications.jpeg)

----
## Explaining Decisions

```prolog
> parent(john, douglas).
> parent(bob, john).
> parent(ebbon, bob).

> parent(john, B)?
parent(john, douglas).

> parent(A, A)?

> ancestor(A, B) :- parent(A, B).
> ancestor(A, B) :- parent(A, C), ancestor(C, B).

> ancestor(A,B)?
ancestor(john, douglas).
ancestor(ebbon, bob).
```

----
## Explaining Decisions

![Decision Tree](decisiontree.png)

<!-- references -->

Source: https://towardsdatascience.com/a-guide-to-decision-trees-for-machine-learning-and-data-science-fe2607241956
----
## Explainability in AI

* Explain how the model made a decision
    - Rules, cutoffs, reasoning?
    - What are the relevant factors? 
    - Why those rules/cutoffs?
* Challenging in symbolic AI with complicated rules
* Challenging with ML because models too complex and based on data
    - Can we understand the rules?
    - Can we understand why these rules?

----

## Explaining Black-Box Models

* Learn simpler model by sampling from more complex one
    - e.g., decision tree learned from DNN outputs
* Roughly: Sensitivity analysis to identify key parameters

----
## SHAP Analysis (SHapley Additive exPlanation)

![SHAP diagram](shap_diagram.png)

<!-- references -->

Lundberg, Scott M., and Su-In Lee. [A unified approach to interpreting model predictions](http://papers.nips.cc/paper/7062-a-unified-approach-to-interpreting-model-predictions.pdf). Advances in Neural Information Processing Systems. 2017.

Notes: It is based on Shapley values, a technique used in game theory to determine how much each player in a collaborative game has contributed to its success. Works for any tree-based models.

----
## SHAP Analysis (SHapley Additive exPlanation)

![force plot](boston_instance.png)

<!-- references -->

Lundberg, Scott M., and Su-In Lee. [A unified approach to interpreting model predictions](http://papers.nips.cc/paper/7062-a-unified-approach-to-interpreting-model-predictions.pdf). Advances in Neural Information Processing Systems. 2017.

----
[![](https://cdn-images-1.medium.com/max/1600/1*7kH8RQHxZK5qElP_DbfGpQ.png)](https://www.datasciencecentral.com/profiles/blogs/demystifying-black-box-models-with-shap-value-analysis)

<!-- references -->
Source: https://www.datasciencecentral.com/profiles/blogs/demystifying-black-box-models-with-shap-value-analysis

----
## "Stop explaining black box machine learning models for high stakes decisions and use interpretable models instead"

<!-- smallish -->

Hypotheses:
* It is a myth that there is necessarily a trade-off between accuracy and interpretability (when having meaningful features)
* Explainable ML methods provide explanations that are not faithful to what the original model computes
* Explanations often do not make sense, or do not provide enough detail to understand what the black box is doing
* Black box models are often not compatible with situations where information outside the database needs to be combined with a risk assessment
*  Black box models with explanations can lead to an overly complicated decision pathway that is ripe for human error


<!-- references -->

Rudin, Cynthia. "Stop explaining black box machine learning models for high stakes decisions and use interpretable models instead." Nature Machine Intelligence 1.5 (2019): 206-215. ([Preprint](https://arxiv.org/abs/1811.10154))

----

## Attention Maps

![Attention Maps](attentionmap.jpeg)

Identifies which parts of the input lead to decisions (but not why!)

<!-- references -->

Source: B. Zhou, A. Khosla, A. Lapedriza, A. Oliva, and A. Torralba. [Learning Deep Features for Discriminative Localization](http://cnnlocalization.csail.mit.edu/Zhou_Learning_Deep_Features_CVPR_2016_paper.pdf). CVPR'16 

----

## CORELS’ model for recidivism risk prediction

| | | |
|-|-|-|
| IF | age between 18-20 and sex is male | THEN predict arrest (within 2 years) |
| ELSE IF | age between 21-23 and 2-3 prior offenses | THEN predict arrest |
| ELSE IF | more than three priors | THEN predict arrest |
| ELSE |predict no arrest.| |

Simple, interpretable model with comparable accuracy to proprietary COMPAS model

<!-- references -->

Rudin, Cynthia. "Stop explaining black box machine learning models for high stakes decisions and use interpretable models instead." Nature Machine Intelligence 1.5 (2019): 206-215. ([Preprint](https://arxiv.org/abs/1811.10154))

---
# Summary

* Provenance is important for debugging and accountability, versioning and data tracking
* Algorithmic transparency can impact users and usability
* Explainability is an open challenge, interpretable models vs post-hoc extracted explanations



