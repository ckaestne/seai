---
author: Christian Kaestner
title: "17-445: Quality Assessment in Production"
semester: Fall 2020
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---

# Quality Assessment in Production

Christian Kaestner


<!-- references -->

Required Reading: 
* 🕮 Hulten, Geoff. "[Building Intelligent Systems: A Guide to Machine Learning Engineering.](https://www.buildingintelligentsystems.com/)" Apress, 2018, Chapter 15 (Intelligent Telemetry).

Suggested Readings: 
* Alec Warner and Štěpán Davidovič. "[Canary Releases](https://landing.google.com/sre/workbook/chapters/canarying-releases/)." in [The Site Reliability Workbook](https://landing.google.com/sre/books/), O'Reilly 2018
* Georgi Georgiev. “[Statistical Significance in A/B Testing – a Complete Guide](http://blog.analytics-toolkit.com/2017/statistical-significance-ab-testing-complete-guide/#noninf).” Blog 2018

----

<div class="tweet" data-src="https://twitter.com/changelog/status/1137359428632621060"></div>


---
## Learning Goals

* Design telemetry for evaluation in practice
* Understand the rationale for beta tests and chaos experiments
* Plan and execute experiments (chaos, A/B, shadow releases, ...) in production
* Conduct and evaluate multiple concurrent A/B tests in a system
* Perform canary releases
* Examine experimental results with statistical rigor
* Support data scientists with monitoring platforms providing insights from production data





---
# From Unit Tests to Testing in Production

*(in traditional software systems)*

----
## Unit Test, Integration Tests, System Tests

![Testing levels](testinglevels.png)
<!-- .element: class="stretch" -->

Note: Testing before release. Manual or automated.

----
## Beta Testing

![Windows 95 beta release](windowsbeta.jpg)
<!-- .element: class="stretch" -->

Note: Early release to select users, asking them to send feedback or report issues. No telemetry in early days.

----
## Crash Telemetry

![Windows 95 Crash Report](wincrashreport_windows_xp.png)
<!-- .element: class="stretch" -->

Note: With internet availability, send crash reports home to identify problems "in production". Most ML-based systems are online in some form and allow telemetry. 

----
## A/B Testing

![A/B test example](ab-groove.jpg)
<!-- .element: class="stretch" -->

Notes: Usage observable online, telemetry allows testing in production.  Picture source: https://www.designforfounders.com/ab-testing-examples/

----
## Chaos Experiments


[![Simian Army logo by Netflix](simianarmy.jpg)](https://en.wikipedia.org/wiki/Chaos_engineering)
<!-- .element: class="stretch" -->

Note: Deliberate introduction of faults in production to test robustness.







---
# Model Assessment in Production

Ultimate held-out evaluation data: Unseen real user data

----
## Identify Feedback Mechanism in Production 

* Live observation in the running system
* Potentially on subpopulation (A/B testing)
* Need telemetry to evaluate quality -- challenges:
    - Gather feedback without being intrusive (i.e., labeling outcomes), without harming user experience
    - Manage amount of data
    - Isolating feedback for specific AI component + version

----
## Discuss how to collect feedback

* Was the house price predicted correctly?
* Did the profanity filter remove the right blog comments?
* Was there cancer in the image?
* Was a Spotify playlist good?
* Was the ranking of search results good?
* Was the weather prediction good?
* Was the translation correct?
* Did the self-driving car break at the right moment? Did it detect the pedestriants?

<!-- discussion -->

Notes: More:
* SmartHome: Does it automatically turn of the lights/lock the doors/close the window at the right time?
* Profanity filter: Does it block the right blog comments?
* News website: Does it pick the headline alternative that attracts a user’s attention most?
* Autonomous vehicles: Does it detect pedestrians in the street?



----
![Skype feedback dialog](skype1.jpg)
<!-- split -->
![Skype report problem button](skype2.jpg)

Notes:
Expect only sparse feedback and expect negative feedback over-proportionally

----
![Flight cost forcast](flightforcast.jpg)

Notes: Can just wait 7 days to see actual outcome for all predictions
----
![Temi Transcription Service Editor](temi.png)

Notes: Clever UI design allows users to edit transcripts. UI already highlights low-confidence words, can 

----
## Manually Label Production Samples

Similar to labeling learning and testing data, have human annotators

![Amazon mechanical turk](mturk.jpg)

----
## Measuring Model Quality with Telemetry

* Three steps:
    - Metric: Identify quality of concern
    - Telemetry: Describe data collection procedure
    - Operationalization: Measure quality metric in terms of data
* Telemetry can provide insights for correctness
    - sometimes very accurate labels for real unseen data
    - sometimes only mistakes
    - sometimes delayed
    - often just samples
    - often just weak proxies for correctness
* Often sufficient to *approximate* precision/recall or other model-quality measures
* Mismatch to (static) evaluation set may indicate stale or unrepresentative data
* Trend analysis can provide insights even for inaccurate proxy measures


----
## Monitoring Model Quality in Production

* Monitor model quality together with other quality attributes (e.g., uptime, response time, load)
* Set up automatic alerts when model quality drops
* Watch for jumps after releases
    - roll back after negative jump
* Watch for slow degradation
    - Stale models, data drift, feedback loops, adversaries
* Debug common or important problems
    - Monitor characteristics of requests 
    - Mistakes uniform across populations?
    - Challenging problems -> refine training, add regression tests

----
![Grafana screenshot from Movie Recommendation Service](grafana.png)

----
## Prometheus and Grafana

[![Prometheus Architecture](prometheusarchitecture.png)](https://prometheus.io/docs/introduction/overview/)

----
![Grafana Dashboard](grafanadashboard.png)

----
## Many commercial solutions

[![DataRobot MLOps](datarobot.png)](https://www.datarobot.com/platform/mlops/)

<!-- references -->
e.g. https://www.datarobot.com/platform/mlops/

Many pointers: Ori Cohen "[Monitor! Stop Being A Blind Data-Scientist.](https://towardsdatascience.com/monitor-stop-being-a-blind-data-scientist-ac915286075f)" Blog 2019
----
## Engineering Challenges for Telemetry
![Amazon news story](alexa.png)

----
## Engineering Challenges for Telemetry
* Data volume and operating cost
    - e.g., record "all AR live translations"?
    - reduce data through sampling
    - reduce data through summarization (e.g., extracted features rather than raw data; extraction client vs server side)
* Adaptive targeting
* Biased sampling
* Rare events
* Privacy
* Offline deployments?

----
## Exercise: Design Telemetry in Production

Discuss: Quality measure, telemetry, operationalization, false positives/negatives, cost, privacy, rare events

Scenarios:
* Group 1: Amazon: Shopping app feature that detects the shoe brand from photos
* Group 2: Google: Tagging uploaded photos with friends' names
* Group 3: Spotify: Recommended personalized playlists
* Group 4: Wordpress: Profanity filter to moderate blog posts


Summarize results on a slide


---
# Experimenting in Production

* A/B experiments
* Shadow releases / traffic teeing
* Blue/green deployment
* Canary releases
* Chaos experiments


----
<div class="tweet" data-src="https://twitter.com/changelog/status/1137359428632621060"></div>


---
# A/B experiments
----
## What if...?
 
* ... we hand plenty of subjects for experiments
* ... we could randomly assign subjects to treatment and control group without them knowing
* ... we could analyze small individual changes and keep everything else constant


▶ Ideal conditions for controlled experiments

![Amazon.com front page](amazon.png)

----
## A/B Testing for Usability

* In running system, random sample of X users are shown modified version
* Outcomes (e.g., sales, time on site) compared among groups

![A/B test example](ab-groove.jpg)

Notes: Picture source: https://www.designforfounders.com/ab-testing-examples/

----
![A/B test example](ab-prescr.jpg)

Notes: Picture source: https://www.designforfounders.com/ab-testing-examples/

----
## A/B Experiment for AI Components?

* New product recommendation algorithm for web store?
* New language model in audio transcription service?
* New (offline) model to detect falls on smart watch

<!-- discussion -->

----
## Experiment Size

* With enough subjects (users), we can run many many experiments
* Even very small experiments become feasible
* Toward causal inference

![A/B test example of a single button's color](ab-button.png)


----

## Implementing A/B Testing

* Implement alternative versions of the system
    * using feature flags (decisions in implementation)
    * separate deployments (decision in router/load balancer)
* Map users to treatment group
    * Randomly from distribution
    * Static user - group mapping
    * Online service (e.g., [launchdarkly](https://launchdarkly.com/), [split](https://www.split.io/))
* Monitor outcomes *per group*
    * Telemetry, sales, time on site, server load, crash rate

----
## Feature Flags

```java
if (features.enabled(userId, "one_click_checkout")) {
     // new one click checkout function
} else {
     // old checkout functionality
}
```

* Boolean options
* Good practices: tracked explicitly, documented, keep them localized and independent
* External mapping of flags to customers
    * who should see what configuration
    * e.g., 1% of users sees `one_click_checkout`, but always the same users; or 50% of beta-users and 90% of developers and 0.1% of all users

```scala
def isEnabled(user): Boolean = (hash(user.id) % 100) < 10
```

----
![split.io screenshot](splitio.png)
<!-- .element: class="stretch" --> 






---
# Confidence in A/B experiments

(statistical tests)

----

## Comparing Averages

<!-- colstart -->
**Group A**

*classic personalized content recommendation model*

2158 Users

average 3:13 min time on site

<!-- col -->

**Group B**

*updated personalized content recommendation model*

10 Users

average 3:24 min time on site

<!-- colend -->
----
## Comparing Distributions

![Two distributions, 10000 samples each from a normal distribution](twodist.png)

----
## Different effect size, same deviations

<!-- colstart -->
![](twodist.png)
<!-- col -->
![](twodisteffect.png)
<!-- colend -->

----
## Same effect size, different deviations

<!-- colstart -->
![](twodist.png)
<!-- col -->
![](twodistnoise.png)
<!-- colend -->

Less noise --> Easier to recognize



----

## Dependent vs. independent measurements

* Pairwise (dependent) measurements
    * Before/after comparison
    * With same benchmark + environment
    * e.g., new operating system/disc drive faster
* Independent measurements
    * Repeated measurements
    * Input data regenerated for each measurement

----
## Significance level
* Statistical change of an error
* Define before executing the experiment
    * use commonly accepted values
    * based on cost of a wrong decision
* Common:
    * 0.05 significant
    * 0.01 very significant
* Statistically significant result =!> proof
* Statistically significant result =!> important result
* Covers only alpha error (more later)

----

## Intuition: Error Model
* 1 random error, influence +/- 1
* Real mean: 10
* Measurements: 9 (50%) und 11 (50%)
*
* 2 random errors, each +/- 1
* Measurements: 8 (25%), 10 (50%) und 12 (25%)
* 
* 3 random errors, each +/- 1
* Measurements : 7 (12.5%), 9 (37.5), 11 (37.5), 12 (12.5)
----
<iframe src='https://gfycat.com/ifr/PleasingMeaslyGalapagossealion' frameborder='0' scrolling='no' allowfullscreen width='640' height='524'></iframe>
----
## Normal Distribution
![Normal distribution](normaldist.png)

<!-- references -->
(CC 4.0 [D Wells](https://commons.wikimedia.org/wiki/File:Standard_Normal_Distribution.png))
----
## Confidence Intervals
![](confint.png)
----
## Comparison with Confidence Intervals
![](perfcomp.png)
 
<!-- references -->
Source: Andy Georges, Dries Buytaert, and Lieven Eeckhout. 2007. [Statistically rigorous java performance evaluation](https://dri.es/files/oopsla07-georges.pdf). In Proc. Conference on Object-Oriented Programming Systems and Applications (OOPSLA '07). ACM, 57-76.
----
# t-test

```r
> t.test(x, y, conf.level=0.9)

        Welch Two Sample t-test

t = 1.9988, df = 95.801, p-value = 0.04846
alternative hypothesis: true difference in means is 
not equal to 0 
90 percent confidence interval:
 0.3464147 3.7520619 
sample estimates:
mean of x mean of y 
 51.42307  49.37383 

> # paired t-test:
> t.test(x-y, conf.level=0.9)
```
----
![t-test in an A/B testing dashboard](testexample.png)
<!-- references -->
Source: https://conversionsciences.com/ab-testing-statistics/
----
![t-test in an A/B testing dashboard](testexample2.png)
<!-- references -->
Source: https://cognetik.com/why-you-should-build-an-ab-test-dashboard/
----
## How many samples needed?
<!-- colstart -->
**Too few?**

<!-- Noise and random results -->
<!-- col -->
**Too many?**

<!-- Risk of spreading bad designs -->
<!-- colend -->


<!-- discussion -->


---
# A/B testing automation

* Experiment configuration through DSLs/scripts
* Queue experiments
* Stop experiments when confident in results
* Stop experiments resulting in bad outcomes (crashes, very low sales)
* Automated reporting, dashboards

<!-- references -->

Further readings:
* Tang, Diane, et al. [Overlapping experiment infrastructure: More, better, faster experimentation](https://ai.google/research/pubs/pub36500.pdf). Proceedings of the 16th ACM SIGKDD international conference on Knowledge discovery and data mining. ACM, 2010. (Google)
* Bakshy, Eytan, Dean Eckles, and Michael S. Bernstein. [Designing and deploying online field experiments](https://arxiv.org/pdf/1409.3174). Proceedings of the 23rd International Conference on World Wide Web. ACM, 2014. (Facebook)
----
## DSL for scripting A/B tests at Facebook
```java
button_color = uniformChoice(
    choices=['#3c539a', '#5f9647', '#b33316'],
    unit=cookieid);

button_text = weightedChoice(
    choices=['Sign up', 'Join now'],
    weights=[0.8, 0.2],
    unit=cookieid); 

if (country == 'US') {
    has_translate = bernoulliTrial(p=0.2, unit=userid);
} else {
    has_translate = bernoulliTrial(p=0.05, unit=userid);
}
```
<!-- references -->

Further readings:
* Bakshy, Eytan, Dean Eckles, and Michael S. Bernstein. [Designing and deploying online field experiments](https://arxiv.org/pdf/1409.3174). Proceedings of the 23rd International Conference on World Wide Web. ACM, 2014. (Facebook)
----
## Concurrent A/B testing

* Multiple experiments at the same time
    * Independent experiments on different populations -- interactions not explored
    * Multi-factorial designs, well understood but typically too complex, e.g., not all combinations valid or interesting
    * Grouping in sets of experiments

<!-- references -->

Further readings:
* Tang, Diane, et al. [Overlapping experiment infrastructure: More, better, faster experimentation](https://ai.google/research/pubs/pub36500.pdf). Proceedings of the 16th ACM SIGKDD international conference on Knowledge discovery and data mining. ACM, 2010. (Google)
* Bakshy, Eytan, Dean Eckles, and Michael S. Bernstein. [Designing and deploying online field experiments](https://arxiv.org/pdf/1409.3174). Proceedings of the 23rd International Conference on World Wide Web. ACM, 2014. (Facebook)



---
# Other Experiments in Production

* Shadow releases / traffic teeing
* Blue/green deployment
* Canary releases
* Chaos experiments


----
## Shadow releases / traffic teeing

* Run both models in parallel
* Report outcome of old model
* Compare differences between model predictions
* If possible, compare against ground truth labels/telemetry

**Examples?**

----
## Blue/green deployment

* Provision service both with old and new model (e.g., services)
* Support immediate switch with load-balancer
* Allows to undo release rapidly

**Advantages/disadvantages?**

----
## Canary Releases

* Release new version to small percentage of population (like A/B testing)
* Automatically roll back if quality measures degrade
* Automatically and incrementally increase deployment to 100% otherwise

![Canary bird](canary.jpg)
<!-- .element: class="stretch" -->

----
## Chaos Experiments

[![Simian Army logo by Netflix](simianarmy.jpg)](https://en.wikipedia.org/wiki/Chaos_engineering)
<!-- .element: class="stretch" -->

----
## Chaos Experiments for AI Components?

<!-- discussion -->

Note: Artifically reduce model quality, add delays, insert bias, etc to test monitoring and alerting infrastructure


----
## Advice for Experimenting in Production

* Minimize *blast radius* (canary, A/B, chaos expr)
* Automate experiments and deployments
* Allow for quick rollback of poor models (continuous delivery, containers, loadbalancers, versioning)
* Make decisions with confidence, compare distributions
* Monitor, monitor, monitor





---
![MLOps](https://ml-ops.org/img/mlops-loop-banner.jpg)

<!-- references -->
https://ml-ops.org/

----
## On Terminology

* Many vague buzzwords, often not clearly defined
* *MLOps*: Collaboration and communication between data scientists and operators, e.g.,
  - Automate model deployment
  - Model training and versioning infrastructure
  - Model deployment and monitoring
* *AIOps*: Using AI/ML to make operations decision, e.g. in a data center
* *DataOps*: Data analytics, often business setting and reporting
  - Infrastructure to collect data (ETL) and support reporting
  - Monitor data analytics pipelines
  - Combines agile, DevOps, Lean Manufacturing ideas

----
## MLOps Overview

* Integrate ML artifacts into software release process, unify process
* Automated data and model validation (continuous deployment)
* Data engineering, data programming
* Continuous deployment for ML models
  - From experimenting in notebooks to quick feedback in production
* Versioning of models and datasets
* Monitoring in production


<!-- references -->
Further reading: [MLOps principles](https://ml-ops.org/content/mlops-principles.html)



---
# Summary

* Production data is ultimate unseen validation data
* Telemetry is key and challenging (design problem and opportunity)
* Monitoring and dashboards
* Many forms of experimentation and release (A/B testing, shadow releases, canary releases, chaos experiments, ...) to minimize "blast radius"
* Gain confidence in results with statistical tests
* MLOps: DevOps-like infrastructure to support data scientists


<!-- 

TODO:

general tradeoffs between testing with offline dataset (old or recent), testing with simulation, shadow execution, or testing in production.

 -->