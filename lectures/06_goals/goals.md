---
author: Christian Kaestner
title: "17-445: "
semester: Summer 2020
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---  

# Goals and Success Measures for AI-Enabled Systems



Christian Kaestner

<!-- references -->

Required Readings: 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 2 (Knowing when to use IS), 4 (Defining the IS’s Goals) and 15 (Intelligent Telemetry)

Suggested complementary reading: 🕮 Ajay Agrawal, Joshua Gans, Avi Goldfarb. “[Prediction Machines: The Simple Economics of Artificial Intelligence](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/6lpsnm/alma991019698987304436)” 2018 

---

# Learning goals

* Judge when to apply AI for a problem in a system
* Define system goals and map them to goals for the AI component
* Design and implement suitable measures and corresponding telemetry


---
## Today's Case Study: Spotify Personalized Playlists

[![Spotify Screenshot of (My) Personalized Playlists](spotify.png)](spotify.png)
<!-- .element: class="stretch" -->





---
# When to use Machine Learning?

----
## When not to use Machine Learning?

* If clear specifications are available
* Simple heuristics are *good enough*
* Cost of building and maintaining the system outweighs the benefits (see technical debt paper)
* Correctness is of utmost importance
* Only use ML for the hype, to attract funding

**Examples?**

Notes: Accounting systems, inventory tracking, physics simulations, safety railguards, fly-by-wire

----
## Consider Non-ML Baselines

* Consider simple heuristics -- how far can you get?
* Consider semi-manual approaches -- cost and benefit?
* Consider the system without that feature
*
* **Discuss Examples**
    - Ranking apps, recommending products
    - Filtering spam or malicious advertisement
    - Creating subtitles for conference videos
    - Summarizing soccer games
    - Controlling a washing machine

----
## When to use Machine Learning

* Big problems: many inputs, massive scale
* Open-ended problems: no single solution, incremental improvements, continue to grow
* Time-changing problems: adapting to constant change, learn with users
* Intrinsically hard problems: unclear rules, heuristics perform poorly

**Examples?**

<!-- references -->
see Hulten, Chapter 2

----
## When to use Machine Learning

* Partial system is viable and interesting: mistakes are acceptable or mitigatable, benefits outweigh costs
* Data for continuous improvement is available: telemetry design
* Predictions can have an influence on system objectives: systems act, recommendations, ideally measurable influence
* Cost effective: cheaper than other approaches, meaningful benefits

**Examples?**

<!-- references -->
see Hulten, Chapter 2
----
## Discussion: Spotify

*Big problem? Open ended? Time changing? Hard? Partial system viable? Data continuously available? Influence objectives? Cost effective?*

[![Screenshot of (My) Personalized Playlists](spotify.png)](spotify.png)
<!-- .element: class="stretch" -->









---
# The Business View

<!-- references -->
🕮 Ajay Agrawal, Joshua Gans, Avi Goldfarb. “[Prediction Machines: The Simple Economics of Artificial Intelligence](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/6lpsnm/alma991019698987304436)” 2018 
----
## AI as Prediction Machines

<!-- colstart -->
AI: Higher accuracy predictions at much much lower cost

May use new, cheaper predictions for traditional tasks (**examples?**)

May now use predictions for new kinds of problems (**examples?**)

May now use more predictions than before 

(Analogies: Reduced cost of light, reduced cost of search with the internet)

<!-- col -->

![Book: Prediction Machines](predictionmachinescover.png)

<!-- colend -->

Notes: May use new, cheaper predictions for traditional tasks -> inventory and demand forcast; May now use predictions for new kinds of problems -> navigation and translation

----
## The economic lense

* predictions are critical input to decision making (not necessarily full automation)
* decreased price in predictions makes them more attractive for more tasks
* increases the value of data and data science experts
* decreases the value of human prediction and other substitutes
* decreased cost and increased accuracy in prediction can fundamentally change business strategies and transform organizations
    - e.g., a shop sending predicted products without asking
* use of (cheaper, more) predictions can be distinct economic advantage

----
## Predicting the Best Route

![Taxi in London](taxi.jpg)
<!-- .element: class="stretch" -->

Note: Cab drivers in London invested 3 years to learn streets to predict the fasted route. Navigation tools get close or better at low cost per prediction. While drivers' skills don't degrade, they now compete with many others that use AI to enhance skills; human prediction no longer scarce commodity.

At the same time, the value of human judgement increases. Making more decisions with better inputs, specifying the objective.

Picture source: https://pixabay.com/photos/cab-oldtimer-taxi-car-city-london-203486/

----
## Predictions vs Judgement

<!-- colstart -->
Predictions are an input to decision making under uncertainty

Making the decision requires judgement (determining relative payoffs of decisions and outcomes)

Judgement often left to humans ("value function engineering")

ML may learn to predict human judgment if enough data
<!-- col -->

```mermaid
graph LR;
p["Predict cancer?"] -->|yes| o;
p-->|no| o2;
o["cancer?"] -->|yes| x1["+"]
o -->|no| x2["-"]
o2["cancer?"] -->|yes| x3["-"]
o2-->|no| x4["+"]
```

*Determine value function from value of each outcome and probability of each outcome*
<!-- colend -->

----
## Automation with predictions

* Automated predictions scale much better than human ones
* Automating prediction vs predict judgement
* Value from full and partial automation, even with humans still required
* Highest return with full automation
    - Tasks already mostly automated, except predictions (e.g. mining)
    - Increased speed through automation (e.g., autonomous driving)
    - Reduction in wait time (e.g., space exploration)
* Liability concerns may require human involvement

----
## Automation in Controlled Environments

![Trucks in a Mine](mine.jpg)


Note: Source https://pixabay.com/photos/truck-giant-weight-mine-minerals-5095088/

----
## The Cost and Value of Data

* (1) Data for training, (2) input data for decisions, (3) telemetry data for continued improving
* Collecting and storing data can be costly (direct and indirect costs, including reputation/privacy)
* Diminishing returns of data: at some point, even more data has limited benefits
* Return on investment: investment in data vs improvement in prediction accuracy
* May need constant access to data to update models

----
## Where to use AI?

* Decompose tasks to identify the use of (or potential use of) predictions
* Estimate the benefit of better/cheaper predictions
* Specify exact prediction task: goals/objectives, data 
* Seek automation opportunities, analyze effects on jobs (augmentation, automate steps, shift skills, see taxis)
* Focus on steps with highest return on investment


----
![AI Canvas](predictionmachines_aicanvas.svg)

<!-- references -->

🕮 Ajay Agrawal, Joshua Gans, Avi Goldfarb. “[Prediction Machines: The Simple Economics of Artificial Intelligence](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/6lpsnm/alma991019698987304436)” 2018 
----
## Cost Per Prediction

*What contributes to the average cost of a single prediction?*

Examples: Credit card fraud detection, product recommendations on Amazon

<!-- discussion -->

----
## Cost Per Prediction

* Useful conceptual measure, factoring in all costs
    - Development cost
    - Data aquisition
    - Learning cost, retraining cost
    - Operating cost
    - Debugging and service cost
    - Possibly: Cost of deadling with incorrect prediction consequences (support, manual interventions, liability)
    - ...

----
## AI Risks

* Discrimination and thus liability
* Creating false confidence when predictions are poor
* Risk of overall system failure, failure to adjust
* Leaking of intellectual property
* Vulnerable to attacks if learning data, inputs, or telemetry can be influenced
*
* Societal risks
    - Focus on few big players (economies of scale), monopolization, inequality
    - Prediction accuracy vs privacy

---
## Discussion: Feasible ML-Extensions
<!-- smallish -->
Discuss in groups

Each group pick a popular open-source system (e.g., Firefox, Kubernetis, VS Code, WordPress, Gimp, Audacity)

Think of possible extensions with and without machine learning

Report back 1 extension that would benefit from ML and one that would probably not

10 min


Guiding questions: 
* ML Suitable: *Big problem? Open ended? Time changing? Hard? Partial system viable? Data continuously available? Influence objectives? Cost effective?*
* ML Profitable: *Prediction opportunities, cost per prediction, data costs, automation potential*










---
# System Goals

----
## Layers of Success Measures

* Organizational objectives: Innate/overall goals of the organization
* Leading indicators: Measures correlating with future success, from the business' perspective
* User outcomes: How well the system is serving its users, from the user's perspective
* Model properties: Quality of the model used in a system, from the model's perspective

**Some are easier to measure then others (telemetry), some are noisier than others, some have more lag**

<!-- split -->

```mermaid
graph TD;
MP(Model properties) --> UO(User outcomes)
UO --> LI(Leading indicators)
LI --> OO(Organizational objectives)
```

----
## Organizational Objectives

*Innate/overall goals of the organization*

* Business
    * current revenue, profit
    * future revenue, profit
    * reduce risk
* Non-Profits
    - Lives saved, animal welfare increased
    - CO2 reduced, fires averted
    - Social justice improved, well-being elevated, fairness improved

**accurate models themselves are not a goal**

**AI may only very indirectly influence such organizational objectives, influence hard to quantify, lagging measures**


----
## Breaking Down Processes

Break overall goals along processes

* Break workflow into tasks
* Identify decisions in tasks
* Evaluate benefit of AI for prediction or automation
* Evaluate the influence of improving some tasks on process

Maintain mapping from task-specific goals to system goals


----
## Leading Indicators

*Measures correlating with future success, from the business' perspective*

* Customers sentiment, customers liking the products (e.g., through surveys, rating)
* Customer engagement, regular use, time spent on site, messages posted
* Growing user numbers, recommendations

**indirect proxy measures, lagging, bias**

**can be misleading (more daily active users => higher profits?)**


----
## User Outcomes

*How well the system is serving its users, from the user's perspective*

* Users receive meaningful recommendations, enjoying content
* Users making better decisions
* Users saving time due to system
* Users achieving their goals

**easier and more granular to measure, but only indirect relation to organization objectives**

----
## Model Properties

*Quality of the model used in a system, from the model's perspective*

* Model accuracy
* Rate and kinds of mistakes
* Successful user interactions
* Inference time
* Training cost

**not directly linked to business goals**

----
## Layering of Success Measures

*Example: Amazon shopping recommendations*

Closely watch model properties for degradation; optimize accuracy; ongoing

Weekly review user outcomes, e.g., sales, reviews returns

Monthly review trends of leading indicators, e.g., shopper loyalty

Quarterly ensure look at organizational objectives

**Telemetry?**

<!-- split -->

```mermaid
graph TD;
MP(Model properties) --> UO(User outcomes)
UO --> LI(Leading indicators)
LI --> OO(Organizational objectives)
```


----
## Success Measures in the Spotify Scenario?

[![Spotify Screenshot of (My) Personalized Playlists](spotify.png)](spotify.png)
<!-- .element: class="stretch" -->


<!-- split -->

```mermaid
graph TD;
MP(Model properties) --> UO(User outcomes)
UO --> LI(Leading indicators)
LI --> OO(Organizational objectives)
```

----
## Exercise: Automating Admission Decisions to Master's Program
<!-- smallish -->
Discuss in groups, breakout rooms

What are the *goals* behind automating admissions decisions?

**Organizational objectives, leading indicators, user outcomes, model properties?**

Report back in 10 min

<!-- discussion -->












---
# Excursion: Measurement

----
## What is Measurement?

* _Measurement is the empirical, objective assignment of numbers,
according to a rule derived from a model or theory, to attributes of
objects or events with the intent of describing them._ – Craner, Bond,
“Software Engineering Metrics: What Do They Measure and How Do We
Know?"

*   _A quantitatively expressed reduction of uncertainty based on one or more observations._ – Hubbard, “How to Measure Anything …"


----
## Everything is Measurable

* If X is something we care about, then X, by definition, must be
detectable.
    * How could we care about things like “quality,” “risk,” “security,” or “public image” if these things were totally undetectable, directly or indirectly?
    * If we have reason to care about some unknown quantity, it is because
we think it corresponds to desirable or undesirable results in some way.
* If X is detectable, then it must be detectable in some amount.
    * If you can observe a thing at all, you can observe more of it or less of it
* If we can observe it in some amount, then it must be
measurable.

*But: Not every measure is precise, not every measure is cost effective*

<!-- references -->

🕮 Douglas Hubbard, “[How to Measure Anything: finding the value of intangibles in business](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/1feg4j8/alma991019515498904436)" 2014


----
## On Terminology:

* *Quantification* is turning observations into numbers
* *Metric* and *measure* refer a method or standard format for measuring something (e.g., number of mistakes per hour)
    - Metric and measure synonmous for our purposes (some distinguish metrics as derived from multiple measures, or metrics to be standardizes measures)
* *Operationalization* is identifying and implementing a method to measure some factor (e.g., identifying mistakes from telemetry log file)



----
## The Maintainability Index

$max(0, (171 - 5.2 ln(HV) - 0.23 CC - 16.2 ln(LOC)*100/171))$
$<10$: low maintainability, $\leq 20$ high maintainability

![Maintainability Index in Visual Studio](maintainabilityindex.png)

<!-- references -->
Further reading: Arie van Deursen, [Think Twice Before Using the “Maintainability Index”](https://avandeursen.com/2014/08/29/think-twice-before-using-the-maintainability-index/), Blog Post, 2014

Note: The maintainability index is a machine learning classifier in the modern sense. The function was derived through linear regression from training data. Thresholds were defined at Microsoft manually.


----
## Measurement in Software Engineering

* Which project to fund?
* Need more system testing?
* Need more training?
* Fast enough? Secure enough? 
* Code quality sufficient?
* Which features to focus on?
* Developer bonus?
* Time and cost estimation? Predictions reliable?
<!-- split -->

## Measurement in Data Science

* Which model is more accurate?
* Does my model generalize or overfit?
* Now noisy is my training data?
* Is my model fair?
* Is my model robust?


----
## Measurement Scales
<!-- smallish -->
* Scale: The type of data being measured; dictates what sorts of analysis/arithmetic is legitimate or meaningful.
* Nominal: Categories ($=, \neq$, frequency, mode, ...)
  * e.g., biological species, film genre, nationality
* Ordinal: Order, but no meaningful magnitude ($<, >$, median, rank correlation, ...)
  * Difference between two values is not meaningful
  * Even if numbers are used, they do not represent magnitude!
  * e.g., weather severity, complexity classes in algorithms
* Interval: Order, magnitude, but no definition of zero ($+, -$, mean, variance, ...)
  * 0 is an arbitrary point; does not represent absence of quantity
  * Ratio between values are not meaningful
  * e.g., temperature (C or F)
* Ratio: Order, magnitude, and zero ($*, /, log, \sqrt{\ }$, geometric mean)
  * e.g., mass, length, temperature (Kelvin)

**Aside: Understanding scales of features is also useful for encoding or selecting learning strategies in ML**

----
## Decomposition of Measures
Often higher-level measures are composed from lower level measures

clear trace from specific low-level measurements to high-level metric

```mermaid
graph LR;
Maintainability --> Correctability;
Maintainability --> Testability;
Maintainability --> Expandability;
Correctability --> FC[Faults Count];
Testability --> SC[Statement Coverage];
Correctability --> Effort;
Testability --> Effort;
Expandability --> Effort;
Expandability --> CC[Change Count];
```


<!-- references -->
For design strategy, see [Goal-Question-Metric approach](https://en.wikipedia.org/wiki/GQM)

----
## Specifying Metrics

* Always be precise about metrics
    - "measure accuracy" -> "evaluate accuracy with MAPE"
    - "evaluate test quality" -> "measure branch coverage with Jacoco"
    - "measure execution time" -> "average and 90%-quantile response time for REST-API x under normal load"
    - "assess developer skills" -> "measure average lines of code produced per day and number of bugs reported on code produced by that developer"
    - "measure customer happyness" -> "report response rate and average customer rating on survey shown to 2% of all customers (randomly selected)"
* Ideally: An independent party should be able to independently set up infrastructure to measure outcomes

----
## Exercise: Specific Metrics for Spotify Goals?


* Organization objectives?
* Leading indicators?
* User outcomes?
* Model properties?
* What are their scales?

<!-- split -->

[![Spotify Screenshot of (My) Personalized Playlists](spotify.png)](spotify.png)
<!-- .element: class="stretch" -->


----
##  Correlation vs Causation

![causation1](causation1.png)

![causation2](causation2.png)

----
##  Correlation vs Causation

* In general, ML learns correlation, not causation
    * (exception: Bayesian networks, certain symbolic AI methods)
* To establish causality:
  * Develop a theory ("X causes Y") based on domain knowledge & independent data
  * Identify relevant variables
  * Design a controlled experiment & show correlation
  * Demonstrate ability to predict new cases
  
----
## Confounding Variables

<!-- colstart -->
```mermaid
graph TD;
IV[Independent Var.] -.->|spurious correlation| DV[Dependent Var.]
CV[Confounding Var.] -->|causal| DV
CV -->|causal| IV
```
<!-- col -->
```mermaid
graph TD;
IV[Coffee] -.->|spurious correlation| DV[Cancer]
CV[Smoking] -->|causal| DV
CV -->|causal| IV
```
<!-- colend -->

----
## Confounding Variables

* To identify spurious correlations between X and Y:
  * Identify potential confounding variables 
  * Control for those variables during measurement (randomize, fix, or measure + account for during analysis)
* Examples
  * Drink coffee => Pancreatic cancer?
  * Degree from high-ranked schools => Higher-paying jobs?
  
----
## Challenge: The streetlight effect

* A type of _observational bias_
* People tend to look for something where it’s easiest to do so
    - Use cheap proxy metrics, that only poorly correlate with goal?

![Streetlight](streetlight.jpg)

----
## Risks of Metrics as Incentives

* Metrics-driven incentives can:
  * Extinguish intrinsic motivation
  * Diminish performance
  * Encourage cheating, shortcuts, and unethical behavior
  * Become addictive
  * Foster short-term thinking
* Often, different stakeholders have different incentives!

**Make sure data scientists and software engineers share goals and success measures**

----
## On Incentives: University Rankings

![US News](us-news.jpg)

Notes:

* Originally: Opinion-based polls, but schools complained
* Data-driven model: Rank colleges in terms of "educational excellence"
* Input: SAT scores, student-teacher ratios, acceptance rates,
retention rates, alumni donations, etc.,

* What is (not) being measured? Any streetlight effect?
* Is the measured data being used correctly?
* Are incentives for using these data good? Can they be misused?

* Example 1
  * Schools optimize metrics for higher ranking (add new classrooms, nicer
  facilities)
  * Tuition increases, but is not part of the model!
  * Higher ranked schools become more expensive
  * Advantage to students from wealthy families
* Example 2
  * A university founded in early 2010's
  * Math department ranked by US News as top 10 worldwide
  * Top international faculty paid \$\$ as a visitor; asked to add affiliation
  * Increase in publication citations => skyrocket ranking!
  
----
## Measurement Validity

* Construct: Are we measuring what we intended to measure?
  * Does the abstract concept match the specific scale/measurement used?
  * e.g., IQ: What is it actually measuring?
  * Other examples: Pain, language proficiency, personality...
* Predictive: The extent to which the measurement can be used to explain some other characteristic of the entity being measured
    * e.g., Higher SAT scores => higher academic excellence?
* External validity: Concerns the generalization of the findings to contexts and environments, other than the one studied
    * e.g., Drug effectiveness on test group: Does it hold over the general public? 

----
## Successful Measurement Program

* Set solid measurement objectives and plans
* Make measurement part of the process
* Gain a thorough understanding of measurement
* Focus on cultural issues
* Create a safe environment to collect and report true data
* Cultivate a predisposition to change
* Develop a complementary suite of measures














---
# Outlook: Measurement with Telemetry

----
## Key Challenge: Telemetry

* Some goals can be quantified easily, others not so much
* Be creative in data sources (telemetry)
    - Existing logs and measures
    - Logging additional information
    - User surveys, feedback mechanisms
* Often only proxy measures, sometimes delayed, often only samples

![Skype feedback mechanism](skype.jpg)

----
## How to Measure System Success?

<!-- colstart -->

[![Spotify Screenshot of (My) Personalized Playlists](spotify.png)](spotify.png)

<!-- col -->

![Cancer Detection](mri.jpg)

<!-- col -->

![Temi](temi.png)

<!-- colend -->













---
# Summary

* Be deliberate about when to use AI/ML
* Understand the business case for AI (cheap predictions, automation, cost per prediction)
* Identify and break down system goals, define concrete measures
* Telemetry to quantify system goals
* Key concepts and challenges of measurement
