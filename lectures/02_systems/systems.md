---
author: Christian Kaestner
title: "17-445: From Models to AI-Enabled Systems"
semester: Summer 2020
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---  

# From Models to Production Systems (Systems Thinking)

Christian Kaestner

<!-- references -->

* Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 5, 7, and 8.

---

# Learning goals

* Explain the consequences of the shift from deductive to inductive reasoning for abstraction and composition
* Explain how machine learning fits into the larger picture of building and maintaining production systems
* Explain the modularity implications of having machine-learning components without specifications
* Describe the typical components relating to AI in an AI-enabled system and typical design decisions to be made





---
# Traditional vs AI-based Software Systems


----
## Complexity in Engineered Systems

![Airplane](airplane.jpg)

* Automobile: ~30,000 parts; Airplane: ~3,000,000 parts
* MS Office: ~ 40,000,000 LOCs; Debian: ~ 400,000,000 LOCs
* How do we build such complex systems?

----
## Managing Complexity in Software

* **Abstraction**: Hide details & focus on high-level behaviors
* **Reuse**: Package into reusable libraries & APIs with well-defined _contracts_
* **Composition**: Build large components out of smaller ones

```java
/**
 * compute deductions based on provided adjusted 
 * gross income and expenses in customer data.
 *
 * see tax code 26 U.S. Code A.1.B, PART VI
 *
 * Adjusted gross income must be positive; 
 * returned deductions are not negative.
 */
float computeDeductions(float agi, Expenses expenses) {
  ...
}
```


----
## Divide and Conquer

* Human cognitive ability is limited
* Decomposition of software necessary to handle complexity
* Allows division of labor
* Deductive reasoning, using logic

![Tax computation system with three components](tax-decomposition.png)
<!-- .element: class="stretch" -->


----
## Debugging and Assigning Blame

* Each component has own specification
* For each input, specification indicates whether output correct

```java
/**
 * compute deductions based on provided adjusted 
 * gross income and expenses in customer data.
 *
 * see tax code 26 U.S. Code A.1.B, PART VI
 */
float computeDeductions(float agi, Expenses expenses);
```

![Tax computation system with three components](tax-decomposition.png)
<!-- .element: class="stretch" -->

----
## Strict Correctness Assumption

* Specification determines which outputs are correct/wrong
* Not "pretty good", "95% accurate", or "correct for 98% of all users"
* A single wrong result indicates a bug in the system

![Tax computation system with three components](tax-decomposition.png)
<!-- .element: class="stretch" -->

Note: A single wrong tax prediction would be a bug. No tolerance of occasional wrong predictions, approximations, nondeterminism.

----
## Image Captioning Algorithm


![Image captioning one step](imgcaptioning.png)

```java
/**
  ????
*/
String getCaption(Image img);
```

Note: We do not know how to program this or specify this.
No way of saying whether caption is "correct" for input, but defer to human judgement.

----
## Learning Image Captioning Algorithm

![Image captioning with ML](imgcaptioningml.png)


*Learning rules by fitting to examples, no specification, inductive reasoning*

Note: "Rules"/algorithm learned from data. Still no specification. Best fit to given training data.

----
## Correctness of Model?

<!-- colstart -->
![Example of wrong caption](imgcaptioning-cake.png)
<!-- col -->
> All models are wrong. Some are useful.
<!-- colend -->

<!-- references -->
Image from: Nushi, Besmira, Ece Kamar, Eric Horvitz, and Donald Kossmann. "[On human intellect and machine failures: troubleshooting integrative machine learning systems](http://erichorvitz.com/human_repair_AI_pipeline.pdf)." In Proc. AAAI. 2017.

Note: Human judgment needed. Furthermore, a single bad example is not a problem.

----
## Weak Correctness Assumptions

* Often no reliable ground truth (e.g. human judgment)
* Accepting that mistakes will happen, hopefully not to frequently; "95% accuracy" may be pretty good
* More confident for data similar to training data

![Example of wrong caption](imgcaptioning-cake.png)
<!-- .element: class="stretch" -->


----
## Specifications in Machine Learning?

* Usually clear specifications do not exist -- we use machine learning exactly because we do not know the specifications
* Can define correctness for some data, but not general rules; sometimes can only determine correctness after the fact
* Learning for tasks for which we cannot write specifications
  * Too complex
  * Rules unknown
* ML will learn rules/specifications (inductive reasoning), often not in a human-readable form, but are those the right ones?
* 
* Usually goals used instead --> maximize a specific objective


----

[![Contrasting inductive and deductive reasoning](inductive.png)](https://danielmiessler.com/blog/the-difference-between-deductive-and-inductive-reasoning/)
<!-- .element: class="stretch" -->


(Daniel Miessler, CC SA 2.0)

----

## Deductive Reasoning

* Combining logical statements following agreed upon rules to form new statements
* Proving theorems from axioms
* From general to the particular
* *mathy reasoning, eg. proof that π is irrational*
* 
* Formal methods, classic rule-based AI systems, expert systems

<!-- split -->

## Inductive Reasoning

* Constructing axioms from observations
* Strong evidence suggests a rule
* From particular to the general
* *sciency reasoning, eg. finding laws of nature*
* 
* Most modern machine learning systems, statistical learning


----
## Consequences from Lack of Specifications

<!-- discussion -->


Note: Breaks many traditional assumptions and foundations for compositional reasoning and divide and conquer

Poorly understood interactions between models:
Ideally, develop models separately & compose together.
In general, must train & tune together.

----
## Decomposing the Image Captioning Problem?

![Image of a snowboarder](snowboarder.png)

Note: Using insights of how humans reason: Captions contain important objects in the image and their relations. Captions follow typical language/grammatical structure

----
## State of the Art Decomposition (in 2015)

![Captioning example](imgcaptioningml-decomposed.png)

<!-- references -->
Example and image from: Nushi, Besmira, Ece Kamar, Eric Horvitz, and Donald Kossmann. "[On human intellect and machine failures: troubleshooting integrative machine learning systems](http://erichorvitz.com/human_repair_AI_pipeline.pdf)." In Proc. AAAI. 2017.


----
## Blame assignment?

![blame assignment problem](imgcaptioningml-blame.png)

<!-- references -->
Example and image from: Nushi, Besmira, Ece Kamar, Eric Horvitz, and Donald Kossmann. "[On human intellect and machine failures: troubleshooting integrative machine learning systems](http://erichorvitz.com/human_repair_AI_pipeline.pdf)." In Proc. AAAI. 2017.

----
## Nonmonotonic errors

![example of nonmonotonic error](imgcaptioningml-nonmonotonic.png)

<!-- references -->
Example and image from: Nushi, Besmira, Ece Kamar, Eric Horvitz, and Donald Kossmann. "[On human intellect and machine failures: troubleshooting integrative machine learning systems](http://erichorvitz.com/human_repair_AI_pipeline.pdf)." In Proc. AAAI. 2017.


----
## Takeaway: Shift in Design Thinking?

Breaking traditional decomposition and reasoning strategies... 

From deductive reasoning to inductive reasoning...

From clear specifications to goals...

From guarantees to best effort...

**What does this mean for software engineering?**

**For decomposing software systems?** 

**For correctness of AI-enabled systems?** 

**For safety?**

**For design, implementation, testing, deployment, operations?**


*These problems are not new, but are exacerbated by the increasing use of ML!*






---
# ML Models as Part of a System

----
## Why do we care about image captioning?

![Image captioning one step](imgcaptioning.png)

----
## Machine learning as (small) component in a system

<!-- colstart -->
![Tax system architecture with an ML component](tax-with-ml.png)
<!-- col -->
[![Audit risk meter](audit-risk-meter.png)](https://ttlc.intuit.com/community/choosing-a-product/help/about-the-audit-risk-meter/00/25924)
<!-- colend -->

Note: Traditional non-ML tax software, with an added ML component for audit risk estimation

----
## Machine learning as (core) component in a system

<!-- colstart -->
![Transcription system architecture](transcriptionarchitecture.png)
<!-- col -->
![Screenshot of Temi transcription service](temi.png)
<!-- colend -->

Note: Transcription service, where interface is all built around an ML component


----
## Many more examples:

* Product recommendations on Amazon
* Surge price calculation for Uber
* Inventory planning in Walmart
* Search for new oil fields by Shell
* Adaptive cruise control in a car
* Smart app suggestion in Android
* Fashion trends prediction with social media data
* Suggesting whom to talk to in a presidential campain
* Tracking and predicting infections in a pandemic
* Adaptively reacting to network issues by a cell phone provider
* Matching players in a computer game by skill
* ...
* 
* Some for end users, some for employees, some for expert users
* Big and small components of a larger system


----
## Model vs System Goal?

![Image captioning one step](imgcaptioning.png)

----
## Model vs System Goal?

![Transcription system architecture](transcriptionarchitecture.png)


----
## More Accurate Predictions may not be THAT Important

* "Good enough" may be good enough
* Prediction critical for system success or just an gimmick?
* Better predictions may come at excessive costs 
    - need way more data, much longer training times
    - privacy concerns
* Better user interface ("experience") may mitigate many problems
    - e.g. explain decisions to users
* Use only high-confidence predictions?


----

## Beyond Software: Impact on Our Society

![Predictive policing](predictive-policing.png)



----
## Machine learning that matters

* 2012 essay lamenting focus on algorithmic improvements and benchmarks in ML
  - focus on standard benchmark sets, not engaging with problem: Iris classification, digit recognition, ...
  - focus on abstract metrics, not measuring real-world impact: accuracy, ROC
  - distant from real-world concerns
  - lack of follow-through, no deployment, no impact
* Failure to *reproduce* and *productionize* paper contributions common
* Ignoring design choices in how to collect data, what problem to solve, how to design human-AI interface, measuring impact, ...
*
* Should focus on making impact -- requires building systems


<!-- references -->

Wagstaff, Kiri. "Machine learning that matters." In Proceedings of the 29 th International Conference on Machine Learning, (2012).




----
## On Terminology

* There is no standard term for referring to building systems with AI components
* "Production ML Systems", "AI-Enabled Systems", "ML-Enabled Systems" or "ML-Infused Systems"; SE4AI, SE4ML
* sometimes "AI Engineering" (but often used with a data-science focus)
* sometimes "ML Systems Engineering" (but often this refers to building distributed and scalable ML learning and data storage platforms)
* "AIOps" ~ using AI to make automated decisions in operations; "DataOps" ~ use of agile methods and automation in business data analytics; "MLOps" ~ technical infrastructure for operating AI-based products and on deploying updates

























---
# Systems Thinking



----
## Repeat: Machine learning as component in a system

![Transcription system architecture](transcriptionarchitecture.png)


----
## The System Interacts with Users

[![Audit risk meter](audit-risk-meter.png)](https://ttlc.intuit.com/community/choosing-a-product/help/about-the-audit-risk-meter/00/25924)

Note: Audit risk meter from Turbo-Tax

----
## The System Interacts with the World

![Smart Toaster](toaster.jpg)


----
## The System Interacts with the World

![Crime Map](crime-map.jpg)

* Model: Use historical data to predict crime rates by neighborhoods
* Used for predictive policing: Decide where to allocate police patrol

----
## System <-> World = Feedback Loops?

![Crime Map](crime-map.jpg)


```mermaid
graph LR;
h[Historic bias] --> Data
Data -->|ML| Model
Model --> Predictions
Predictions -->|influence| Data
```


----
## ML Predictions have Consequences

* Assistance, productivity, creativity
* Manipulation, polarization, discrimination
* Feedback loops


----
## Safety is a System Property

* Code/models are not unsafe, cannot harm people
* Systems can interact with the environment in ways that are unsafe

![Smart Toaster](toaster.jpg)

----
## Safety Assurance in the Model/outside the Model

> Goal: Ensure smart toaster does not burn the kitchen

<!-- discussion -->

----
## Safety Assurance in the Model/outside the Model

<!-- colstart -->
* In the model
  - Ensure maximum toasting time
  - Use heat sensor and past outputs for prediction
  - Hard to make guarantees
* Outside the model (e.g., "guardrails")
  - Simple code check for max toasting time
  - Non-ML rule to shut down if too hot
  - Hardware solution: thermal fuse

<!-- col -->

![Thermal fuse](thermalfuse.png)
(Image CC BY-SA 4.0, C J Cowie)
<!-- colend -->

----
## Model vs System Properties

* Similar to safety, many other qualities should be discussed at model **and** system level
  - Security
  - Privacy
  - Transparency, accountability
  - Maintainability
  - Scalability, energy consumption
  - Impact on system goals
  - ...




----
## Thinking about Systems

* Holistic approach, looking at the larger picture, involving all stakeholders
* Looking at relationships and interactions among components and environments
    - Everything is interconnected
    - Combining parts creates something new with emergent behavior
    - Understand dynamics, be aware of feedback loops, actions have effects
* Understand how humans interact with the system

> A system is a set of inter-related components that work together in a particular environment to perform whatever functions are required to achieve the system's objective -- Donella Meadows

<!-- references -->
Leyla Acaroglu. "[Tools for Systems Thinkers: The 6 Fundamental Concepts of Systems Thinking](https://medium.com/disruptive-design/tools-for-systems-thinkers-the-6-fundamental-concepts-of-systems-thinking-379cdac3dc6a)." Blogpost 2017

----
## System-Level Challenges for AI-Enabled Systems

* Getting and updating data, concept drift, changing requirements
* Handling massive amounts of data
* Interactions with the real world, feedback loops
* Lack of modularity of AI components, lack of specifications, nonlocal effects
* Deployment and maintenance
* Versioning, debugging and incremental improvement
* Keeping training and operating cost manageable
* Interdisciplinary teams
* Setting system goals, balancing stakeholders and requirements
* ...










---
# Designing Intelligent Experiences

(Human-AI Interaction)

----#
# AI predictions should influence the world

* Smart toaster
* Automated slide design
* Product or music recommendations
* Feed curation in social media or news
* Recidivism prediction
* Health monitoring
* Transcription services
* Image search engine
* Self-driving cars
* Smart home
*
* Interact with the world through actuators (smart devices) or by influencing people



----
## Designing Intelligent Experiences

* How to use the output of a model's prediction (for a objective)?
* Design considerations:
    - How to present prediction to a user? Suggestions or automatically take actions?
    - How to effectively influence the user's behavior toward the system's goal?
    - How to minimize the consequences of flawed predictions?
    - How to collect data to continue to learn from users and mistakes?
* Balancing at least three **system-level** outcomes:
    - Achieving objectives
    - Protection from mistakes
    - Collecting data for training


----
## Presenting Intelligence

* Automate: Take action on user's behalf

* Prompt: Ask the user if an action should be taken

* Organize: Display a set of items in an order

* Annotate: Add information to a display

* Hybrids of these


----
## Factors to Consider


* **Forcefulness**: How strongly to encourage taking an action (or even automate it)?
* **Frequency**: How often to interact with the user?
* **Value**: How much does a user (think to) benefit from the prediction?
* **Cost**: What is the damage of a wrong prediction?





----
## Breakout Discussion: Experience Design


<!-- colstart -->

Fall detection for elderly people:

![Smart watch](smartwatch.jpg)


<!-- col -->

Safe browsing: Blocking malicious web pages

![Safe browsing warning](warning.png)

<!-- colend -->


* How do we present the intelligence to the user?
* Consider system goals, forcefulness, frequency, value of correct and cost of wrong predictions

Notes:
Devices for older adults to detect falls and alert caretaker or emergency responders automatically or after interaction. Uses various inputs to detect falls.
Read more: [How fall detection is moving beyond the pendant](https://www.mobihealthnews.com/content/how-fall-detection-moving-beyond-pendant), MobiHealthNews, 2019


----
## Collecting Feedback

![Safe Browsing Feedback](safe-browsing-feedback.png)






---

# Operating Production ML Systems

(deployment, updates)

----
## Things change...


<!-- colstart -->

* Newer better models released
  - Better model architectures
  - More training data
* Goals and scope change
  - More domains supported
  - Better recognition of dialects
* Model training due to drift
  - New terms (jargon) emerge in domain
  - Increased adoption in region with dialect
* Online experimentation


<!-- col -->

![Architecture diagram of transcription service; many components, not just ML](transcriptionarchitecture.png)


<!-- colend -->
----
## Things change...


<!-- colstart -->

<!-- discussion -->

<!-- col -->

*Reasons for change in audit risk prediction?*
![Audit prediction](audit-risk-meter.png)


<!-- colend -->

----
## Monitoring in Production

Design for telemetry

<!-- colstart -->
![Safe Browsing Feedback](safe-browsing-feedback.png)
<!-- col -->
![Safe Browsing Statistics](safe-browsing-stats.png)
<!-- colend -->


----
## Monitoring in Production


<!-- colstart -->

<!-- discussion -->

<!-- col -->

*What and how to monitor in audit risk prediction?*
![Audit prediction](audit-risk-meter.png)


<!-- colend -->

----
## Pipeline Thinking


![Pipeline](pipeline.png)

<!-- references -->

* Graphic: Amershi et al. "[Software engineering for machine learning: A case study](https://www.microsoft.com/en-us/research/uploads/prod/2019/03/amershi-icse-2019_Software_Engineering_for_Machine_Learning.pdf)." In Proc ICSE-SEIP, 2019. 


----
## Design with Pipeline and Monitoring in Mind

![Architecture diagram of transcription service; many components, not just ML](transcriptionarchitecture2.png)

----
## Shifting from Models to Pipelines is Challenging

Across interviews with enterprise ML teams:

* Data scientists often focus on modeling in local environment, model-centric workflow
* Rarely robust infrastructure, often monolithic and tangled
* Challenges in deploying systems and integration with monitoring, streams etc
* 
* Shifting to pipeline-centric workflow challenging
* Requires writing robust programs, slower, less exploratory
* Standardized, modular infrastructure 
* 
* Big conceptual leap, major hurdle to adoption

<!-- references -->

O'Leary, Katie, and Makoto Uchida. "[Common problems with Creating Machine Learning Pipelines from Existing Code](https://research.google/pubs/pub48984.pdf)." Proc. Third Conference on Machine Learning and Systems (MLSys) (2020).

---
# Summary

* ML changes many engineering assumptions; from deductive to inductive reasoning; consequences for composition and abstraction
* Production AI-enabled systems require a *whole system perspective*, beyond just the model
* Engineering pipelines not models
* Large design space for user interface (intelligent experience): forcefulness, frequency, telemetry
* Quality at a *system* level: safety beyond the model, beyond accuracy


---
# Recommended Readings

* 🗎 Wagstaff, Kiri. "[Machine learning that matters](https://arxiv.org/abs/1206.4656)." In Proceedings of the 29th International Conference on Machine Learning, (2012).
* 🗎 Sculley, David, Gary Holt, Daniel Golovin, Eugene Davydov, Todd Phillips, Dietmar Ebner, Vinay Chaudhary, Michael Young, Jean-Francois Crespo, and Dan Dennison. "[Hidden technical debt in machine learning systems](http://papers.nips.cc/paper/5656-hidden-technical-debt-in-machine-learning-systems.pdf)." In Advances in neural information processing systems, pp. 2503-2511. 2015.
* 🗎 Nushi, Besmira, Ece Kamar, Eric Horvitz, and Donald Kossmann. "[On human intellect and machine failures: troubleshooting integrative machine learning systems](http://erichorvitz.com/human_repair_AI_pipeline.pdf)." In *Proceedings of the Thirty-First AAAI Conference on Artificial Intelligence*, pp. 1017-1025. 2017.
* 🗎 O'Leary, Katie, and Makoto Uchida. "[Common problems with Creating Machine Learning Pipelines from Existing Code](https://research.google/pubs/pub48984.pdf)." Proc. Third Conference on Machine Learning and Systems (MLSys) (2020).
* Blog post: [On the process for building software with ML components](https://ckaestne.medium.com/on-the-process-for-building-software-with-ml-components-c54bdb86db24)