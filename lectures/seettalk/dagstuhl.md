---
author: Christian Kaestner
title: "Software Engineering for AI-Enabled Systems"
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian
Kaestner & Eunsuk Kang"
---

# Teaching Software Engineering for AI-Enabled Systems

Eunsuk Kang and Christian Kaestner

---

## Software Engineering for AI-Enabled Systems

----


## Software Engineering for AI-Enabled Systems != SE-4-ML-frameworks

![SciKit Learn Logo](scikit.png)



----


## Software Engineering for AI-Enabled Systems != ML4SE

![Code Completion with AI](codecompl.png)


----
## Software Engineering for AI-Enabled (AI-ML-based, ML-infused) Systems

![](temi.png)

(SE 4 ML-enabled systems)


---
## Software Engineering

> Software engineering is the branch of computer science that creates practical, cost-effective solutions to
computing and information processing problems, preferentially by applying scientific knowledge,
developing
 software systems in the service of mankind. 

Engineering judgements under limited information and resources

A focus on design, tradeoffs, and the messiness of the real world

Many qualities of concern: cost, correctness, performance, scalability, security, maintainability, ...



**"it depends..."**


<!-- references -->
Mary Shaw. ed. Software Engineering for the 21st Century: A basis for rethinking the curriculum. 2005.


----
## Most AI/ML Courses

Focus narrowly on modeling techniques or building models

Using static datasets, evaluating accuracy

Little attention to software engineering aspects of building complete systems


(see Antonio's talk)


----

![](temi.png)

----
## Example Software Engineering Concerns


* How to build robust AI pipelines and facilitate regular model updates? 
* How to deploy and update models in production? 
* How to evaluate data and model quality in production? 
* How to deal with mistakes that the model makes and manage associated risk?
* How to trade off between various qualities, including learning cost, inference time, updatability, and interpretability? 
* How to design a system that scales to large amounts of data? 
* How to version models and data?
* How to manage interdisciplinary teams with data scientists, software engineers, and operators?


---

![Overview](overview.png)

---
## What's different?


* Missing specifications
* Environment is important (feedback loops, data drift)
* Nonlocal and nonmonotonic effects 
* Testing in production
* Data management, versioning, and provenance

----
## Really different?


* Missing specifications -- *implicit, vague specs very common; safe systems from unreliable components*
* Environment is important -- *the world vs the machine*
* Nonlocal and nonmonotonic effects -- *feature interactions, system testing* 
* Testing in production -- *continuous deployment, A/B testing*
* Data management, versioning, and provenance -- *stream processing, event sourcing, data modeling*

----
![Technical Debt](debt.jpg)

----

> While developers of simple traditional systems may get away with poor practices, most developers of AI-enabled systems will not.


---

![Overview](overview.png)

---
## Assignments

Break the habit of modeling in notebooks on static datasets

Design for realistic "production" setting: deployment, experimentation in production, data drift and feedback loops

Movie recommendation scenario, simulating 160k users watching movies in real time

![Assignment infrastructure](sim.png)

---
## Aside: DevOps

![DevOps](devops.png)


---
## Readings

All lecture material (except simulator): https://github.com/ckaestne/seai

Annotated bibliography: https://github.com/ckaestne/seaibib

ICSE SEET'20 paper

<!-- split -->
![DIS](book.webp)

---
## Suggested Topics

* Identifying the right requirements for fairness, robustness, privacy, security, usefulness, ...
* Supporting exploratory programming
* Modularity, nonmodularity, and feature interactions 
* Versioning of data and models; provenance
* Designing telemetry
* Testing and experimenting in production
* Architectural reasoning and deployment
* Ensuring safety: Designing fallback strategies, railguards, ...
* Designing interactions with users (forcefulness of experience)
* Monitoring, data drift, feedback loops, data quality
* Quality assurance of ML pipeline