# 17-445/645 Software Engineering for AI-Enabled Systems -- Learning Goals

## Lecture: Introduction and Motivation

Content:

* Lecture illustrates traditional view of machine learning and contrasts it with the challenges of building systems. Characterizes stakeholders involved and their goals. Overview of qualities. Outlines challenges to be discussed
* Brief distinction AI vs ML and typical classes of AI components
* Key distinction specifications vs learning from data, but also success in engineering systems from imprecise specifications and unreliable components
* Syllabus and class structure

Learning goals:

* Explain the typical machine-learning process
* Illustrate the challenges in engineering an AI-enabled system beyond accuracy
* Summarize the respective goals and challenges of software engineers vs data scientists

Assignment:

* Case study analysis of a troubled ML project


## Lecture: Components of an AI-Enabled System

Overview:

* Components and corresponding challenges (experience, intelligence, orchestration)
* Overview of design options and automation degrees, e.g., forcefulness of the experience
* Steps of the ML pipeline, including design options and automation

Learning goals:

* Describe the components of a typical machine learning pipeline and their responsibilities and challenges
* Describe the typical components relating to AI in an AI-enabled system and typical design decisions to be made
* Illustrate the design space for AI-enabled systems for a given sample system

Assignment:

* Build a simple predictive ML model to gain experience with all involved steps

Readings:

* ... EIS chapter

## Lecture: Dealing with Mistakes

Overview:

* Specifications or lack thereof for ML-components, probabilistic specifications in certain AI components; inevitability 
* Introduction to risk analysis, fault trees, and hazard analysis; writing of requirements
* Overview of fault handling strategies (redundancies, voting, fallback, undo, forcefulness, ...)

Learning goals:

* Analyze the number of ways a mistake in an AI component can influence the behavior of a system
* Evaluate risk of a mistake from the AI component using fault trees
* Design and justify a mitigation strategy for a concrete system

Assignment:

* Write requirements and plan mechanisms for dealing with mistakes

## Lecture: Tradeoffs among AI Techniques (2 lectures)

Overview

* Survey quality attributes of interest (e.g., accuracy, model size, inference time, learning time, robustness)
* Survey of ML and symbolic AI techniques and their tradeoffs

Learning goals:

* Describe the most common models and learning strategies used for AI components and summarize how they work
* Organize and prioritize the relevant qualities of concern for a given project
* Plan and execute an evaluation of the qualities of alternative AI components for a given purpose

Assignment:

* Present tradeoff analysis among two techniques (prepare blog post + short presentation); use both and measure actual qualities of either solution to the degree possible

## Lecture: Updating Models

Overview:

* Introduction to software architecture and domain-specific modeling
* Importance of model updates; threats from stale data and data drift
* Architectural discussions: when to learn, incremental vs from scratch, where the model lives, costs for updates vs costs from stale models, client-side vs server-side models vs hybrid approaches

Learning goals:

* Create an architectural model describing the relevant characteristics to reason about update frequency and costs
* Critique the decision of where an AI model lives (e.g., cloud vs edge vs hybrid), considering the relevant tradeoffs 
