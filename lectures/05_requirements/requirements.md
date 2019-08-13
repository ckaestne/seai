---
author: Eunsuk Kang
title: "17-445: Requirements and Dealing with Mistakes"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Eunsuk Kang"
---  

# Requirements and Dealing with Mistakes

Eunsuk Kang

<!-- references -->

Required reading: Hulten, Geoff. "Building Intelligent Systems: A
Guide to Machine Learning Engineering." (2018), Chapters 6--8, and 24.

---
# Learning Goals

* Understand ways a mistake in an AI component can influence the behavior of a system

* Evaluate risk of a mistake from the AI component using fault trees

* Design and justify a mitigation strategy for a concrete system

---
# Example System

---
# Requirements for an AI-Enabled System

----
## Requirements Specification

----
## Machine vs World

* Why we must consider the world

* Example of goals that do not consider the world

----
## Defining goals

* Takes into account all relevant stakeholders

* Achievable 

* Measurable (optimizable)

----
## Example: Anti-Phishing System

* From the textbook, Chapter 4

---
# Mistakes in AI

----
## Types of Errors

* Wrong output

----
## Impact of Errors

* Safety

* Security

----
## Safety Engineering 101

* Quick intro

----
## Risk Analysis

* What is risk analysis?

----
## Fault Tree Analysis (FTA)

* What is FTA?

---
# Dealing with Errors

----
## Designing for Failures

* Resilience engineering

----
## Fault Tolerance Techniques

* Redundancies (caution: N-version programming)

* Voting

* Fallback

* Undo

* Prompt user instead of automate (for critical actions)

---
# Summary
