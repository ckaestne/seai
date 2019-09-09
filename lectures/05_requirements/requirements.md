---
author: Eunsuk Kang
title: "17-445: Requirements and Risk Analysis"
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

---
# Mistakes in AI

----
## Types of Errors

* Wrong output

----
## Impact of Errors

* Safety

* Security

---
# Risk Analysis

----
## Risks

* Risk = Impact * Likelihood

----
## Fault Tree Analysis (FTA)

* What is FTA?

* A technique for systematically identifying root causes of a failure

* FTA as a investigative tool

* FTA as a decision making tool

----
## Basic Definitions

* Event
	* Top Event
* Gate

----
## FTA: Example

* Small light failure example

----
## Analysis

* What can we do with FTA?
  * Qualitative
  * Quantitative

----
## Minimal Cut Analysis

* Cut

* MinCut

----
## Failure Likelihood Analysis

* Probabilitistic analysis

----
## FTA Process

1. Specify the system design
   * Environment + machine domains 
   * Phenomena
2. Identify the top event(s)   
3. Construct the fault tree
4. Analyze the tree
   * Identify minimal cut sets
5. Consider alternative designs
6. Repeat

----
## Case Study: Infusion Pump

* Construct a FTA for the top event: Patient overdosed

---
# Summary
