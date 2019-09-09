# Individual Assignment 2: Requirements and Risks

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will get practice on how to systematically identify system requirements and risks of their failures in an AI-enabled system. In particular, you will learn to (a) make a clear distinction between the roles that environmental and machine domains play in system dependability, and (2) apply fault tree analysis (FTA) to identify potential risks in a case study scenario involving a self-driving vehicle.

Learning goals:
* Understand the role of the environment in establishing system requirements.
* Learn to systematically identify risks and potential causes in an AI-enabled system.
* Understand the strengths and limitations of FTA.

## Tasks and Questions

1. [Apollo](http://apollo.auto/index.html) is an open-source software platform for self-driving vehicles. Read the [Software Architecture specification for Apollo 3.5](https://github.com/ApolloAuto/apollo/blob/master/docs/specs/Apollo_3.5_Software_Architecture.md) and familiarize yourself with the major components of the system. You do NOT need to understand the details of the underlying implementation. Instead, focus on what functionality each of the components is responsible for and how they interact with each other.

2. Read the [preliminary report by the National Transportation Safety Board (NTSB)](https://www.ntsb.gov/investigations/AccidentReports/Reports/HWY18MH010-prelim.pdf) on the Uber self-driving car accident in 2018. Keep in mind that the report is not conclusive, and the investigation is still on-going, and so there may be multiple possible underlying causes of the failure to consider.

Answer the questions below. Wherever reasonable, provide evidence, for example by referring to specific parts of the source material. Concise and precise answers with a clear argument and structure are preferred over long, meandering collections of sentences.

Questions:

1. **Question 1:** Consider the scenario depicted in the NTSB report.
* a. Identify environmental and machine domains in the scenario.
* b. Specify the system-level safety requirement that was violated during the accident.
* c. Specify a list of environmental assumptions and software specifications that were needed to establish the system-level requirement.
* d. Which of the assumptions and/or specifications in 1.c were violated during the accident? 

2. **Question 2:** 
* a. Construct a fault tree to analyze the Uber accident from the NTSB report and identify potential root causes. Assume that the self-driving vehicle in the accident had the same software architecture as the one in Apollo 3.5.
* b. Identify all minimal cut sets in your fault tree.
(For this question, you may use any tool of your choice to construct the fault tree. A scan of a hand-drawn diagram is also acceptable, as long as it is clearly legible. There are also several free FTA tools you may wish to use; e.g., OpenFTA (http://www.openfta.com) and Open Reliability Editor (https://github.com/troeger/fuzzed)).

3. **Question 3:** Based on your analysis in Question 2, what changes to the system design or operating procedures would you recommend to reduce the risk of similar types of failures?

4. **Question 4:** FTA is a powerful tool for identifying and understanding failures, but can also produce misleading results if used poorly. What are some limitations of FTA? List at least two, and discuss them in the context of self-driving vehicle safety.

Submit your answers as a single PDF document to Canvas by [see Canvas]. Make sure your document is clearly structured, such that it is recognizable which answer belongs to which question.

## Grading

The assignment is worth 100 points. For full credit, we expect:
* Q1. Identification of relevant system requirements, assumptions, and specifications, including a clear distinction between environmental and machine domains (20 pt)
* Q2. Construction of a syntactically valid fault tree that adequately captures the scenario depicted in NSTB report (40 pt)
* Q3. Discussion of potential mitigations to the failure (15 pt)
* Q4. Discussion of the limitations of FTA (15 pt)
* A clearly structured, well written document (10 pt)
