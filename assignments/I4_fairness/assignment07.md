# Individual Assignment 4: Fairness

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will get practice on how to systematically identify fairness issues in AI-enable systems. In particular, you will learn to (1) think about potential harms that can be caused by an unfair AI system, (2) identify potential sources of bias, and (3) use data analysis to evaluate and measure for a case study system involving credit card scoring.

Learning goals:
* Understand the potential negative impact of a biased AI-driven system on society.
* Learn to systematically identify potential bias in an ML dataset.
* Understand the limitations of existing definitions of fairness.

## Tasks and Questions

For this assignment, you will work with a dataset from a credit card scoring system used by Schufa, a German private credit bureau. Schufa scores are similar to FICO scores in the US; most German citizens have a Schufa score, and these scores are used to inform financial decisions in various contexts, from banking and insurance to real estate rentals.

Despite its significant impact on the lives of German citizens, the algorithm used by the Schufa scoring system has been kept opaque from the public (not surprisingly, since Schufa is a private company). This lack of transparency also means that it is difficult to determine whether the system may be (inadvertently) making unfair decisions against certain groups of people. In response to this concern, there have been attempts to unearth the inner workings of the system and identify potential bias (most notable one being the OpenSCHUFA project; https://openschufa.de/english).

Your job is to (1) think about the potential negative impact of unfair decisions made by credit card rating systems like Schufa (2) and identify potential bias in the Schufa system. 

A sample dataset from Schufa is available online for download (https://archive.ics.uci.edu/ml/datasets/Statlog+%28German+Credit+Data%29). It contains information about 1000 loan applications and includes 20 attributes that describe various characteristics of applicants, including their credit history, employment, martial status, gender, age, and job. In addition, each row in the dataset is labeled with a classification decision that states whether the application is considered "good" or "bad". More detailed information about the format of the dataset and attribute values can be found in the provided link.

Answer the questions below. Concise and precise answers with a clear argument and structure are preferred over long, meandering collections of sentences.

Questions:

**Question 1:** Recall the two types of harms that can be caused by AI (harms of allocation and harms of representation). For each of these two types, give a concrete example of harm that can occur due to an unfair decision by Schufa.

**Question 2:** Recall the five types of sources of bias discussed in class: Skewed samples, tainted examples, limited features, sample size disparity, and proxies. For each of them, give (1) a concrete example in the context of Schufa and (2) a brief explanation of how that bias might result in an unfair decision by Schufa.

**Question 3:** Analyze the given Schufa dataset to detect potential bias. In particular, use the notion of _group fairness_ discussed in class as the metric of fairness for this question. Note that there may be multiple protected groups (each characterized by one of the attributes in the dataset, such as age) against which Schufa makes unfair decisions. Your analysis must identify at least two such groups and compute disparity measures for them. You may use any programming language or library to perform the analysis.

Your response to this question should include (1) a brief description of how you performed the analysis (you do not need to submit your code, but include a snippet or pseudocode if you think it would be helpful) and (2) the set of protected groups along with the disparity measures for each one of them.

**Question 4:** Based on the bias that you found in Question 3, suggests at least one type of modification to the dataset that may help reduce the bias in Schufa.

**Question 5:** What are limitations of group fairness as a definition for fairness? Explain by giving an example in the context of Schufa.

Submit your answers as a single PDF document to Canvas by [see Canvas]. Make sure your document is clearly structured, such that it is recognizable which answer belongs to which question.

## Grading

The assignment is worth 100 points. For full credit, we expect:
* Q1. Discussion of potential harms on society (10 pt)
* Q2. Discussion of potential sources of bias (30 pt)
* Q3. Description of the dataset analysis and results (30 pt)
* Q4. Discussion of a modification to reduce bias (10 pt)
* Q5. Discussion of the limitations of group fairness (10 pt)
* A clearly structured, well written document (10 pt)
