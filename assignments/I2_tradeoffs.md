# Individual Assignment 2: ML Tradeoffs

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

While benefits and drawbacks of different ML techniques can be described conceptually and are often well understood by experts, in this assignment you will actually *measure* the differences on various qualities of interest and practice communicating results to a nonexpert audience. You will compare at least three techniques and present your results in a “memo to your entire team”.

Learning goals:
* Understand multiple ML techniques and their tradeoffs
* Define measures for quality attributes of interest and conduct measurement
* Communicate tradeoffs to a nonexpert audience

## Scenario

For this assignment, consider you are part of a Google Android team that reviews apps in the Google Play app store to detect malicious apps, e.g., apps that steal private information, install cryptominers or bots, or cause financial charges by sending messages to expensive premium numbers. If you are interested, this [paper](https://www.csc2.ncsu.edu/faculty/xjiang4/pubs/OAKLAND12.pdf) discusses malicious Android apps.

With over 3 million apps in the app store, nearly 4000 apps added every day, and about 70000 apps updated every day, it is infeasible to review all apps manually. Your team explores options of how to automate some of the reviews or focus attention of reviews to possibly problematic apps. You envision a system that detects apps that may be malicious automatically and flags them for review. Ideally, the system is useful for manual security reviewers and will continuously learn as new attacks are discovered.

You are currently in the stage of exploring automatic detection with machine learning techniques, but hoping to put something into production soon. You have collected a dataset of about 5000 previously detected malicious apps to train on and have some good idea about what features to use. The key challenge right now is to identify *relevant qualities* for the model to be used in the production system and to compare how different *machine learning techniques* (e.g., decision trees, SVM, deep learning) compare. 

Before you build and deploy an actual production system, you want to involve the entire team in a discussion. To prepare for that discussion, you want to explore different techniques and write a memo that you can circulate as a basis for the discussion. Your team for this project consists of data scientists, software engineers, two security experts, a project manager, and several employees that currently do manual reviews. Most of them do not have a deep technical understanding of machine learning or the technical infrastructure. You suspect that management might also be interested in the memo.

### Provided Data and Model

For this assignment, we use the [Drebin dataset](https://www.sec.cs.tu-bs.de/~danarp/drebin/) (credentials on Canvas) to stand in for a subset of the data the Google team may have available. The dataset contains about 5000 malicious apps and data from about 130000 benign apps that can be used to learn a classifier. The providers of the dataset have extracted various features from the apps themselves, which can be used for this assignment. The features correspond to technical decisions in the apps’ implementations (e.g., APIs used, intents used, permissions used); details are described in the corresponding [technical paper](https://www.sec.cs.tu-bs.de/pubs/2014-ndss.pdf), but are not important for this assignment. We provide a [notebook](https://github.com/cmu-seai/ml-malware-classifier/blob/master/malware_analysis.ipynb) with a basic implementation that loads a subset of the data and learns a classifier; you will find other similar notebooks online. You may reuse any existing code in those notebooks or develop your own for the basis of the assignment. The provided notebook includes the basics and should be easy to modify to change the learner, the number of rows, or the features used (a preprocessed file to work with the full dataset can also be found on Canvas). Note that the focus of the assignment is not on data cleaning, feature engineering, or model training, but on measuring the various qualities of different models.

We recommend that you use the GitHub classroom link on Canvas to create a private Github repository based on our starter code.

## Task 1: Identify relevant qualities and measures

Discuss what qualities are important for a model underlying the detection tool. Consider real-world production concerns if you would use this technique actually for helping with security in Android, including providing the infrastructure to compute predictions, update models, debugging, pursuing business goals, and interacting with app developers and app users, and so forth.

Consider relevance of at least (1) accuracy, (2) training cost, (3) amount of data needed, (4) scalability with the number of features considered, (5) effort for data cleaning and feature engineering, (6) inference cost, (7) cost of updating the model with new data, (8) model size, (9) robustness, and (10) interpretability. You may consider other qualities. You may decide that not all qualities are equally relevant in this scenario. You may group them as relevant and not relevant or rank them.

For at least 4 relevant qualities, define a measure and operationalize it. Typically you want to chose operationalizations to measure the qualities automatically, but for some qualities, operationalization may involve human judgement or human-subject experiments; measures may be on any kind of scales, including nominal scales. Many metrics and operationalizations will likely be obvious and simple and follow common standards, some may not be. In either case, the description should be precise enough that others can *independently* measure these qualities on other modeling techniques without seeing your code. 

## Task 2: Compare modeling techniques

Select and compare *three* different ML techniques to predict whether an app is malicious. We suggest to use some form of *neural networks* as one of the techniques. 

We provide data and a notebook with an initial Naive Bayes implementation, which you may reuse and adopt. You can use the provided implementation as one of your three techniques. We do not expect you to invest additional effort in data cleaning or feature engineering, but you may. You may use any frameworks or implementations you like, including cloud services.

## Task 3: Summarize Findings in Memo to the Team

*Make a recommendation* for which learning technique to use, summarizing your considerations and results, in a memo targeted at a team with members from different backgrounds and different preferences. Expect that the decision might be controversial, so be clear in your arguments. Avoid jargon and communicate assuming an audience with only limited data science or software engineering background. Typically there are tradeoffs, where one technique does not fully dominate the other on all qualities of interest; in this case, explain how you made the tradeoff decision arriving at your recommendation. Your analysis and recommendation should be based on the specific scenario.


## Deliverables

Submit a report describing the activities and considerations and including the memo as described below as PDF to Gradescope. In addition make implementations and models available to the course staff (preferably through GitHub in a private repository created with the GitHub Classroom link on Canvas, but also box.com, Google Colab, and other services work).

Your report should cover the following points, each in a clear subsection (ideally start each subsection on a new page and map the pages in Gradescope):

* Techniques (brief): Name the three AI/ML techniques evaluated. For each technique name the learning library or tool used and provide a separate link to the model code for each technique.
* Relevant qualities (max 2 pages): List the qualities considered and each indicate whether you consider the quality as relevant for the scenario and why/why not. This should include at least the qualities listed under Task 1 above.
* Measures and operationalization (max 2 pages): For 4 relevant qualities, each provide a concrete metric and describe how to operationalize it. The description should be accurate enough that one could independently reimplement and repeat the measurement. Provide pointers to where in your implementation you collect the measure (if applicable).
* Results: Report your measurement results for all relevant qualities for all three learning techniques (table or text). For example, you may provide a table with 3 columns for each technique and 4 rows for each quality, where the cells contain the measurement results. No further explanation or discussion needed.
* The memo (1–3 pages): Include the memo to the team. The memo should make a recommendation about which technique to adopt and justify it. The memo should be self-contained and not refer to other sections of the report. It should be suitable for the target audience, forgoing jargon. The memo may repeat information from the other sections of the report. 


## Grading

The focus of this assignment is on reasoning about qualities in a specific scenario, measurement (defining and operationalizating measures), and communicating results. We assume that you apply the ML techniques in a reasonable way, but we will not grade for accuracy or technical sophistication in how the techniques are used. We do not penalize any opinion or decision as long as there is a reasonable argument behind it. 

We will use approximately the following rubric for a total of 100 points:
 - [ ] 10 points: Code provided to learn a model to predict malicious apps with three different learning techniques, one of which needs to be based on neural networks. Separate links to the code learning the models are provided.
 - [ ] 10 points: The report includes justification for which qualities are considered relevant. The justifications relate to the specific scenario. *All* qualities listed under Task 1 are discussed.
 - [ ] 10 points each (up to 40p) for describing and metrics and operationalization a relevant quality in the report. The metric is clearly defined and the description is sufficient to independently measure the quality. A pointer to implementation of each measurement is provided.
 - [ ] 20 points: Measurement results (concrete numbers) are reported for at least 4 relevant qualities for each of the three learning techniques. The results correspond to the learned models and the metrics described in the report.
 - [ ] 10 points:  The memo clearly recommends a single ML technique for the scenario. It justifies why this technique is preferably based on measurements or other considerations. The memo explains the recommendation when tradeoffs exist. The memo’s analysis is consistent with the scenario and the qualities identified as relevant.
 - [ ] 10 points: The memo is written clearly and avoids jargon. It is self-contained. It is suitable for target audience. 

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class. We recommend a pairing on Canvas. You may *not* work together with a student with whom you have worked together on a previous individual assignment.

If you work together as a team, you can either submit a joint solution or separate solutions on Gradescope. If you submit a joint solution, both team members will receive the same grade. If you submit separate solutions, those solutions may share text or code, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.

You will receive 3 bonus points if your submission includes a screenshot from a Zoom session with your potential partner. You can receive these bonus points for just discussing the option of working together with your partner, even if you decide to work alone.
