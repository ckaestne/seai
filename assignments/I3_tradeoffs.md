# Individual Assignment 3: AI Tradeoffs

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

While benefits and drawbacks of different AI/ML techniques can be described conceptually and are often well understood by experts, in this assignment you will actually *measure* the differences on various qualities of interest and practice communicating results to a nonexpert audience. You will compare at least three techniques and present your results in a “memo to your entire team”.

Learning goals:
* Understand multiple AI/ML techniques and their tradeoffs
* Define measures for quality attributes of interest and conduct measurement
* Communicate tradeoffs to a nonexpert audience

## Scenario

For this assignment, we will reuse the dataset and tasks from Assignment I2 (predicting the popularity of movies on a streaming service platform).

You are considering to build a dashboard for the procurement and contracting team that can help them make decisions about which movies they should license for the platform and how much money they might be willing to pay. You also envision that the system might be useful to understand what is popular on the platform and why and similar planning tasks involved in planning a portfolio of movies to offer.

While you have already built a model in the previous assignment, you are now exploring requirements for actually building a platform and are trying to get a better understanding which modeling technique might be appropriate for a production setting.

Before you build the dashboard, you want to involve the entire team in a discussion. To prepare for that discussion, you want to explore different techniques and write a memo that you can circulate as a basis for the discussion. Your team for this project consists of data scientists, software engineers, a project manager, and a few representatives from the procurement and contracting team. You suspect that management might also be interested in the memo.

## Task 1: Identify relevant qualities and measures

Discuss what qualities are important for a model underlying the planned dashboard. Consider real-world production concerns if you would use this technique actually for making business decisions, including providing the infrastructure to compute predictions, update models, debugging, pursuing business goals, and so forth.

Consider relevance of at least accuracy, training cost, amount of data needed, amount of features available, effort for data cleaning and feature engineering, inference cost, cost of updating the model with new data, model size, robustness, interpretability, **TODO**. You may not consider all qualities equally relevant in this scenario.

For each relevant quality (at least 5), define a measure and operationalize it. Typically you want to chose operationalizations to measure the qualities automatically, but for some qualities, operationalization may involve human judgement or human-subject experiments. Many metrics and operationalizations will likely be obvious and simple, some may not be. In either case, the description should be precise enough that others can independently measure these qualities on other modeling techniques without knowing your exact implementation. 

## Task 2: Compare modeling techniques

Select and compare *three* different AI/ML techniques to predict the popularity of a movie. At least one technique must be based on *neural networks*. You may reuse your data and implementation from assignment I2. You may use any frameworks or implementations you like, including cloud services.

## Task 3: Summarize Findings in Memo to the Team

Make a recommendation for which learning technique to use, summarizing your considerations and results, in a memo targeted at a team with members from different backgrounds and different preferences. Expect that the decision might be controversial, so be clear in your arguments. Avoid jargon and communicate assuming an audience with only limited data science or software engineering background. Typically there are tradeoffs, where one technique does not fully dominate the other on all qualities of interest; in this case, explain how you made the tradeoff decision arriving at your recommendation. Your analysis and recommendation should be based on the specific scenario.


## Deliverables

Submit a report describing the activities and considerations and including the memo as described below as PDF to Gradescope. In addition make implementations and models available to the course staff as in assignment I2 (preferably through  Github, but also box.com or other services work).

Your report should cover the following points, each in a clear subsection, where each subsection ideally starts on a new page:

* Techniques (brief): Name the three AI/ML techniques evaluated. For each technique name the learning library or tool used and provide a link to your code that is learning the model and a link to the learned model.
* Relevant qualities (max 1 page): List the qualities considered and each indicate whether you consider the quality as relevant for the scenario and why. This should include at least the qualities listed under Task 1 above.
* Measures and operationalization (max 2 pages): For at least 5 relevant qualities, each provide a concrete metric and describe how to operationalize it. Provide pointers to your implementation where you collect the measure (if applicable).
* Results: Report your measurement results for all relevant qualities for all three learning techniques (table or text).
* The memo (2–6 pages): Include the memo to the team. The memo should be self-contained without the other sections of the report and suitable for the target audience. The memo may repeat information from the other sections of the report. 


## Grading

The focus of this assignment is on reasoning about qualities in a specific scenario, measurement (defining and operationalizating measures), and communicating results. We assume that you apply the AI/ML techniques in a reasonable way, but we will not grade for accuracy or technical sophistication in how the techniques are used. We do not penalize any opinion or decision as long as there is a reasonable argument behind it. 

We will use approximately the following rubric for a total of 100 points:
 - [ ] 20 points: Code to learn a model to predict movie popularity with three different learning techniques, one of which needs to be based on neural networks (including 5 points for code quality). Links to learned models are provided. 
 - [ ] 10 points: Convincing justification for which qualities are considered relevant; the justification must be specific for the given scenario. All qualities listed under Task 1 are discussed.
 - [ ] 20 points: Description of metrics and operationalization for at least 5 relevant qualities; metrics are clearly defined and the descriptions are sufficient to independently measure these qualities. Pointers to implementation provided.
 - [ ] 10 points: Measurement results reported for at least 5 relevant qualities for each of the three learning techniques.
 - [ ] 40 points: A well written memo arguing convincingly for which technique to adopt that is suitable for the target audience (20 points for the technical content and arguments and 20 points for clarity and suitability for target audience). The memo should clearly recommend a single AI/ML technique for the scenario, make justifications based on measurements or other considerations, should make a judgement call when tradeoffs exist. The memo’s analysis must fit the scenario.

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class, under the following condition: *You may not work with anybody who you know well or who was on your team in a previous course.* To facilitate the search for team members, we post a link to a shared Google spreadsheet on Canvas.

If you work together as a team, you can either submit a joint solution or separate solutions on Gradescope. If you submit a joint solution, both team members will receive the same grade. If you submit separate solutions, those solutions may share text or code, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.