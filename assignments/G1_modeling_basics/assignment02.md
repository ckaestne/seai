# Group Assignment 1: Modeling Basics

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

This assignment is intended as a warmup to get to know your team and get familiar with the basics of machine learning tools. In this assignment, you will build and evaluate a model that can be used to create recommendations for a site like Netflix or Youtube. In this assignment, you will take the data analysist's perspective for building a model (feature engineering, evaluation on static data), whereas we will care about software engineering concerns (deployment, testing, evaluation in production, scaling, updating) in later assignments.

Learning goals:
* Collect data from multiple sources and engineer features for learning
* Apply state of the art machine learning tools
* Evaluate a model on a given dataset
* Practice teamwork and reflect on the process

## Tasks

Consider you are in the early days of video streaming and you want to foster sales by keeping your users engaged and coming back. A key feature you want to deploy is a new recommendation engine that suggests movies to users. To develop that feature you will need one or multiple models.

In a later assignment you need to provide a function `recommend: UID -> List[MovieID]` that returns for a given user a ranked list of recommended movies to show to the user, but for now you may also focus on other forms of predictive models that may be useful for a recommendation system.

**Provided data:** We provide an event stream of a streaming service site that records server logs, which include information about which user watched which video and ratings about those movies. In addition, we provide read-only access to an API to query information about users and movies. You are welcome to gather additional external information if it is useful for the task, for example, ids for [IMDB](https://www.imdb.com/) and [TMDB](https://www.themoviedb.org/) are provided.

The information about the provided Kafka stream and the API can be found on Canvas.


**Modeling:** Learn a model to make recommendations. You have full freedom in deciding what technology to use, how to clean data, how to extract features, which feature to extract, what kind of model to learn with what kind of tools. You may use the provided virtual machine, may use your own infrastructure, or may use external tools and services, as long as you document your process and make the essential artifacts available to the course staff.

**Evaluation:** Evaluate the quality of your model with a suitable evaluation strategy. This likely involves separating some of the provided data as evaluation data and evaluating model accuracy in some form.

**Demonstrate model improvement:** You will likely need to iterate over your model repeatedly as you test different features or different learning techniques. Retain at least one alternative model and demonstrate how changes (e.g., different learning technique or additional feature) have lead to better model performance.

You have considerable freedom in how you approach this task. You are free to chose programming language and libraries as you wish. 


## Deliverables

Deliverables consist of a report (single PDF file) and supporting artifacts. Upload the report to canvas. For supplementary artifacts, there are multiple options: Preferably upload artifacts to your team's GitHub repository (see signup link on Canvas), upload large files to your CMU box account, or zip the files together with report for your Canvas upload. In either case, make clear from your report where to find any artifacts that you refer to.

The report should include the name of all students who contributed to the assignment and answer the following questions in clearly labeled sections of the document:

* Overall process (max 1 page): Describe your team's overall approach to developing the model. Describe how your team collocated, how you made decisions, and how you approached the problem.
* Data and cleaning (max .5 page): Describe the data you used for learning (provided and external), how you gathered it, and describe how you cleaned the data.
* Features: Provide a full list of all features used in the model and a short description of how they were extracted. Provide a pointer to the implementation of the feature extraction process, as appropriate.
* Learning (max 1 page): Describe the learning techniques used and provide a pointer to the implementation. Provide a brief justification why you decided to use this specific technique and implementation. Provide a pointer to the final model learned.
* Evaluation (max 1 page): Describe how you evaluated the model. This should include at least a description of the evaluation metric and the evaluation data. Briefly justify both the used metric and how you separated evaluation data.
* Evaluation results: Provide the evaluation results for the final model. In addition, demonstrate how the evaluation helped in designing the model by including results for one significant decision during the modeling process (e.g., comparing two learning techniques or comparing results with and without a certain feature). Provide a pointer to the corresponding artifacts.
* Team meeting notes: Provide pointers to notes taken at team meetings. The notes should describe how work was divided. 
* Process reflection (max .5 page): Think back about your team's process and reflect about what worked well and what did not. Focus especially on problems regarding teamwork and process and discuss what you would do different if you would do the assignment again.

On page limits: Figures and tables do not count toward the page limit. All page limits are soft limits that should usually be obeyed but can be exceeded if there are specific reasons (e.g., unusual decisions that need more space for explanations).

## Grading

We expect a reasonable job for data cleaning, feature extraction, learning, and model evaluation that demonstrates a basic understanding of all involved tasks. We expect readable code for all involved steps (with documentation where necessary). We do NOT have any expectations with regard to model accuracy of the resulting model; we may give up to 5 bonus points for very accurate models.

We will grade the presence of team meeting notes, not their content.
We will not apply penalties for problems in team work as long as the team recognizes the issue in the reflection and discusses strategies to mitigate issues in the future. We do not penalize any opinion or decision as long as there is a reasonable argument behind it.

We will use approximately the following rubric for a total of 100 points:
 - [ ] 10 points: Data gathering and data cleaning performed and described 
 - [ ] 15 points: Feature extraction performed and described
 - [ ] 15 points: Learning performed and described, learning technique reasonably justified
 - [ ] 15 points: Evaluation of final model performed and described. The evaluation metric is clear and suitably chosen. The use of evaluation data is appropriate.
 - [ ] 10 points: Evaluation of a pair of models shows the benefit of a specific design decision.
 - [ ] 15 points: Report and code quality (structure, readability, documentation)
 - [ ] 5 points: Team meeting notes included
 - [ ] 15 points: Meaningful team reflection, grounded in your experiences from this assignment, beyond superficial statements and mere truisms that ties specifically to this assignment.
 - [ ] up to 5 bonus points for very good models

Unless exceptional situations arise that require a discussion with the course staff, all team members who contribute to the solution will receive the same grade. Please try to first solve teamwork issues within the team and contact the course staff for advice and help if the situation does not improve.

## Advice on Teamwork

A key goal of this assignment is for teams to get to know each other and find efficient ways of collaboration. Please establish a way of communication and collaboration that works for your team -- for example, a Slack channel and clear notes from meetings that include agreed assignments are very useful.
In addition, this assignment is designed to force each team to agree on a technology framework and become familiar with that framework -- you can continue to use that technology stack in future team assignments.

We expect that team members will have very different backgrounds and different amounts of experience with machine learning -- this is intentional. Use this assignment to identify strength and weaknesses, fill missing gaps in background knowledge, and teach each other about tools and practices that are effective for this task.


