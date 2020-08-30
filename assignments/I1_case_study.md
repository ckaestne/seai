# Individual Assignment 1: Production ML Case Study

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

Building a system with an AI component requires more than building and tuning a model. Understanding challenges in a specific project may help deriving insights for other projects. In this assignment, you will analyze the report for on of two projects to identify software engineering concerns in building a production ML system.

Learning goals:
* Understand the scope of software engineering challenges when building an AI-enabled system
* Identify technical and nontechnical challenges 
* Identify and describe measures for project success

## Tasks and Questions

Pick one of the following two articles about developing and deploying a production system with a machine learning component:

* Sendak, M., et al. [Real-World Integration of a Sepsis Deep Learning Technology Into Routine Clinical Care: Implementation Study](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7391165/). *JMIR Medical Informatics* 8.7 (2020): e15182.
* Sculley, D., Matthew Eric Otey, Michael Pohl, Bridget Spitznagel, John Hainsworth, and Yunkai Zhou. [Detecting Adversarial Advertisements in the Wild](https://research.google/pubs/pub37195.pdf). In *Proceedings of the 17th ACM SIGKDD International Conference on Knowledge Discovery and Data Mining*, pp. 274-282. ACM, 2011.

The first article focuses on a recent medical system with a deep learning component deployed at a hospital, the second on detecting malicious ads at Google about a decade ago. Both describe the system and efforts and challenges in deploying the system in production.


Read one of the papers and if necessary familiarize yourself with terminology and additional context, using other web and research publications on the topic as needed.


Answer the questions below (<1 page per question). Wherever reasonable, provide evidence, for example by referring to specific parts of the source material. Your answers may contain opinions and speculations, but make sure that they are clearly recognizable as such and clearly separate opinions/speculations from facts. 

Concise and precise answers with a clear argument and structure are preferred over long, meandering collections of sentences.

Questions:

1. **Question 1:** What makes the problem (sepsis detection/detecting adversarial advertisement) hard? Specifically, why is a machine-learning solution used rather than a some well-specified rules implemented in traditional code?
2. **Question 2:** What qualities were important to the team in building the system, beyond prediction accuracy? Identify relevant qualities, each briefly explain why they are important for the project, and give a brief description of how the team has checked or could check whether those qualities are sufficiently achieved in the project (e.g., with specific way to measure the quality).
3. **Question 3:** What are *engineering* challenges, outside of the initial model development, that emerged when turning the initial idea into a production system and how were those addressed? Note, this question specifically does not ask about data-science difficulties in building the initial model (getting data, data cleaning, feature engineering, selecting a learning technique), but about challenges that occur when building a production system, e.g., around deployment, maintenance and evolution, human-user interactions, safety. Identify at least three engineering challenges for which the team had to make decisions. Justify why these were important challenges, what potential options the team had to address them, and summarize how the team actually addressed them.
4. **Question 4:** What lessons can be learned for future software projects with machine-learning components of similar scale or importance? Identify and briefly describe at least two *engineering* lessons that are worth sharing with other teams building AI-enabled systems, especially teams that are new to using ML techniques. Again, lessons should relate to the engineering, deployment, or operation of a production system, not the initial model development.

Submit your answers as a single PDF document to Gradescope by [see Canvas]. Make sure your document is clearly structured, such that it is recognizable which answer belongs to which question. Ideally, you answer each question on a separate page, which makes our lives easier for grading.


## Grading

The assignment is worth 100 points. We will assign credit as follows:
* 10p: The document is clearly structured, such that it is clear which text belongs to which question.
* 20p: A discussion of the problem's difficulty that explains (a) why the problem is hard and (b) why machine learning is a suitable solution.
* 20p: Identification of at least 3 important qualities for the system (other than accuracy measures of the used model) with a justification explaining why the quality is important. All qualities must be grounded in the report of the case study.
* 10p: For each important quality, a description of how the team has measured (if described in the case study) or could measure (if not described in the report) whether the quality is sufficiently achieved.
* 20p: Identification of at least 3 engineering challenges in engineering, deploying, and operating the system, that the team faced in the case study. The challenges must be grounded in reporting of the case study. All challenges must relate to engineering aspects, not data-science aspects in building the original model.
* 10p: For each engineering challenge, a discussion of (a) importance, (b) alternative considered, and (c) solution adopted. The description must be grounded in the case study.
* 10p: Identification and description of two engineering lessons learned in the project. The lessons generalize from the case study and make specific recommendations for other projects. The lessons must relate to engineering concerns of the production system, not data-science concerns in the initial model development.

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class. We suggest teams for the assignment on Canvas.

If you work together as a team, you can either submit a joint solution or separate solutions on Gradescope. If you submit a joint solution, both team members must have contributed to the solution and both team members will receive the same grade. If you submit separate solutions, those solutions may share text and you may discuss all aspects of the assignment, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.

You will receive 3 bonus points if your submission includes a screenshot from a Zoom session with your potential team. You can receive these bonus points for just discussing the option of working together with your partner, even if you decide to work alone.

