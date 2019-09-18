# Group Assignment 2: AI Tradeoffs

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

While benefits and drawbacks of different AI/ML techniques can be described conceptually and are often well understood by experts, in this assignment you will actually *measure* the differences on various qualities of interest and practice communicating results to a nonexpert audience. You will compare at least two techniques and present your results to the class.

Learning goals:
* Understand multiple AI/ML techniques and their tradeoffs
* Measure quality attributes of interest
* Communicate tradeoffs to a nonexpert audience

## Tasks

Using the scenario and dataset from Assignment G1 (possibly enhanced by other data you might want to collect), you are planning to do additional prediction tasks.
As a first step, you want to predict the popularity of movies (i.e., how many people are going to watch a movie per day) so that you can plan royalty payments and future movie acquisitions. You also want to show this information to users, e.g., to indicate which movies are *hot* right now.


### A: Technique comparison

Pick *two* different AI/ML techniques for this assignment from the Doodle poll linked in Canvas. Note that you cannot pick techniques already claimed by other teams.

You will apply both techniques to predict movie popularity (**primary scenario**) and compare them across multiple qualities. That is, you will actually implement the prediction mechanisms with both techniques. 

Assume you want to deploy the technique in production, discuss and justify which technique you would use and why. Consider real-world production concerns if you would use this technique actually for making business decisions, including providing the infrastructure to compute predictions with MANY users/requests, update models, debugging, pursuing business goals, and so forth. Typically there are tradeoffs, where one technique does not fully dominate the other on all qualities of interest; in this case, explain how you made the tradeoff decision arriving at your recommendation. Your analysis and recommendation should be based on the specific scenario for a production system for which you anticipate more users in the future.

Afterward find a task (**alternative scenario**) for which you would recommend the other technique. Stay within the same movie streaming scenario, but you may collect different data if needed. Again, measure the relevant qualities and make an argument why this technique is more suitable when used for this alternative scenario in a production environment.


You again have full technical freedom in selecting programming languages, frameworks, and tools as you prefer. 


### B: Presenting results

Assume you want to argue in a team meeting for which technique to deploy in the next version of the system.
The audience consists of (a) software engineers with only superficial background in AI, (b) data analyst without experience in building production systems, and (c) managers with basic technical understanding. Assume the decision was controversial within the team and you present results to make a specific data-supported recommendation; expect critical questions from the faction that sees their preferred solution not being recommended.

Prepare a 10 minute presentation, in which you argue which technique to use and why. This will likely involve a brief explanation of how the techniques work as well as a discussion of measured or estimated results and their importance. Be prepared to answer the team's questions afterward.

Make sure your presentation is understandable to the described broad audience.
Note that you will likely not want to present all your results, but want to focus on the important insights and measures.


## Deliverables

You will present the presentation in class and afterward upload the presentation file and a report to Canvas.
Note that the in-class presentation is during class the day of the deadline.

Logistics: We expect that you present on your own laptop during class and provide us with a PDF version of your slides afterward. All team members should have an active role during the presentation. For Canvas, deliverables consist of a presentation (single PDF) and report (single PDF file, links to supporting artifacts), combined into a zip file.  For supplementary artifacts, we prefer that you upload them to your team's GitHub repository or your CMU box account. In either case, make clear from your report where to find any artifacts that you refer to.

The report should include the name of all students who contributed to the assignment and answer the following questions in clearly labeled sections of the document:

* Techniques (brief): Name the two AI/ML techniques considered and provide a link to your implementation and the learning libraries uses
* Problem (max .5 pages): Problem and dataset analyzed. If it is the same as assignment G1, a single line stating that is sufficient.
* Measurement (max 3 pages): A list of all measures considered, a description of how the measurement was performed, and the measurement results for both techniques. The description should be detailed enough that an experienced developer could reproduce them. Not all qualities are easily measurable -- discuss limitations where needed and provide a best effort measurement.
* Recommendation (max 1 page): A discussion and justification why one technique should be preferred over the other, grounded in the measurements and the movie streaming scenario. If there are tradeoffs, explain how you arrived at your recommendation. You may make additional assumptions (e.g., financial resources of the company) as long as you clearly document them.
* Alternative scenario (max 2 pages): Describe a different problem and dataset for which you recommend the other technique. Provide measurement results for this scenario as well (explaining differences in measurement if needed). Justify why the technique should be preferred.
* Discussion (max .5 page): Reflect on your work and discuss limitations of your measurement strategy, if any. In case you had more time or would start over, what would you change?


## Grading

The focus of this assignment is on measurement, tradeoff analysis, and presenting results. We expect a good description of how qualities are measured, including an honest reflection on limitations. If there are tradeoffs, we expect a convincing justification rooted in the realism of the scenario. We expect a presentation that can convince an audience with diverse backgrounds. We do not penalize any opinion or decision as long as there is a reasonable argument behind it. We assume that you apply the AI/ML techniques in a reasonable way, but we will not grade for accuracy or technical sophistication in how the techniques are used.

We will use approximately the following rubric for a total of 100 points:
 - [ ] 25 points: Description of measurements and measurement results of primary scenario
 - [ ] 10 points: Description of measurements and measurement results of alternative scenario
 - [ ] 15 points: Justified recommendation and tradeoff analysis of primary scenario
 - [ ] 10 points: Justified recommendation and tradeoff analysis of alternative scenario
 - [ ] 10 points: Suitable selection of alternative scenario
 - [ ] 20 points: Convincing and accessible presentation
 - [ ] 10 points: Report, presentation, and code quality (structure, readability, documentation)

Unless exceptional situations arise that require a discussion with the course staff, all team members who contribute to the solution will receive the same grade. Please try to first solve teamwork issues within the team and contact the course staff for advice and help if the situation does not improve.
