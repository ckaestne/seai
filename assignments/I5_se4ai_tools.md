# Individual Assignment 5: Software Engineering Tools for AI-Enabled Systems

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will have a chance to explore modern tools that are useful for building AI-enabled systems. You will try them in the context of the movie streaming scenario and write a blog post about them.

Learning goals:
* Explore the ecosystem of software engineering tools for AI-enabled systems
* Explain to other stakeholders the purpose of a tool

## Tasks

This assignment is very open-ended and you can customize it to your interests.

Pick an aspect of building AI-enabled systems that you find interesting (e.g., testing, deployment, operations) and look for a tool that supports this task. You must pick a tool **that you are not yet familiar with**. Each student/team **must pick a different tool**; claim the tool of your choice in the Google Spreadsheet linked from Canvas. Try the tool in the context of the movie streaming example and write a blog post about the tool and your experience. Within 3 days after the deadline, read at least two other blog posts from other students and comment on them.

## Guidance and hints

**Picking a tool:** Claim the tool of your choice early so that you do not waste effort exploring a tool that is then claimed by somebody else. First come first serve. Please only claim one tool at any time, but you may change what tool you claim if your first choice does not turn out to be interesting or usable.

You may pick open source tools as well as commercial tools, as long as you can give the course staff access to your work. You may use your AWS credit for this assignment or sign up for trial versions if you like.

Pick a tool that you have not used before. Maybe there are tools that you have read about and are curious to explore.

The tool does not need to be directly related to AI or ML, but should be plausibly fit into a production scenario where it supports or interacts with AI components in a larger system. For example, a distributed logging system may not be designed specifically for ML applications but would be a useful foundation for collecting telemetry. Avoid using pure data science tools (pure data exploration or ML learning frameworks). If in doubt ask the instructors whether a tool is in scope. Here are a couple of examples you could consider, but you can find [many](https://www.analyticsvidhya.com/blog/2019/07/21-open-source-machine-learning-tools/) [lists](https://github.com/EthicalML/awesome-production-machine-learning) with a little searching:

* MLOps, monitoring, and deployment: e.g. Kubernetis, MLflow, Kubeflow, Apache Flume, MCenter
* Pipeline automation and best practices: e.g., Kedro, Airflow
* Data and model versioning: e.g., dvc, ModelDB
* Data programming, data cleaning: e.g. Snorkel, Holoclean
* Big data solutions: e.g., Sparks, Hadoop
* Learning at scale/in the cloud: e.g., Amazon SageMaker, TFX

**Trying the tool:** For the “try the tool” part, we expect at a minimum that you install/set up the tool and use it in the context of the movie streaming scenario (ideally for movie recommendations as in the group project or predicting movie popularity as in I2 and I3, but also other possible tasks in this scenario are okay). Feed it with some sample data from the scenario. For example, you could set up a distributed logging system and feed it with telemetry data from the team project. You may, but are not required to, fully integrate the tool with your team project or previous homework solutions. You may use your team’s virtual machine if you coordinate with the rest of your team or use your AWS credits if suitable.

**The blog post:** Write the blog post for a general audience of readers interested in production machine learning (e.g., data scientists interesting in building production systems, software engineers interested in machine learning, self-taught enthusiasts interested in the topic). As in the memo in assignment I3, avoid jargon and avoid assuming too much background knowledge. Other popular blogs might provide some ideas, such as https://towardsdatascience.com/ or many company blogs.

The blog post should cover at least (1) the problem that the tool addresses, (2) a discussion how it helps with examples from the movie streaming scenario, and (3) a discussion of the strength and limitations of the tool.

We recommend that you post the blog posts publicly in a location of your choice (e.g., medium.com). If you have a personal blog, feel free to post it there. If you prefer to not post the blog post publicly, post it in the Discussion section Canvas. If you post it in a public place that does not allow comments, post a link to it on Canvas, so that other students can comment there.

**The comments:** After the deadline read at least two other blog posts (you can find their links in the spreadsheet) and post comments on them. Comments can share additional experience, ask questions, or indicate insights you gained from reading the blog post. The comments are due 3 days after the assignment’s main deadline.


## Deliverable

Post the blog post, update the Google Spreadsheet with links, and submit a short PDF to Gradescope.

**Post the blog post** publicly or in the discussion section on Canvas (on canvas use the prefix “Blog: ” for the title of the posting).

**Update the Google Spreadsheet** linked from Canvas with the tool name and a link to your blog post by the assignment’s deadline. Within three days after the deadline add two more links to the comments you made on other blog posts to the Spreadsheet.

The **PDF** on gradescope (likely just a single page) should cover:

1. **Blog post link:** Provide a link to the blog post
2. **Data links:** Provide a brief (max .5 page) description of for what and how you tried to use the tool in the context of the movie streaming scenario. Provide links (e.g., to GitHub) of where to find your configuration or use of the tool as evidence of you trying the tool with data from the movie streaming scenario. You may include screenshots, outputs, or logs if that is helpful. Provide credentials for external services, if needed. 
3. **Appendix (optional):** You may share additional information that you prefer not to include in the blog post (e.g., for readability or because it is sensitive information) with the course staff in this appendix.


## Grading

The assignment is worth 100 points. For full credit, we expect:
* [ ] 10 points: The spreadsheet is filled out correctly and we can find your blog post and comments without asking. :-)
* [ ] 50 points: A blog post that covers at least (1) the problem that the tool addresses, (2) a discussion how it helps with examples from the movie streaming scenario, and (3) a discussion of the strength and limitations of the tool. The blog post is professionally written and suitable for a broad target audience of interested software engineers and data scientists. 
* [ ] 20 points: Evidence that the tool was tried on data from the movie streaming scenario.
* [ ] 20 points: Two comments on other blog posts that show an engagement with the content of the blog post (i.e., not just “looks good” or “interesting!”).
* [ ] (optional) 5 bonus points if the blog post is posted publicly.

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class, under the following condition: *You may not work with anybody who you know well or who was on your team in a previous course or other assignment in this course (including I3, I4, and the group project).* To facilitate the search for team members use the “team search” tab of the spreadsheet on Canvas.

If you work together as a team, you can either submit a joint solution or separate solutions on Gradescope. If you submit a joint solution, both team members will receive the same grade. If you submit separate solutions, those solutions may share text or code, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.