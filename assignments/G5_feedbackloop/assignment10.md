# Group Assignment 5: System Monitoring

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will continue to run your prediction model but start thinking more explicitly about potential problems that may arise in your system from feedback loops and attacks.


Learning goals:
* Reason about feedback loops and adversarial attacks in machine-learning systems
* Design and implement a monitoring strategy to detect feedback loops and attacks
* Use the Lambda Architecture to implement a data analysis solution

## Tasks

Throughout this assignment, continue to run your recommendation infrastructure and update your models regularly. We will continue to assess availability of your recommendation service.

### Planning

**Feedback loops:** Think about potential feedback loops (postive or negative)
that may  occur in the system due to your recommendation algorithm. Are there
populations that may lead to positive or negative behavior due to your
recommendations? Think about what responsibility you might have as company and
as authors of the recommendation system. Plan how you would detect such a
feedback loop and what you can do to avoid negative consequences once detected.

**Adversarial attacks:** Think about how users or other stakeholders might try 
to attack your recommendation system. Again, think about how you would 
(a) make it harder to attack the system, 
(b) detect such attack and 
(c) what to do once detected.

Note, we have introduced mechanisms for specific feedback loops in our infrastructure and may try to simulate an attack on your recommendation system during the assignments duration. It is okay if you look for feedback loops or attacks that are not actually occuring for any teams: We do not require that you detect the specific feedback loop or attack that we encoded, but may provide bonus points if you do. 

### Monitoring and Detection

Build a system to detect problematic feedback loops and attacks in near real time (at least one of each). Implement the system using the lambda architecture, producing near real-time reports *for all three teams* in this class through a webserver. The reporting web page should contain some information on how to read the results.

For example, your web page could produce a dashboard with a graph that you expect to remain stable, but that would show an upward trend if a feedback loop seems to affect the system. Similarly, you could highlight problematic trends that might indicate an attack (using graphs or even simple warning messages).

Note, you can see the recommendations that all three teams make publicly in the Kafka stream. We divided the user population by teams, so different teams may influence their users independently.

**Technical guidance:**
Create a webserver on port 8080 of your virtual machine that shows a report for each of the three teams. 

Design your analysis following the lambda architecture to perform an accurate analysis in a nightly batch job and update results incrementally (potentially approximated) based on incoming data.
For the batch processing part, consider what data to store, when and for how long. You are welcome to explore batch computation systems like Hadoop, but for this assignment a single, nonparallelized and nondistributed analysis script is likely sufficient. 
For the stream computations, you likely want to subscribe to our provided Kafka stream; we recommend to break down the stream processing into multiple modular parts. If you want to manage events between parts of your stream processing solution, you can install your own Kafka server or (if the load remains moderade) create a new topic on our Kafka server with the prefix `team$TEAMNAME_`. 

For reporting, a simple web-server at reports the most recent results whenever a stats page is requested, e.g., based on `flask`, is likely sufficient. You likely want to plot results using a plotting library, either generate svg/png images or render plots in the browser with a Javascript library. Do not invest too much time on the aesthetics of your web page. Clear information is more important for this assignment. 

You may create a separate team repository for this assignment on [Github Classroom](https://classroom.github.com/g/1O5bU1Bw).



## Deliverables

We expect an available recommendation service that is running through the period of this assignment. We expect a running implementation of the monitoring and detection service for all three teams in your virtual machine and the documented code of that service (following the lambda architecture) in your team's GitHub repository. Finally, upload a report to Canvas that covers the following sections:

* **Analysis of Potential Feedback Loops** (2 pages max): Describe the process you used to analyze feedback loops and any potential (at least 2) feedback loops you identified. For each feedback loop, explain what might happen and what the positive or negative consequences are, and how it could be detected.
* **Analysis of Potential Attacks** (2 pages max): Describe the process you used to analyze potential attacks and any potential (at least 2) attacks you identified. For each potential attack, describe the attack scenario, how it could be detected, how it could be mitigated or made harder to exploit, and what could be done once detected.
* **Description of Monitoring and Detection Infrastructure** (2 page max): Describe the architecture of your monitoring and detection infrastructure and discuss how you could scale it as the system becomes more used.
Explain how your implementation achieves detection of feedback loops or adversarial attacks described in the previous sections. Clearly explain your detection mechanism in the report with clear mapping to source code. Document assumptions, if you make any. 
* **Screenshots of Reports:** Provide screenshots of your reports for all three teams. Include some explanation of how to read the reports if necessary.
* **Recommendation Service Reflection** (1 page max): Looking back at the entire semester in which you have designed, implemented, deployed, and monitored the recommendation service. What parts were the most challenging? Which aspects are still unstable and would require additional investment if you had to deploy the recommendation service at scale in production? How would you address these issues if you had more time and more resources?
* **Team reflection** (1 page max): Think back on your team's teamwork throughout this semester. What went well or less well in the team assignments? What were some of the main challenges you faced in teamwork?  What could have been done better in your future collaboration in other teams? We are looking for honest reflections that are open about potential issues; we grade only the quality of the reflection, not the quality of the teamwork described in the reflection.

As usual, all page limits are soft limits that can be broken if there is a specific reason. Screenshots and figures do not count toward the page limit.



## Grading


We will use approximately the following rubric for a total of 200 points:
 - [ ] 30 points: Appropriate discussion of at least 2 potential feedback loops, their consequences, and their possible detection.
 - [ ] 30 points: Appropriate discussion of at least 2 potential attacks and corresponding detection and mitigation strategies.
 - [ ] 15 points: Description of the monitoring and detection infrastructure
 - [ ] 35 points: Implementation of the monitoring service using the Lambda architecture, using both batch and stream processing
 - [ ] 20 points: Web service showing results for all 3 teams (screenshots + working service)
 - [ ] 15 points: High availability of the recommendation service throughout this assignment
 - [ ] 20 points: Meaningful recommendation-service reflection, grounded in your experiences throughout this semester, beyond superficial statements and mere truisms.
 - [ ] 20 points: Meaningful teamwork reflection, grounded in your experiences throughout this semester, beyond superficial statements and mere truisms.
 - [ ] 15 points: Report and code quality, including quality of your commit log

Unless exceptional situations arise that require a discussion with the course staff, all team members who contribute to the solution will receive the same grade. Please try to first solve teamwork issues within the team and contact the course staff for advice and help if the situation does not improve.
