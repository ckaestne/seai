# Group Assignment 4: Model Update Deployment and A/B Testing

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

Based on your learning and serving infrastructure for the movie recommendation service,
you now focus on allowing frequent model updates, easing deployments, and 
supporting experimentation.

Learning goals:
* Design a scalable and robust infrastructure for model inference
* Set up and use continuous integration
* Build a continuous delivery pipeline with canary releases and deploy model updates without downtime
* Design infrastructure for and A/B tests 


## Tasks

Keep your recommendation service running as much as possible throughout the entire period of the assignment.
Prefer poor recommendations over missing or very slow answers from your service.
We will look at the logs (public, in the Kafka stream) to assess downtime.

You may use [Github classroom](https://classroom.github.com/g/oxo4b3bS) to
create a private repository for this assignment.


### Continuous Integration for Pipeline Code

Set up a continuous integration infrastructure (with Jenkins in your virtual machine) that
builds and tests your entire pipeline on every commit to your Git repository.
Use a Jenkins plugin to plot *test coverage* over time.
(Note, unsecured Jenkins implementations are actively exploited in the wild, so please
take basic security precautions such as setting a password).

### Model Update and Canary Release Infrastructure

Design and build an infrastructure that you can use to incrementally deploy new versions of your 
recommendation service. New releases can be triggered by changes to your learning infrastructure or simply by
learning regularly from more recent data.

We recommend to proceed roughly in the following steps:
* Route incoming traffic through a point that can decide which of multiple servers to ask for a recommendation. Have flexible and easily changeable rules, which users are routed to which recommendation server.
* Run the router and the multiple servers each in their own container and demonstrate that you can manually switch over from one server to another without downtime.
* Create a process to regularly update your training data with recent data from the Kafka stream. Run this regularly with automation (e.g., as a cronjob every night).
* Use Jenkins to trigger the learning process for every commit to the learning or inference infrastructure and every time your learning dataset is updated (this is independent from the tests of your infrastructure code above). Automate measuring model quality and building of a new Docker container. Abort deployment when tests do not pass or model quality degrades substantially.
* Create a supervisor program that schedules and controls a new release (triggered by Jenkins): start the containers with the new server, decide where traffic is routed, observed the behavior of the new server, *automatically* roll back the release when problems are detected or eventually switch all traffic to the new release when no problems are detected.
* Monitor the process and send automated messages (emails) for successful and aborted releases.

To build such infrastructure, it is important to decide how quality is measured, both during the model learning phase and during the canary release.
In addition, it is important to decide how to detect releases that should not go into production (hint: you will most likely want to use a *t-test*
on some telemetry data).


Demonstrate the capabilities of your system by showing at least one successful release, at least one release correctly aborted due to failing tests in Jenkins, and at least one release correctly aborted during the canary release stage. To this end, you will need to create commits that specifically create broken or poor quality models. Demonstrate that you can update models in production without any downtime of your service.


### A/B Test Infrastructure

Design and build an infrastructure to conduct A/B tests and report the results of A/B tests.
You may want to coordinate this with the canary release infrastructure, there is likely
substantial opportunity for reuse.

With the infrastructure, you should be able to:
* Declare flags for experiments
* Decide which users will see each experiment
* Use these flags in the implementation to decide whether to activate experimental code for a given user (e.g., extra or different computations or use of a different model)
* Collect telemetry data to measure to observe the outcome of the experiment
* Create a report that summarizes the outcome of the experiment (and the confidence that this outcome is not due to random effects)


Run at least two experiments simulaneously with your infrastructure and for long enough to get confident results.

Note, you can run experiments with a *if*-statement within a single server implementation or you can use a router to decide between multiple servers with different code.


## Infrastructure Hints

As usual, you are free in choosing your own technology. 
While they might provide inspiration, do not use external service like [LaunchDarkly](https://launchdarkly.com/) or [split.io](https://www.split.io/),
but build your own infrastructure.
We assume that you will reuse much code from previous assignments.

While nice to have, you do not need to design a user interface for monitoring releases or creating, starting, or stopping experiments.
For A/B testing it is sufficient, when users of the experiment infrastructure need to learn how to edit configuration or code files and call scripts, as long as this process is described.


Although we do not set explicit requirements for quality assurance,
we suggest that you continue to write test cases for your infrastructure code
and conduct code reviews within your team.

If you hit resource limits of your virtual machine, contact the course staff.



## Deliverables

Set up your infrastructure in your virtual machine and commit your infrastructure code (including all scripts and configurations) to your Git repository. 
Submit a report (see below) as a single PDF to GitHub.
The report's first page should list all team members that contributed to the solution
and a link to the Git repository and directory where we can find your implementation.

In the report, describe:
* *Continuous integration*: Provide a link (and instructions or passwords if needed) to your Jenkins page that reports builds and tracks test coverage.
* *Continuous delivery, canary testing, and A/B testing infrastructure* (2 page text max): Briefly describe the infrastructure you have build for automated model updates, continuous delivery, canary testing, and A/B testing in this assignment. Describe key components (with links to their implementations) and how they interact. Describe how the individual components are triggered (e.g., what is automatically triggered, where are developers in the loop). An architectural diagram will likely be helpful. Please include clear references to the code in your repository.
* *Automated decisions in continuous delivery* (.5 pages text max): Describe which qualities you assess and what specific measures you use during a new release (both during the Jenkins phase and during the canary testing phase). Describe and justify how your system decides when to abort a release (thresholds, statistical tests, etc).
* *Release reports*: Provide evidence of at least one successful release, at least one release aborted during testing, and one release aborted during canary testing in production. Include the automatically generated messages and provide links to the corresponding commits and Jenkins jobs.
* *A/B experiments* (1 page text max): Describe two A/B experiments you conducted and their results. Describe the purpose of the experiments, and clearly document the setup (e.g., how many users are selected and how) with justification. Include or link to the generated reports for these tests.
* *Availability report*: Compute downtime of your service based on the logs in the Kafka stream and report the availability you achieved during the two weeks of this assignment. If you had significant downtime, explain the reasons for that downtime.
* *Reflection* (1 page text max): Look back at the assignment and the infrastructure you built. What worked well, what did not? Is your infrastructure itself robust? If you had more time or had to start over, what would you change? Would you consider using an external service like [LaunchDarkly](https://launchdarkly.com/) or [split.io](https://www.split.io/)?

As usual, all page limits are soft limits that can be broken if there is a specific reason. Screenshots and figures do not count toward the page limit.



## Grading

The focus of this assignment in on building infrastructure, automating deployments, and automating important decisions.

We will use approximately the following rubric for a total of 175 points:
 - [ ] 15 points: Continuous integration with Jenkins
 - [ ] 15 points: Automated updates of training data
 - [ ] 10 points: Automated learning of new models on code and data changes
 - [ ] 10 points: Automated testing and packaging of updated models
 - [ ] 30 points: Canary testing infrastructure, including necessary router, telemetry, and reporting components
 - [ ] 15 points: Successful demonstration of releases
 - [ ] 20 points: A/B testing infrastructure
 - [ ] 15 points: Evidence of two A/B tests
 - [ ] 10 points: Appropriate use of statistics for decision making and reporting
 - [ ] 15 points: Meaningful reflection, grounded in your experiences from this assignment, beyond superficial statements and mere truisms.
 - [ ] 15 points: Report and code quality, including quality of your commit log
 - [ ] 5 points: Low downtime through the assignment


Unless exceptional situations arise that require a discussion with the course staff, all team members who contribute to the solution will receive the same grade. Please try to first solve teamwork issues within the team and contact the course staff for advice and help if the situation does not improve.
