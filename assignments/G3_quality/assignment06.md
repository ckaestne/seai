# Group Assignment 3: Infrastructure Deployment and Testing

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

After experimenting with different modeling techniques on a static data set, it is now time to transition the movie recommendation mechanism into production.
You will refactor your system, such that you can automate all data acquisition and learning steps,
you will test your infrastructure code,
you will deploy your recommendation engine,
and you will evaluate model quality in production.

Learning goals:
* Test all components of the learning infrastructure
* Build infrastructure to assess model and data quality
* Deploy a model inference service in a container
* Build an infrastructure to evaluate a model in production



## Tasks

### Pipeline implementation

Transition your learning, evaluation, and inference code to a code structure
that could be used for production and that it can be tested. That will likely
involve splitting code for different steps in the pipeline into separate
modules that can be called independently.
If you used a Jupyter notebook before, now is the time to transition
command-line programs.
Decide how you share data between
each step (e.g., where to store the training and evaluation data, 
how to serialize the learned model). Use a fresh directory in your team's GitHub
repository or create a fresh repository.

Note that your program should cover the entire pipeline. For example, it
should have functionality to gather training/evaluation data from the Kafka
stream and the provided APIs (and possibly other data sources), to clean data,
and extract features. All those steps should be reasonably robust and
repeatable. You may store intermediate results in files or databases on your
virtual machine if you like, but you should be able to recreate that data from
scratch with your infrastructure.

At this point, we do require that you work with Git for all your code and
changes. Make reasonably cohesive commits with appropriate commit messages.

Automate (offline) model evaluation and write the evaluation results of
the model in a file that is stored together with the model, that could be
used for later comparison. You do not need to create a visual frontend 
for this assignment,
but you want to store the results in a machine readable format (e.g., JSON)
to make future processing and presentation easier.

Overall, the implementation should make it easy to run the pipeline for experimentation
(e.g., after changing model parameters) or on more recent data.


### Data quality

As part of your pipeline, design and automate data quality checks for all
inputs and decide how to handle low quality data. Write test cases to assure
that your data quality checks and repair or notification mechanisms work
correctly. Focus on data schema issues, missing data, and duplicate data;
you do not need to attempt to detect semantic drift or distribution changes.


### Inference service and testing in production

Build a model inference service that provides movie recommendations on request
given a learned model.
Specifically, we will start to send http calls to 
`http://<ip-of-your-virtual-machine>:8082/recommend/<userid>`
to which your service should respond with an ordered comma separated list of up to
20 movie IDs in a single line; we consider the first movie ID as the highest
recommended movie. You can recognize whether your answer
has been correctly received by a corresponding log entry in the Kafka stream.
Package the service with all necessary dependencies in a Docker container
and commit the `Dockerfile` to your repository.
Aim for reasonable availability of your service.

If you have performance challenges to meet a large number of API requests,
reach out to the course staff to explore options.

Design and implement an approach to evaluate model quality *in production*.
Specifically, identify how well your recommendations are doing
and create daily reports.
Again, you do not need to create a graphical frontend, but we recommend
to store data in a machine-readable format for future use.

### Infrastructure testing

Evaluate *infrastructure code quality* by testing all steps in your model
learning and evaluation pipeline  (e.g., data extraction, data cleaning,
feature extraction, learning,  serving, telemetry). Use automated unit tests
and report test coverage. You may want to refactor your code, e.g., extract
the code that parses a line from Kafka as a separate function, to make it
easier to test. Include instructions in your README.md file on how we can run
your unit tests. We recommend, but do not require to set up automated testing
with a continuous integration service (e.g., installing Jenkins on your
virtual machine). Make and justify decisions about how much testing is
appropriate to gain confidence in the correctness and robustness of your
solution.


### Infrastructure Hints

You are free in choosing your own technology. If using Python, you may 
want to look into `Flask` for developing your service; for unit testing
consider Python's builtin `unittest` or the external `nose2` or `pytest`,
`coverage.py` or `Pytest-cov` can be used to measure coverage.
Separate tests in a folder distinct from your main code.

We assume that you will reuse much code from previous assignments but
expect that you will likely have to refactor your implementation.
We expect that additional code will be required primarily for 
serving the model, data quality checks, and infrastructure tests.

During and after this assignment, we may inject data quality issues
in the Kafka stream or provided API or we may make invalid requests
to your API. Try to make your service robust, such that it continues
to work despite such problems.

If you hit resource limits of your virtual machine, contact the course staff.

## Deliverables

Submit a report (see below) as a single PDF to GitHub.
The report's first page should list all team members that contributed to the solution
and a link to the Git repository and directory where we can find your implementation.

The prediction service should be deployed in a docker container within your virtual machine 
and should answer requests after the assignment's deadline. 
The implementation should be committed to your Git repository.

In the report, describe:
* *Code structure* (.5 pages text max): Briefly describe how the code for your learning pipeline is structured (e.g., modules, their purpose, their interactions, and exchanged files). A diagram that gives an overview of code modules and datasets will likely help.
* *Data quality steps* (1 page text max): (1) Describe what steps you have taken to assure data quality, including how you detect and how you repair or report issues. (2) Provide links to corresponding test cases. (3) Briefly justify why you focus on the issues you described (e.g., why they are important or economical to check) and (4) provide a list of issues that might go undetected by your current implementation.
* *Evaluation in production* (1 page text max): Briefly describe how you evaluate the quality of your model in production. Include a report of model quality measured in production.
* *Testing strategy* (1 page text max): (1) Briefly describe how you tested your infrastructure and (2) discuss how confident you are in the correctness and robustness of your solution. (3) If you had more time, how would you improve testing? (4) Include a generated coverage report (e.g. screenshot).

As usual, all page limits are soft limits that can be broken if there is a specific reason. Screenshots and figures do not count toward the page limit.



## Grading

The focus of this assignment in on engineering a robust and tested pipeline. We expect
reasonable implementation and test quality (including appropriate code structure).

We will use approximately the following rubric for a total of 100 points:
 - [ ] 15 points: Deployment of the model inference service using a Docker container
 - [ ] 15 points: Well structured implementation of the infrastructure, covering all steps of the pipeline
 - [ ] 20 points: Reasonable and well tested checks for data quality
 - [ ] 20 points: Good tests and appropriate discussion of test adequacy
 - [ ] 15 points: Description and implementation of testing in production and corresponding test result
 - [ ] 15 points: Report and code quality, including quality of your commit log

Unless exceptional situations arise that require a discussion with the course staff, all team members who contribute to the solution will receive the same grade. Please try to first solve teamwork issues within the team and contact the course staff for advice and help if the situation does not improve.
