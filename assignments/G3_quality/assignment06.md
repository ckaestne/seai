# Group Assignment 3: Quality

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

## Pipeline implementation

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

At this point, we require that you work with Git for all your code
and changes. Make reasonably cohesive commits with appropriate commit
messages.

Automate (offline) model evaluation and write the evaluation results of
the model in a file that is stored together with the model, that could be
used for later comparison. You do not need to create a visual frontend 
for this assignment,
but you want to store the results in a machine readable format (e.g., JSON)
to make future processing and presentation easier.

Overall, the implementation should make it easy to run the pipeline for experimentation
(e.g., after changing model parameters) or on more recent data.


## Data quality

Design and automate data quality checks for all inputs and decide how to handle
low quality data. Write test cases to assure that your data quality checks
and repair/notification mechanisms work correctly.


## Inference service and testing in production

Build a model inference service that provides movie recommendations on request
given a learned model.
Specifically, we will send http calls to `http://<ip-of-your-virtual-machine>:8082/recommend/<userid>`
to which your service should respond with a comma separated list of up to
20 movie IDs in a single line. You can recognize whether your answer
has been correctly received by a corresponding log entry in the Kafka stream.
Package the service with all necessary dependencies in a Docker container
and commit the `Dockerfile` to your repository.
Aim for reasonable availability of your service.

Design an implement an approach to evaluate *model quality* in production.
Specifically, identify how well your recommendations are doing
and create daily reports.
Again, you do not need to create a graphical frontend, but we recommend
to store data in a machine-readable format for future use.

## Infrastructure testing

Evaluate *infrastructure code quality* by testing all steps in your model
learning and evaluation pipeline  (e.g., data extraction, data cleaning,
feature extraction, learning,  serving, telemetry). Use automated unit tests
and report test coverage. Include instructions of how to run your unit tests.
We recommend, but  do not require to set up automated testing with a
continuous integration service (e.g., installing Jenkins on your virtual
machine). Make and justify decisions about how much testing is appropriate to
gain confidence in the correctness and robustness of your solution.



## Deliverables

Submit a report (see below) as a single PDF to GitHub.
The report's first page should list all team members that contributed to the solution
and a link to the Git repository and directory where we can find your implementation.

In the report, describe:
* Code structure (.5 pages): Briefly describe how the code for your learning pipeline is structured (e.g., modules, their purpose, their interactions, and exchanged files).
* Data quality steps


* an implementation for learning tasks 
* running prediction service
* test coverage report
* a list of data quality issues that are automatically detected and pointers to corresponding test cases
* report of accuracy in production and comparison on previous eval on static dataset


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
