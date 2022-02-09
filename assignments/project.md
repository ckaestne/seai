# Group Project: Movie Recommendations

(11-695/17-445/17-645/17-745 Machine Learning in Production / AI Engineering)

## Overview

In this project, you will implement, evaluate, operate, monitor, and evolve a recommendation service for a scenario of a movie streaming service. You work with a scenario of a streaming service with about 1 million customers and 27k movies (for comparison, Netflix has about 180 million subscribers and over 300 million estimated users worldwide and about 4000 movies or 13k titles worldwide). Consider you are in the early days of video streaming and are building a Netflix-like streaming business with a massive catalog of (not very recent) movies.

The focus of this assignment is to *operate* a recommendation service *in production*, which entails many concerns, including deployment, scaling, reliability, drift and feedback loops.

The assignment has multiple milestones and a final project presentation. It has a total of 400 points.

## Overall mechanics and infrastructure

**Teamwork:** You will work on this project in your assigned teams. As a team, you will use a shared GitHub repository and a virtual machine to coordinate your work. Please establish a way of communication and collaboration that works for your team -- for example, a Slack channel and a Trello board. Please agree on how you take clear notes from meetings that include agreed tasks and responsibilities. We expect that team members will have different backgrounds and different amounts of experience with machine learning and software engineering -- this is intentional. Use the first milestone to identify strength and weaknesses, fill missing gaps in background knowledge, and teach each other about tools and practices that are effective for this task. We do not expect that all team members contribute equally to each part of the project, but we expect that all team members make every effort to be a good team member (attend meetings, prepared and cooperative, respect for other team members, work on assigned and agreed tasks by agreed deadlines, reaching out to team members when delays are expected, etc). We will regularly check in about teamwork and perform *peer grading* to assess team citizenship of individual students after every milestone (see this [paper](http://www.rochester.edu/provost/assets/PDFs/futurefaculty/Turning%20Student%20Groups%20into%20Effective%20Teams.pdf) page 28-31 for procedure details).

**Milestones:** For each milestone and the final presentation, there are separate deliverables, described below. The milestones are typically mostly checkpoints to ensure that certain functionality has been delivered. Milestones are graded on a pass/fail scheme for the criteria listed with each milestone. Teams may submit work for milestones late or redo milestones with their team tokens as described in the [syllabus](https://github.com/ckaestne/seai/blob/F2020/README.md#course-syllabus-and-policies).

Milestones build on each other. We recommend to look at all milestones before starting the project, as you may make different design decision and avoid  extensive rework.

**Infrastructure:** We provide a virtual machine for each team and will send recommendation requests to your virtual machines. You receive data about movies and users through an API and can access log files from past movie watching behavior through a Kafka stream (see Canvas for server addresses and credentials). We provide separate streams for each team (`movielog<TEAM>`). You will offer a prediction service from your virtual machine, but you do not need to run all your code on that machine. You may build a distributed system with multiple machines (e.g., using the provided AWS credits), where you use the provided virtual machine only as API broker or load balancer. You may request more computing resources from the course staff if the virtual machine’s resources are insufficient (not that this may take a few days and will require a system restart).

**Provided data:** We provide an event stream (Apache Kafka) of a streaming service site that records server logs, which include information about which user watched which video and ratings about those movies. The log has entries in the following format:

* `<time>,<userid>,recommendation request <server>, status <200 for success>, result: <recommendations>, <responsetime>` – the user considers watching a movie and a list of recommendations is requested; the recommendations provided by your service are included (or an error message if your service did not provide a valid response)
* `<time>,<userid>,GET /data/m/<movieid>/<minute>.mpg` – the user watches a movie; the movie is split into 1-minute mpg files that are requested by the user as long as they are watching the movie
* `<time>,<userid>,GET /rate/<movieid>=<rating>` – the user rates a movie with 1 to 5 stars

In addition, we provide read-only access to an API to query information about users and movies (see Canvas for address). Both APIs provide information in JSON format, which should be mostly self-explanatory. Note that movie data, including “vote_average”, “vote_count” and “popularity” fields come from some external database and do not reflect data on the movie recommendation service itself. In addition, you may collect data from external data sources not provided by the course staff; for example, ids for [IMDB](https://www.imdb.com/) and [TMDB](https://www.themoviedb.org/) are provided for each movie.

You do not need to use all provided data from the stream, but should use most of the relevant data and should not down-sample too much for the final model. Plan for the fact that data gathering and cleaning data may take some time; the provided raw data is fairly large and you may need some time to download and process it. If Internet bandwidth is a problem, consider performing some preprocessing on the [public Linux](https://www.cmu.edu/computing/services/endpoint/software/how-to/timeshare-unix.html) or [Virtual Andrew](https://www.cmu.edu/computing/services/endpoint/software/virtual-andrew.html) machines within the CMU network.

The addresses and credentials for the provided event stream and the API can be found on Canvas.

**Languages, tools, and frameworks:** Your team is free to chose any technology stack for any part of this project. You have root access to your virtual machine and are free to install any software you deem suitable. You also may use external data and services (e.g. cloud services) as long as you can make them also available to the course staff. For example, you can use the provided Amazon AWS credits for this project. Whenever you set up tools or services, pay some attention to configuring them with reasonable security measures; past student solutions have been actively exploited in past projects.

**Documentation and reports:** For all milestones, we ask you to discuss some aspects of your design decision and implementation. It may be a good idea to write general documentation that is useful for the team in a place that is shared and accessible to the team (e.g., README.md or wiki pages on GitHub). Conversely it may be a good idea to include text or figures you write for reports as part of the project documentation. Feel free to link to more detailed documentation from your report or simply copy material from existing documentation into the report.

In general, we do not much care about the format or location of where we can find parts of your answers, such as code and screenshots, as long as we can find it. Please make an effort to be clear where to find content if it is not copied directly into the report, preferably with direct links.



## Milestone 1: Recommendation Model and First Deployment

**Learning goals:**

* Collect data from multiple sources and engineer features for learning
* Apply state of the art machine learning tools
* Deploy a model inference service 
* Measure and compare multiple quality attributes of your model
* Practice teamwork and reflect on the process

**Tasks:** Get familiar working as a team. Take notes at team meetings about how you divide the work (who is going to do what and by when).

Train a model that can make movie recommendations for a specific user. There are many different forms of offering such services that may take past ratings or watch behavior and the similarity between users or between movies into account (you may want to look into collaborative filtering if you are not familiar; here is material from a past [recitation](https://github.com/ckaestne/seai/blob/S2020/recitations/06_Collaborative_Filtering.ipynb) that may be helpful).

You will likely explore different kinds of models developed with different modeling techniques. Compare those models in terms of (1) prediction accuracy, (2) training cost, (3) inference cost (or throughput in production), (4) model size, and (5) scalability. For each of these qualities define a measure and report measured results from at least two models (these could be different ML techniques or two models learned with the same ML technique but with different hyperparameters or different features or different libraries). 

Build a model inference service that provides movie recommendations on request given your learned model (e.g. using [flask](https://flask.palletsprojects.com/en/1.1.x/)). Specifically, we will start to send http calls to `http://<address-of-your-virtual-machine>:8082/recommend/<userid>` to which your service should respond with an ordered comma separated list of *up to 20 movie IDs* in a single line; we consider the first movie ID as the highest recommended movie. We will wait for answers to our requests for at most 800ms. *You can recognize whether your answer has been correctly received and parsed by a corresponding log entry in the Kafka stream* (expect to see an entry `<time>,<userid>,recommendation request <server>, status <200 for success>, result: <recommendations>, <responsetime>`).

Note that users of the streaming service will immediately see recommendations you make and your recommendations may influence their behavior.

For this milestone, we do not care about specifics of how you learn or deploy your model, how accurate or how fast your predictions are, or how stable your service is.

**Deliverables:** Submit your code to Github and tag it with `M1_done` and submit a short report to Gradescope that describes the following:

* *Learning* (1 page max): Briefly describe what data and what kind of machine learning technique(s) you use and why. Provide a pointer to your implementation where you train at least two different models (e.g. to GitHub or other services). 
* *Model comparison* (1 page of text max, the table does not count toward the page limit): Define a suitable measure for all five qualities above and explain how you operationalize the measure (i.e., how you gather data and translate it into a number). The description should be accurate enough that one could independently reimplement and repeat the measurement without having access to your code. Provide a link to any code you wrote to conduct the measurements. Provide a table that lists the five measurement results for the two models from the previous step and argue which of these models you will use in production. For example, this table could have rows for the five measures and columns for the two models and the cells would report the measurement results.
* *Prediction service* (1 page max): Briefly describe how you implemented the recommendation service and how you derive a ranking from your model. Provide a pointer to your implementation (e.g. to GitHub or other services).
* *Team process and meeting notes* (1 page of text max, figures do not count toward the page limit): Briefly describe how your team organizes itself. What communication channels do you use? How do you divide the work? How do you assign responsibilities? Provide pointers to notes taken at team meetings; the notes should describe how work was divided. 

In this and all future milestones, page limits are not strictly enforced and can be broken if there is a good reason. We prefer precise and concise answers over long and rambling ones.

**Grading:** The grading specifications below focus on completing the work and each part is graded pass/fail. We will not attempt to evaluate the quality of the prediction service. We will not try to distinguish between better and worse solutions, but will give full credit if the specification is met and none otherwise for each part. For example, forgetting to include a screenshot of or pointer to teamwork notes will mean that all 10 points for that part are deducted, even if the description is otherwise well done. The specifications should be clear enough that you can confidently judge yourself whether you have achieved the goal; if in doubt contact the course staff. Note that you can regain lost points by resubmitting the solution as described in the [syllabus](https://github.com/ckaestne/seai/blob/F2020/README.md#course-syllabus-and-policies).

This milestone is worth 100 points:

* [ ] 10pt: The report contains a description of the data used and the learning technique selected. The text explains why this approach was chosen. The described chosen approach matches the problem.
* [ ] 10pt: A link to the implementation of the learning step is provided. The implementation matches the description and addresses the learning problem. 
* [ ] 5pt each (up to 25pt): The report describes metrics and operationalization of the five qualities. Each metric is clearly defined and the description is sufficient to independently measure the quality. A pointer to implementation of each measurement is provided. The results of the measure are reported and match to the metric description and the models.
* [ ] 5pt: The report argues which of the compared models should be used in production.
* [ ] 10pt: The report contains a description of the prediction service and explains how a ranking is computed. 
* [ ] 10pt: A link to the implementation of the prediction service is provided. The implementation matches the description and serves ranked recommendations. 
* [ ] 10pt: The report includes a description of how the team was organized, including a description of communication channels and process for work division and responsibility assignments. A screenshot of/pointer to teamwork notes that describes how work was divided is provided.
* [ ] 10pt: The prediction services successfully answers at least 2000 recommendation requests in the day before or after the milestone deadline. To be successful, the answer must be well-formed and arrive within the time limit. You can check success yourself by looking for the status 200 message in the movielog; we use that same information for grading.
* [ ] 10pt: The prediction service answers at least 10% of all recommendation requests in the day before or after the milestone deadline with personalized recommendations (i.e., within the time limit, `200` status, not the same recommendation for every user).
* [ ] 3pt: Bonus points for social activity (see very end of this document)



## Milestone 2: Model and Infrastructure Quality

**Learning goals:**

* Test all components of the learning infrastructure
* Build an infrastructure to assess model and data quality
* Build an infrastructure to evaluate a model in production
* Use continuous integration to test infrastructure and models

**Tasks:** First, evaluate the quality of your model both offline and online. For the offline evaluation, consider an appropriate strategy (e.g., suitable accuracy measure, training-validation split, important subpopulations, considering data dependence). For the online evaluation, design and implement a strategy to evaluate model quality in production (e.g., chose and justify metric, collect telemetry).

Second, if you have not done so already, migrate your learning infrastructure to a format that is easy to maintain and test. That will likely involve moving out of a notebook and splitting code for different steps in the pipeline into separate modules that can be called independently. Test all steps of your pipeline so that you have reasonable confidence in the correctness, robustness, and possibly other qualities of your learning solution. Also test the correctness of your prediction service. Design, implement, and test a strategy to deal with data quality problems.

Finally, automate all your tests in a continuous integration platform. The platform should automatically build and test your pipeline and prediction service implementation and create reports for test results and coverage. The platform should also automatically trigger learning and evaluating a new model whenever pipeline code changes and report offline accuracy results.

At this point, we do require that you work with Git for all your code and changes. Make reasonably cohesive commits with appropriate commit messages. We recommend adopting a process with your team in which you use pull requests to review and integrate changes.

**Technical details:** The pipeline refers to all parts of the learning process. For example, it should have functionality to gather training/evaluation data from the Kafka stream and the provided APIs (and possibly other data sources), to clean data, and extract features, train models, evaluate predictions, serialize models, serve models, and collect telemetry. All those steps should be reasonably robust and repeatable. You may store intermediate results in files or databases on your virtual machine or in the cloud if you like, but you should be able to recreate that data from scratch with your infrastructure. Overall, the implementation should make it easy to run the pipeline for experimentation (e.g., after changing hyperparameters) or on more recent data.

Evaluate *infrastructure code quality* by testing all steps in your model learning and evaluation pipeline, especially all data transformation code. You do not need to test whether the machine-learning algorithm itself is correctly implementated, but should test that you can use it to learn a model. However, you may want to also test your server logic that uses the model for increased confidence. Use automated unit tests and report test coverage. For unit testing consider Python's builtin `unittest` or the external `nose2` or `pytest`; `coverage.py` or `Pytest-cov` can be used to measure coverage. You may want to refactor your code, e.g., extract the code that parses a line from Kafka as a separate function, to make it easier to test. However, you should not introduce any testing-specific flows in your code in this process. You may consider the use of mocks or stubs for testing. Make decisions about how much testing is appropriate to gain confidence in the correctness and robustness of your solution. For this, consider testing both positive and negative flows in your pipeline logic. It would be helpful to anticipate scenarios that may break your function and include defensive code to handle them. 

Writing unit tests for the online and offline evaluation code is not required, but is highly recommended. Your online evaluation logic is technically part of the deployment, and should be subject to all standards that hold for other components. You should consider writing unit tests for the telemetry/monitoring code in the online evaluation and the evaluation mechanism you chose in the offline evaluation. 

Set up an continuous integration service. You could install Jenkins on your virtual machine or use a cloud service, such as GitHub Actions, Travis-CI, and Circle-CI. You may use the same or different services for testing the infrastructure and automating the learning process. This service should run the unit test suites upon every build. You may need to restructure your code-base to run them efficiently (For example, in scenarios where your pipeline is written in Python but your server is in Java). You may also want to consider reporting a build failure when unit test failures are encountered.

Your continuous integration service should also trigger the learning pipeline, where your code/data change now trains and evaluates a new model. The evaluation results should be written to a log file. You can choose to configure the continuous integration service to decide when to trigger the learning pipeline. Typically, you should consider triggering it only when commits are made to your main branch and avoid training models for every branch.

You do not need to create a visual frontend for this milestone, but model-quality reports and continuous-integration reports should be stored in a readable format (preferably machine readable, e.g., csv or JSON, for future automation, but readable log files are also sufficient).

For data quality, focus on data schema issues, missing data, and duplicate data; you do not need to attempt to detect drift. During and after this assignment, we may inject data quality issues in the Kafka stream or provided API or we may make invalid requests to your API. Try to make your service robust, such that it continues to work despite such problems.

If you hit resource limits of your virtual machine, contact the course staff or consider using cloud resources. Typically, you should consider isolating your web service and pipeline environments if this happens. 

**Deliverables:** Submit your code to Github and tag it with `M2_done` and submit a short report to Gradescope that describes the following:

* *Offline evaluation* (1 page of text max): Briefly explain how you conduct your offline evaluation. This just include a description of the validation/test *data* and how it was derived (including a discussion of data dependence and important subpopulation if appropriate) and a brief description and justification of the used *metric*. Include or link to evaluation results in your report (figures do not count toward the page limit). Provide a pointer to the corresponding implementation in your code (preferably a direct GitHub link).
* *Online evaluation* (1 page of text max): Briefly describe the metric used for evaluating model quality in production, the telemetry data collected, and the operationalization of the metric. Include or link to evaluation results in your report (figures do not count toward the page limit). Provide a pointer to the corresponding implementation in your code (preferably a direct GitHub link).
* *Data quality* (0.5 pages max): Briefly describe the steps you have taken with regard to data quality and provide a pointer to the corresponding implementation in your code (preferably a direct GitHub link).
* *Pipeline implementation and testing* (1 page max): Briefly describe how you structured the implementation of your pipeline and how you conducted testing. Include or link to a coverage report (figures do not count toward the page limit). Briefly argue why you think the testing is adequate. Provide a pointer to the corresponding implementation and test suite in your code (preferably a direct GitHub link).
* *Continuous integration* (0.5 pages max): Describe your continuous integration setup both for infrastructure testing and for automatically training and evaluating models. Provide a pointer to the service (and credentials if needed to access the platform).

**Grading:** This milestone is worth 100 points: 

* [ ] 10pt: Most commits (>60%) are reasonably cohesive and contain reasonable commit messages. The code is generally reasonably well structured and understandable.
* [ ] 10pt: The report describes how the pipeline is implemented and structured and contains a pointer to the pipeline implementation. The implementation matches the description.
* [ ] 15pt: Data quality checks are described in the report and implemented (with a link to the implementation provided). The description matches the implementation. At a minimum, schema violations in inputs are detected and handled.
* [ ] 15pt: A suitable strategy for offline model evaluation is described in the report that covers (1) validation/test split, (2) a clear description of the used metric, and (3) a plausible justification of why the metric is suitable for the problem. A link to a corresponding implementation that matches the description is provided. Evaluation results are included or linked for the used model that were computed with the described process and metric.
* [ ] 20pt: A suitable strategy for online model evaluation is described in the report that covers (1) the metric used, (2) the telemetry data collected, and (3) how the metric is computed from the data. A link to a corresponding implementation that matches the description is provided. Evaluation results are included or linked that were computed with the described process and metric.
* [ ] 20pt: A description of how the pipeline was tested is included in the report and a link to the corresponding tests is included. The report argues why the performed testing was adequate. A coverage report is included or linked.
* [ ] 10pt: The infrastructure tests, model learning, and offline model evaluation are all automated with a continuous integration service and triggered automatically when code is changed on GitHub. A pointer to the service is provided.
* [ ] 3pt: Bonus points for social activity (see very end of this document)



## Milestone 3: Monitoring and Continuous Deployment

**Learning goals:**

* Deploy a model prediction service with containers and support model updates without downtime
* Build and operate a monitoring infrastructure for system health and model quality
* Build an infrastructure for experimenting in production 
* Infrastructure for automatic periodic retraining of models
* Version and track provenance of training data and models

**Tasks:** *Important: Read availability requirements. The service should be available during the 7 days before the milestone deadline.*

After gaining confidence in your infrastructure quality and automating essential tasks, we will now focus on deployment, versioning, and monitoring. 

First, containerize your model inference service (and possibly other parts of your infrastructure). Add support for switching between different versions without downtime (e.g., adding a load balancer). 

Second, setup an automated process to periodically train a new version of your model on more recent data and push those models into production (e.g. every 3 days).

Third, set up a monitoring infrastructure that monitors the health of your recommendation service (including availability) and the quality of its predictions. You might want to set up automated alerts if problems are detected.

Fourth, build or setup an experimentation environment, in which you can compare two models in production (e.g., for an A/B test or a canary release). This requires that you can route requests from different users to different models and collect and report results per model. Report confidence in differences between models using appropriate statistical tests. Demonstrate the experimentation infrastructure with a simple experiment (e.g., comparing models learned on different data or with different hyperparameters).

Finally, track provenance of your predictions and models such that for every prediction your recommendation service makes you can answer: (1) which version of the model has made the prediction, (2) which version of the pipeline code and ML frameworks has been used to train that model, and (3) what data has been used for training that model.

Keep your recommendation service running as much as possible for the remainder of the project. We will evaluate the availability in the *7 days before  and 3 days after the milestone deadline*. Prefer poor recommendations over missing or very slow answers from your service. We will look at the logs (public, in the Kafka stream) to assess downtime. 

**Technical details:** We recommend [Docker](https://www.docker.com/) to containerize your model serving infrastructure. You can package the model inside the container or have the container load the model from an external resource (e.g., mounted file system or web server). Your continuous integration/deployment infrastructure should automatically build a new container or reconfigure the container when needed. You can write your own simple load balancer in 10 lines of Python or Node.js code if needed, say with [flask](https://flask.palletsprojects.com/en/1.1.x/) or [express](https://expressjs.com/), so you can switch between multiple models without downtime. You can consider using a container repository service like [Docker Hub](https://docs.docker.com/docker-hub/) to manage your containers and their versions easily. 

We recommend to mostly use existing infrastructure for monitoring, such as [Prometheus](https://prometheus.io/) and [Grafana](https://grafana.com/). You may use external cloud services if you prefer. Monitor at least availability of your service (e.g., preferably analyzing the Kafka logs not just your server logs) and the model quality (measure from Milestone 2).

For experimenting in production, you can write your own infrastructure or use an external library or service (e.g., [LaunchDarkly](https://launchdarkly.com/) or [split](https://www.split.io/)). You will probably write your own simple load balancer to route traffic to different model servers depending on which users should see which model. You can use your existing telemetry infrastructure to identify model quality in production for each model. It is nice, but not essential, to have a visual frontend to adjust how users are divided between different models and to show differences in measured outcomes. If no such visual frontend is created, you might want to create a command-line tool to compute and print the results of the experiment.

Regarding provenance you, you have again full flexibility. You may use a tool like [dvc](https://dvc.org/) or write your own mechanisms. The key point is to being able to track all inputs used for a prediction when needed, e.g., for debugging. Consider tradeoffs among different qualities, such as the amount of data stored and the effort in retrieving it.

Although we do not set explicit requirements for quality assurance, we suggest that you continue to write test cases for your infrastructure code and conduct code reviews within your team.

If you hit resource limits of your virtual machine, contact the course staff or consider using cloud resources.

**Deliverables:** Submit your code to Github and tag it with `M3_done` and submit a short report to Gradescope that describes the following:

* *Containerization* (0.5 pages max): Briefly describe how you containerized and deployed your inference service and if/where/how you automatically create containers as part of the continuous integration/continuous deployment process.  Provide a pointer to the Dockerfile(s) and other relevant implementations (preferably a direct GitHub link).
* *Automated model updates* (0.5 pages max): Briefly describe how you automatically retrain and deploy updated models. Provide a pointer to the relevant implementation (preferably a direct GitHub link).
* *Monitoring* (0.5 pages text max): Briefly describe how you set up your monitoring infrastructure and what you monitor and whether and why you set alerts. Include a screenshot of your dashboard showing at least availability and model quality measures (figures do not count toward the page limit). Provide pointers to the corresponding code/infrastructure (preferably a direct GitHub link) and explain how we can access your dashboard (include credentials if needed).
* *Experimentation* (1.5 pages max): Briefly describe the design of your experimentation infrastructure. Describe how you split users between models, how you track the quality of each model, and how you report differences among models. Explain the statistical tests you use and justify why they are appropriate for this task. Include results of at least one experiment (screenshot or link, does not count against the page limit). Provide pointers to your implementation/infrastructure.
* *Provenance* (2 pages max): Describe how you version and track provenance of predictions and models. Explain how you can, for any past recommendation, identify the model version, the used pipeline version, and the used training data. Illustrate this with a concrete example of one past recommendation. Provide sufficient pointers such that the course staff could also identify the corresponding information for a given recommendation and find the corresponding data and implementation.

**Grading:** This milestone is worth 100 points: 

- [ ] 10pt: Infrastructure setup with containers described in the report, link to relevant implementations provided, and containers are running.
- [ ] 20pt: Models are automatically updated with more recent data. The report describes the process for retraining and deployment and provides pointers to the corresponding implementation. The description matches the implementation.
- [ ] 25pt: A monitoring infrastructure observes service availability and model quality. The report describes the infrastructure. The report describes and justifies what alerts were set up or why no alerts were used. A screenshot of the service is included and pointers to implementation and running dashboard are provided. The description matches the implementation.
- [ ] 25pt: An infrastructure for online experimentation is implemented and has been used for at least one experiment. Appropriate statistical tests are used to report confidence in the experiments’ results. The report describes how users are split, how quality is tracked, and how results are reported. A screenshot of an experiment’s outcome is included and links to the corresponding implementation are provided. The description matches the implementation.
- [ ] 10pt: The report describes how provenance is tracked. It explains how for a given prediction the responsible model can be identified and how for that model the corresponding pipeline version and training data can be identified. It illustrates that process with one concrete example. Links to the corresponding implementation are provided. The description matches the implementation.
- [ ] 10pt: The recommendation service is at least 80% available in the 7 days before the milestone’s deadline and the 3 days after (i.e., max downtime of 48h), while at least two updates are performed in that time period.
- [ ] 10 bonus points: The recommendation service is at least 98% available in the 7 days before the milestone’s deadline and the 3 days after, while at least two updates are performed in that time period.
- [ ] 3pt: Bonus points for social activity (see very end of this document)



## Milestone 4: Drift and Feedback Loops

**Learning goals:**

* Reason about feedback loops and adversarial attacks in machine-learning systems (optional)
* Design and implement a monitoring strategy to detect feedback loops and attacks

**Tasks:** Consider feedback loops due to recommendations (positive or negative), fairness, and the potential for attacking the recommendation system (e.g., poisoning and evasion attacks). Think about what responsibility you might have as company and as authors of the recommendation system. Plan how you would detect a feedback loop and what you can do to avoid negative consequences once detected. Analyze the system logs or models for traces of two feedback loops, fairness issues, or attacks.

**Technical details:** For analyzing feedback loops, fairness, and attacks, better solutions will follow a more systematic process than just brainstorming: It is useful to go back to requirements and analyze assumptions and perform some form of risk analysis.

For analyzing  issues with actual data, you will analyze past recommendations and user behavior, for example, changes in user behavior over time, recommendation quality differences for different populations, drift in recommendation requests or user behavior. We have no requirements for how to conduct this analysis but recommend to explore the data and share the results with a notebook.

We have introduced mechanisms for specific feedback loops in our infrastructure and may try to simulate an attack on your recommendation system during the assignments duration. It is okay if you look for feedback loops or attacks that are not actually occurring or detect issues that we did not plan for. You can receive full credit with a rigorous analysis, independent of whether you find any actual issues and independent of whether you detect the issues that we artificially encoded. 

**Deliverables:** Submit your analysis code and results to GitHub and submit a short report to Gradescope:

* *Conceptual Analysis of Potential Problems (process)* (2 pages max): Describe the process you used to analyze possible feedback loops, fairness, and attacks. Include some evidence that you followed this process in your analysis (copies or pointers). Evidence may take many forms, depending on your process, but might include mindmaps, requirements documents, or threat models.  
* *Conceptual Analysis of Potential Problems (results)* (2 pages max): Identify at least *two* potential feedback loops, *two* potential fairness issues, and *two* potential attacks. For each feedback loop, explain what might happen and what the positive or negative consequences are, and how it could be detected. For each fairness issue, describe the potential problem, the used notion of fairness, how it could be detected, and how it can be reduced. For each potential attack, describe the attack scenario, how it could be detected, how it could be mitigated or made harder to exploit, and what could be done once detected.
* *Analysis of Problems in Log Data* (2 pages max): Briefly describe how you analyzed *two* of the six potential issues (either feedback loop, fairness, or attack) in the telemetry data of your system. Summarize your key findings, including negative results. Provide pointers to the artifacts behind your analysis for details (ideally links to code or notebook files on Github).

**Grading:** The assignment is worth 60 points:

- [ ] 10pt: The report describes the *process* used to look for possible issues in the system. The report includes copies of/pointers to supporting artifacts that demonstrate that you followed the process.
- [ ] 10pt: The report describes *two* possible feedback loops, describes possible consequences, and strategies how to detect them. The discussed issues are plausible within the context of the recommendation service.
- [ ] 10pt: The report describes *two* possible fairness issues, describes the problem and corresponding notion of fairness, how it can be detected and how it can be reduced. The discussed issues are plausible within the context of the recommendation service.
- [ ] 10pt: The report describes *two* possible attacks on the system, describes how each could be detected, how each could be mitigated or made harder to exploit, and what could be done once detected. The discussed issues are plausible within the context of the recommendation service.
- [ ] 10pt *each* for *two* analyzed potential issues selected from the ones discussed above. The issue was analyzed with telemetry data, the analysis is clearly described, and the results are reported.

## Final Report and Presentation

**Learning goals:**

* Reflect on challenges building, deploying, and maintaining AI-enabled systems
* Reflect on challenges with regard to teamwork
* Effectively communicate technical decisions and summarize lessons learned

**Tasks:** Up to this point, the project focused on implementing and testing functionality, but you also now have multiple weeks of operating the service and observing its effects. This final part has two steps: (1) reflection on the infrastructure and teamwork and (2) a presentation. 

First, conduct a project postmortem: reflect on the entire group project and discuss which decisions were hard and why, which decisions you would change in retrospect, and what you would do differently if you were building this for an actual company (probably with more time but also with higher stakes). Also reflect on your experience of working as a team (remotely).

Second, create a 8 min presentation to the class presenting the project and your experiences. The presentation should cover some key design decisions and some results (e.g., quality measures or availability) and reflection, but generally you are free to chose how you focus your presentation. The target audience for this talk is other teams in this class: Share what you did and what you learned or found interesting or challenging. Note that all teams worked on the same project, so you can assume familiarity with the task and do not need to introduce basics.

**Technical details:** Good reflections are grounded in concrete experience and the specifics of the project. They avoid mere superficial statements and truisms. We are looking for honest reflections that are open about potential issues; we grade only the quality of the reflection, not the quality of the technical decisions or teamwork described in the reflection.

For the presentation, we recommend that you prepare slides and practice timing. All team members should have an active part in the presentation. You may prerecord the presentation and play the recording for the final presentation if you prefer.

**Deliverables:** Upload your slides to GitHub and submit the reflection to Gradescope with two sections:

* *Reflection on Recommendation Service* (2 page max): Looking back at the entire project in which you have designed, implemented, deployed, and monitored the recommendation service. What parts were the most challenging? Which aspects are still unstable and would require additional investment if you had to deploy the recommendation service at scale in production? How would you address these issues if you had more time and more resources?
* *Reflection on teamwork* (1 page max): Think back on your team's teamwork throughout this project. What went well or less well in the team assignments? What were some of the main challenges you faced in teamwork?  What could have been done better in your future collaboration in other teams? 

**Grading:** This final step is worth 40 points:

* [ ] 20pt: A presentation given to the entire class that describes key design decisions, results, and reflections on the entire project. The presentation is understandable to the target audience. Slides uploaded to GitHub.
* [ ] 10pt: Reflection on the recommendation service that makes a good faith attempt at critically discussing the project. The reflection is grounded in concrete experiences.
* [ ] 10pt: Reflection on teamwork throughout this project that makes a good faith attempt at critically discussing the team’s experience. The reflection is grounded in concrete experiences.
* [ ] 3pt: Bonus points for social activity (see very end of this document)



## Social Activities Bonus

We hope that the following can encourage some social interaction that goes beyond the technical parts of the team project. This is entirely optional.

Team members can earn 3 bonus points in each of the three milestones and the final report if they engage in a social activity with their team that is **not** related to any coursework. This could be in person or online. This could just be an informal happy hour, playing a board game or computer game together,  do a [puzzle](https://krazydad.com/) or [trivia quiz](https://nerdschalk.com/best-trivia-games-on-zoom/), watch a movie, or whatever you like, as long as it is not course related. If you do, post a photo or screenshot to the public Slack channel **#social** and tag all team members who participated. You can also join forces with other teams if you are looking for some friendly competition, no constraints.

We accept posts throughout the entire period while you are working on the milestone, and until 3 days after the corresponding milestone deadline, in case you want to use this to celebrate milestone completion.
