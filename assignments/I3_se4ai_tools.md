# Individual Assignment 3: Software Engineering Tools for Production ML Systems

(11-695/17-445/17-645/17-745 Machine Learning in Production / AI Engineering)

## Overview

In this assignment, you will have a chance to explore modern tools that are useful for building AI-enabled systems. You will try them in the context of the movie streaming scenario and write a blog post about them.

Learning goals:
* Explore the ecosystem of software engineering tools for production ML systems
* Explain to other stakeholders the purpose of a tool

## Tasks

This assignment is very open-ended and you can customize it to your interests.

Pick an aspect of building production machine learning systems that you find interesting (e.g., requirements, testing in production, data quality, deployment, operations) and look for a tool that supports this task. You must pick a tool **that you are not yet familiar with** and that has not been discussed by students in previous semesters. Each student/team **must pick a different tool**; claim the tool of your choice in the Google Spreadsheet linked from Canvas. Try the tool in the context of the movie streaming example and write a blog post about the tool and your experience. Within 3 days after the deadline, read at least two other blog posts from other students and comment on them.

## Guidance and hints

**Picking a tool:** Claim the tool of your choice early so that you do not waste effort exploring a tool that is then claimed by somebody else. First come first serve. Please only claim one tool at any time, but you may change what tool you claim if your first choice does not turn out to be interesting or usable.

Unless you think the blog post is shallow and that you can do better, the following tools were discussed in previous semesters and should not be selected: [Amazon Sagemaker](https://medium.com/@jackyzou1997/a-gentle-introduction-to-aws-sagemaker-ml-ai-on-the-cloud-de8dd0191818), [Apache Airflow](https://medium.com/balancing-lines/automating-data-pipeline-using-apache-airflow-444e695181e9), [Apache Flume](https://wenfeiy.medium.com/a-gentle-introduction-toapache-flume-1ce715475129), [Apache Hadoop](https://medium.com/@sanshang/first-try-on-apache-hadoop-fe24aee66665), [Apache Spark](https://medium.com/@abellamk/apache-spark-with-pyspark-a-step-by-step-approach-2448a1216cd9), [Auto-Surprise](https://wangxingchen2930.medium.com/auto-surprise-automates-algorithm-and-hyperparameter-tuning-ee8f01b9f354), [BentoML](https://medium.com/@maahin_beri/using-bentoml-to-serve-scikit-models-10f54c29dfc9), [CML](https://medium.com/@karthik.vaithyanathan/using-continuous-machine-learning-to-run-your-ml-pipeline-eeeeacad69a3), [Cortex](https://medium.com/@nsgupta.vivek/model-deployment-automation-with-cortex-45c48aaed063), [DVC](https://medium.com/@nwest_7200/a-brief-introduction-to-data-version-control-dvc-82ec5ee76c2b), [Grafana](https://zexuannotes.com/using-grafana-prometheus-and-postgresql/), [Great Expectations](http://wordpress.com/2020/10/29/what-to-expect-with-great-expectations/), [Holoclean](https://medium.com/@jacob.tanenbaum/a-first-look-at-holoclean-205ca7c71369), [Kedro](https://prathit-p.medium.com/kedro-software-engineering-principles-for-data-science-6eced3cc3390), [Kubeflow](https://trungdcn.medium.com/kubeflow-managing-the-whole-machine-learningcycle-c9e6a6149d91), [Kubernetes](https://medium.com/@mazzottacraig/deploying-a-flask-application-with-kubernetes-8a491c220b59), [Luigi](https://jimmdd.medium.com/exploring-spotifys-luigi-to-build-etl-pipeline-97309dc01fd9), [MLflow](https://medium.com/@kevin.n.lu123/mlflow-managing-your-ml-pipeline-from-training-to-deployment-7e0d87df9d), [ModelDB](https://medium.com/@songrcs/versioning-your-dataset-and-models-using-modeldb-10b0ee3873ed), [Neo4j](https://medium.com/@mohonisc/recommendation-system-with-neo4j-graph-database-f111ff377d07?sk=83eb1f72f810fea61fbb03df94e1459e), [pydqc](https://psbbvishal.medium.com/pydqc-eda-done-in-one-command-86ca8fca791f), [Snorkel](https://medium.com/@FanglinChen/snorkel-for-recommendation-system-3f7c10cbdb82), [TensorFlow Lite](https://medium.com/tensorflow-lite-for-android/exploring-tensorflow-lite-for-android-aca0e0c82ba), [TPOT](https://medium.com/@daniel.biales/automl-taking-tpot-to-the-movies-cf7e6f67f876?sk=6737cdd9d4cf2ff3c7322ee25f80fe70).

You may pick open source tools, academic prototypes, as well as commercial tools, as long as you can give the course staff access to your work. You may use your AWS credit for this assignment or sign up for trial versions if you like.

Pick a tool that you have not used before. Maybe there are tools that you have read about and are curious to explore.

If there is a tool that you wanted to explore but that has already been claimed, search for competitors of that tool.

The tool does not need to be directly related to machine learning or use machine learning, but should be plausibly fit into a production scenario where it supports or interacts with ML components in a larger system. For example, a distributed logging system may not be designed specifically for ML applications but would be a useful foundation for collecting telemetry. Avoid using pure data science tools (pure data exploration, notebook extensions, or standard machine learning libraries). If in doubt ask the instructors whether a tool is in scope. Here are a couple of examples you could consider, but you can [find](https://neptune.ai/blog/best-mlops-tools) [many](https://www.analyticsvidhya.com/blog/2019/07/21-open-source-machine-learning-tools/) [lists](https://github.com/EthicalML/awesome-production-machine-learning) with a little searching:

* MLOps, monitoring, and deployment: e.g. Kubernetis, MLflow, Kubeflow, Apache Flume, MCenter, Prometheus, Loki, Logstash, Elasticsearch, LaunchDarkly, Split.io
* Pipeline automation and best practices: e.g., Kedro, Airflow, Luigi, Dask
* Data and model versioning, experimentation: e.g., dvc, ModelDB, Neptune, TensorBoard, Weights & Biases, Comet.ml
* Data programming, data cleaning, best practices: e.g. Snorkel, Holoclean, Great Expectations, pydqc
* Testing tools: CheckList, IBM 360, IBM ART, Data Linter, Crowdsourcing Platforms, ease.ml/ci, Rainforest, JMeter
* Big data solutions: e.g., Sparks, Hadoop, Flink, Reflow, Dragster, Beam
* Learning at scale/in the cloud: e.g., Amazon SageMaker, TFX, Azure ML, Google Cloud AutoML, IBM Watson Studio, Databricks

**Trying the tool:** For the “try the tool” part, we expect at a minimum that you install/set up the tool and use it in the context of the movie streaming scenario (ideally for movie recommendations as in the group project or predicting movie popularity, but also other possible tasks in this larger scenario with the provided data are okay). Feed it with some sample data from the scenario. For example, you could set up a distributed logging system and feed it with telemetry data from the team project. You may, but are not required to, fully integrate the tool with your team project or previous homework solutions. You may use your team’s virtual machine if you coordinate with the rest of your team or use your AWS credits if suitable.

**The blog post:** Write the blog post for a general audience of readers interested in production machine learning (e.g., data scientists interesting in building production systems, software engineers interested in machine learning, self-taught enthusiasts interested in the topic). Importantly, avoid jargon and avoid assuming too much background knowledge. Other popular blogs might provide some ideas, such as https://towardsdatascience.com/ or many company blogs. You may also look for inspiration in blog posts written by students in previous semesters linked above.

The blog post should cover at least (1) the problem that the tool addresses, (2) a discussion how it helps with examples from the movie streaming scenario, and (3) a discussion of the strength and limitations of the tool.

We recommend that you post the blog posts publicly in a location of your choice (e.g., medium.com). If you have a personal blog, feel free to post it there. If you prefer to not post the blog post publicly, post it in the Discussion section of Canvas. If you post it in a public place that does not allow comments, create a discussion post on Canvas with a link, so that other students can comment there.

**The comments:** After the deadline read at least two other blog posts (you can find their links in the spreadsheet) and post comments on them. Comments can share additional experience, ask questions, or indicate insights you gained from reading the blog post. The comments are due 3 days after the assignment’s main deadline.


## Deliverable

Post the blog post, update the Google Spreadsheet with links, and submit a short PDF to Gradescope:

**(1) Post the blog post** publicly or in the discussion section on Canvas (on canvas use the prefix “Blog: ” for the title of the posting).

**(2) Update the Google Spreadsheet** linked from Canvas with the tool name and a link to your blog post by the assignment’s deadline. Within three days after the deadline add two more links to the comments you made on other blog posts to the Spreadsheet.

**(3)** Post a **PDF** to gradescope (likely just a single page, we use this primarily to track grades consistently in one place) covering:

1. **Blog post link:** Provide a link to the blog post
2. **Data links:** Provide a brief (max .5 page) description of for what and how you tried to use the tool in the context of the movie streaming scenario. Provide links (e.g., to GitHub) of where to find your configuration or use of the tool as evidence of you trying the tool with data from the movie streaming scenario, if appropriate. You may include screenshots, outputs, or logs if that is helpful, but there is no need to replicate information from the blog post. Provide credentials for external services, if needed. 
3. **Appendix (optional):** You may share additional information that you prefer not to include in the blog post (e.g., for readability or because it is sensitive information) with the course staff in this appendix.


## Grading

The assignment is worth 100 points. We will assign credit as follows:
* [ ] 10 points: The spreadsheet is filled out correctly and we can find your blog post and comments without asking. 
* [ ] 40 points: A blog post about the selected tool is posted that explains the problem that the tool addresses.
* [ ] 10 points: The blog post illustrates how the tool is useful in a production machine learning system with examples from the movie streaming scenario.
* [ ] 10 points: The blog post discusses the strength and limitations of the tool. 
* [ ] 10 points: The blog post is professionally written and suitable for a broad target audience of interested software engineers and data scientists, avoiding jargon and not expecting too much technical background. 
* [ ] 10 points: Evidence is provided that the tool was tried on data from the movie streaming scenario.
* [ ] 10 points: Two comments on other blog posts show an engagement with the content of those blog posts (i.e., not just “looks good” or “interesting!”).
* [ ] (optional) 3 bonus points if the blog post is posted publicly.

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class. We recommend a pairing on Canvas. If you deviate from the recommended pairing, you may *not* work together with a student with whom you have worked together on a previous individual assignment.

If you work together as a team, you can either submit a joint solution on Gradescope and a joint row in the spreadsheet, or you can submit solutions separately. If you submit a joint solution, both team members will receive the same grade. If you submit separate solutions, those solutions may share text or code, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.
