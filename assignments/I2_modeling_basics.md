# Individual Assignment 2: Modeling Basics

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

This assignment is intended as a warmup to get familiar with the basics of machine learning tools and the challenges involved in gathering data. This assignment will use data from a Netflix-like movie streaming service.

Learning goals:
* Collect data from multiple sources and engineer features for learning
* Apply state of the art machine learning tools
* Evaluate a model on a fixed dataset

## Tasks

Consider you are in the early days of video streaming and are building a Netflix-like streaming business with a massive catalog of movies. Currently, the service has one million users and about 27.000 movies. We will focus on recommending movies later, but in this assignment, the goal is to predict the expected popularity of movies to plan movie acquisitions and royalty payments. That is, you want to predict for a given movie, how frequently it will be watched per day (`predictPopularity: Movie -> Int`). 

Note, that the scenario is intended to predict the popularity of movies that are not yet available for streaming yet. Therefore, although you have access to watching behavior for all movies, you should not use past watching numbers of a movie when predicting that movie's future popularity. You can of course use the popularity of other, possibly similar, movies on the platform.

**Provided data:** We provide an event stream (Apache Kafka) of a streaming service site that records server logs, which include information about which user watched which video and ratings about those movies. In addition, we provide read-only access to an API to query information about users and movies. In addition, you should collect data at least from one external data source not provided by the course staff; for example, ids for [IMDB](https://www.imdb.com/) and [TMDB](https://www.themoviedb.org/) are provided for each movie.

You do not need to use all provided data, but should use most of it and not down-sample too much for the final model. Plan for the fact that data gathering may take some time; the provided raw data is fairly large and you may need some time to download and process it (if Internet bandwidth is a problem, consider performing some preprocessing on the [public Linux](https://www.cmu.edu/computing/services/endpoint/software/how-to/timeshare-unix.html) or [Virtual Andrew](https://www.cmu.edu/computing/services/endpoint/software/virtual-andrew.html) machines within the CMU network).

The addresses and credentials for the provided event stream and the API can be found on Canvas.

**Modeling:** Learn a model to predict a movie's popularity. You have full freedom in deciding what technology to use, what data to collect and how, how to clean data, how to extract features, which feature to extract, what kind of model to learn with what kind of tools. You may develop everything in a notebook or use any other infrastructure, including external tools and services, as long as you document your process and make all artifacts available to the course staff.

**Evaluation:** Evaluate the quality of your model with a suitable evaluation strategy. As part of the evaluation you should compare at least to two baseline heuristics.

**Prediction service:** Provide a command line tool (e.g., `predict.py`) or web service that uses the learned model to performs the prediction and returns the predicted popularity of the movie (measured in "expected watches per day"). Describe the expected inputs for the prediction (command line options or API parameters). 
Make the prediction service independent of the learning infrastructure; to achieve this you will need to serialize the learned model into a file after learning and load it in the prediction service.

**Demonstrate model improvement:** You will likely need to iterate over your model repeatedly as you test different features or different learning techniques. Keep at least one prior or alternative model and demonstrate how changes (e.g., different learning technique or additional feature) have lead to better model accuracy.

You have considerable freedom in how you approach this task. You are free to chose programming language and libraries as you wish. 


## Deliverables

Deliverables consist of a report (single PDF file) and supporting artifacts. Upload the report to Gradescope, ideally separating different report sections on different pages. For supplementary artifacts, preferably upload artifacts to the provided GitHub repository (see signup link on Canvas) and upload large files (>50mb) to your CMU box account (http://cmu.box.com/). In either case, make clear from your report where to find any artifacts that you refer to with links, page numbers, line numbers or similar.

The report should answer the following questions in clearly labeled sections of the document:

* Overall process (max 1 page): Describe your overall approach to developing the model. What was your basic strategy? How did you start? How did you iterate? How did you decide when to stop?
* Data and cleaning (max 2 pages): Describe the data you used for learning (provided and external), how you gathered it, and describe how you cleaned the data. The data collected must include at least one external data source.
* Features: Provide a full list of all features used in the model and a short description of how they were extracted. Provide a pointer to the implementation of the feature extraction process, as appropriate.
* Learning (max 1 page): Describe the learning techniques used, hyperparameters chosen, and provide a pointer to the implementation. Provide a brief explanation why you decided to use this specific technique with these hyperparameters. Provide a pointer to the final model learned.
* Evaluation (max 1 page): Describe how you evaluated the model. This should include at least a description of the evaluation metric and the evaluation data and the baseline heuristics used for comparison. Briefly justify why the chosen metric is appropriate for this evaluation and justify how the training/validation/test split is appropriate for this problem. Provide a pointer to the evaluation code.
* Prediction service (max .5 pages): Provide a pointer to the implementation of the prediction service and a brief description of how to use it.
* Evaluation results: Provide the evaluation results. This will include at least 4 results: Results for 2 baseline heuristics, results for the final model, and results for one alternative or prior model (e.g., different learning techniques or different features). Provide a pointer to the corresponding artifacts.

On page limits: Figures and tables do not count toward the page limit. All page limits are soft limits that should usually be obeyed but can be exceeded if there are specific reasons (e.g., unusual decisions that need more space for explanations).

## Optional Bonus: Implementing Random Forest Learning

Implementing your own learning technique can be useful to understand how learning techniques really work. We will provide **50 bonus points** if you implement your own **random forest** learning technique and compare it against results achieved with off-the-shelf implementations (e.g., in scikit learn) for the learning problem of this assignment. You may complete this part also **at any point later in the semester** up to the day of the last lecture.

You may use libraries for some parts of your implementation (e.g., Pandas for data frames) and look at textbooks and examples, but the actual learning code should be entirely your own implementation.

To complete this bonus part, commit a reasonably documented implementation to your GitHub repository and include an entry point that applies your learner to the dataset and reports results (notebook or command-line script). Either include an extra page in your report with the original submission or send an email with a pointer to the course staff.

## Grading

We expect a reasonable job for data cleaning, feature extraction, learning, and model evaluation that demonstrates a basic understanding of all involved tasks. We expect readable code for all involved steps (with documentation where necessary). We do NOT have any expectations with regard to model accuracy of the resulting model; you may receive full credit even with models that do not perform well.

We will use approximately the following rubric for a total of 150 points:
 - [ ] 10 points: Overall approach to modeling described
 - [ ] 30 points: Data gathering and data cleaning performed and described; all or most movies considered in the dataset and at least one external data source used
 - [ ] 20 points: Feature extraction performed and described
 - [ ] 20 points: Learning performed and described, learning technique and hyperparameters reasonably justified
 - [ ] 30 points: Evaluation of final model performed and described. The evaluation metric is clear and suitably chosen. Two reasonable baseline heuristics are described and implemented. The use of evaluation data is appropriate.
 - [ ] 10 points: Predictive service that is independent from the learning infrastructure is provided and sufficiently documented
 - [ ] 10 points: Evaluation results reported show that the final model outperforms the baseline heuristics and the alternative/prior model.
 - [ ] 20 points: Report and code quality (structure, readability, documentation)
 - [ ] optional: 50 bonus points for implementing and using own random forest learning technique

