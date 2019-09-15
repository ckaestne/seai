---
author: Eunsuk Kang
title: "17-445: Trade-offs among AI Techniques"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Eunsuk Kang"
---  

# Trade-offs among AI Techniques

Eunsuk Kang

<!-- references -->

Required reading: Hulten, Geoff. "Building Intelligent Systems: A
Guide to Machine Learning Engineering." (2018), Chapters 6, 7, and 24.

---
# Learning Goals

* Understand the major types of ML tasks and learning methods

* Organize and prioritize the relevant qualities of concern for a given project

* Plan and execute an evaluation of the qualities of alternative AI techniques for a given purpose

---
# Selection

----
## AI != Deep Learning

![AI vs ML](AIvsML.jpg)

(In this lecture, we will focus on ML)

----
## ML Methods

![ml-methods-poll](ml-methods-poll.jpg)

----
# Selection

## How do I decide which ML technique to use for my project?

----
## Criteria: Attributes & Constraints

* Attributes 
  * Quality attributes: What the user experiences 
	* Performance, reliability, availability...
  * Project attributes: Time-to-market, development & HR cost
  * Design attributes: Type of ML method used, accuracy, training
    time, prediction time, memory usage
* Constraints: What you must satsify
  * Problem constraints: What the product must provide to the user
  * Project constraints: Deadline, project budget, available skills
  * Design constraints: Type of ML task required, limits on computing resources, data
	availability

---
# Types of ML Tasks

----
## ML Tasks

* Classification
* Regression
* Clustering
* (Dimensionality reduction)

----
## Classification

![spam-filter](spam-filter.png)

* Which one of the given categories does a new
observation belong to?
	* e.g., e-mail spam filter, pedestrian detection
	* Output is a _categorical_ value

----
## Regression

![hurricane](hurricane.gif)

* What is the estimated value for an output given an observation?
	* e.g., weather forecasting, sales prediction
	* Output is a _numercal/continuous_ value

----
## Clustering

![social-network](social-network.jpg)

* What is the best way to divide a set of observations into
distinct groups?
	* Output is a set of categories 
	* e.g., human genetic clustering, social network analysis

<!-- references -->

_An Exploration of Social Identity: The Geography and Politics of
News-Sharing Communities in Twitter_, Herdagdelen et al. (2012)

----
## Example: Product Recommendation

![Product recommendations](recommendations.png)

### Q. What type of ML task(s) does the system perform?

---
# Attributes of ML Methods

----
## Attributes 

* Type of ML task: Classification, regression, or clustering?
* Type of data required
  * Labeled vs. not labeled
  * Categorical vs. numerical
* Accuracy: (Number of correct predictions) / (Total number of predictions)
* Interpretability: Why did the model make decision X?
* Complexity
   * Linear vs. non-linear relationship between input & output variables
   * Number of features
* Training costs
  * Amount of training data required to reach high accuracy
  * Training time
* Model size: Can you store all your model in memory?
* Incrementality: Can you improve the model by gradually adding more data?
* Inference time: How long does it take for the model to make a decision?

----
## Accuracy for Binary Classification

![accuracy-metrics](accuracy-metrics.jpg)

* Recall = TP / (actual positive) = TP/ (TP + FN)
* Precision = FP / (actual negatives) = FP / (TN + FP)

---
# Types of ML Methods

----
## Linear Regression

![linear-regression](linear-regression.png)

* Tasks: Regression 
* Linear relationship between input & output variables
* Easy to interpret, low training cost, small model size
* Can't capture non-linear relationships well

----
## Decision Tree Learning

![decision-tree-fraud](credit-card-fraud.png)

* Tasks: Classification & regression
* Non-leaft nodes: Conditional on input variables
* Leaf nodes: Class labels or continuous output values
* Easy to interpret; can capture non-linearity; can do well with
  little data
* Low accuracy (high risk of overfitting); possibly very large tree size

----
## Neural Network

![neural-network](neural-network.png)

* Tasks: Classification & regression
* High accuracy; can capture a wide range of problems (linear & non-linear)
* Difficult to interpret; high training costs (time & amount of
  data required, hyperparameter tuning)

----
## k-Nearest Neighbors (kNN)

![knn](knn.png)

* Tasks: Classification & regression
* Infer the class/property of an object based on that of _k_ nearest neighbors
* _Lazy learning_: Generalization is delayed until
  the inference takes place 
* Easy to interpret; little training costs (due to lazy learning)
* Potentially slow inference (again, due to lazy learning); high data storage
  requirement (must store all training instances)

<!-- ---- -->
<!-- ## K-Means Clustering -->

<!-- ![k-means](k-means.png) -->

<!-- * Task: Clustering -->
<!-- * Fast (for small _k_) -->
<!-- * Manual choice of _k_ -->

<!-- ---- -->
<!-- ## Hierarchical Clustering -->

<!-- ![hierarchical](hierarchical.png) -->

<!-- * Task: Clustering -->
<!-- * Can produce hierarhical clusters -->
<!-- * Slower than k-Means -->

----
## Ensemble Learning

![ensemble-learning](ensemble.png)

* Combine a set of low-accuracy (but cheaper to learn) models to
provide high-accuracy predictions
* Techniques:
  * Boosting (e.g., gradient boosting)
  * Bagging (random forest)
  * Stacking

----
## Random Forest

![random-forest](random-forest.png)

* Randomly construct lots of decision trees
* Final output is the mode (for classification) or mean (regression) of 
  individual trees
* High accuracy & reduced overfitting; incremental (can add new trees)
* Reduced interpretability; large number of trees can take up space

----
## Other Learning Methods

* Logistic regression 
* Support vector machine (SVM)
* Naive Bayes
* Principal component analysis (PCA)
* Markov networks
* Clustering methods
  * k-Means, hierarchical clustering
* Symbolic methods
  * Multi-agent systems
  * Logic-based representations
* and more...

---
# Tradeoff Analysis

----
## Cost vs Benefit

![netflix-leaderboard](netflix-leaderboard.png)

_"We evaluated some of the new methods offline but the additional
accuracy gains that we measured did not seem to justify the
engineering effort needed to bring them into a production
environment.”_

<!-- references -->

_Netflix Recommendations: Beyond the 5 stars_, Amatriain & Basilico,
Netflix Technology Blog (2012)

----
## Trade-offs: Accuracy vs Interpretability

![trade-offs](tradeoffs.png)

<!-- references -->

_Overcoming the Barriers to Production-Ready Machine Learning
Workflows_, Bloom & Brink, O'Reilly Strata Conference (2014).

----
## Multi-Objective Optimization

![moo](moo.png)

* Determine optimal solutions given multiple, possibly
  **conflicting** objectives
* **Dominated** solution: A solution that is inferior to
  others in every way
* **Pareto frontier**: A set of non-dominated solutions 

----
## Selecting Optimal ML Methods

1. Identify a set of constraints 
2. Eliminate methods that do not satisfy the constraints
3. For each type of attribute, evaluate remaining methods
4. Eliminate dominated methods
5. Consider priorities among attributes to select an optimal solution

----
## Selection

![scikit-learn](ml_map.png)

---
# Summary

