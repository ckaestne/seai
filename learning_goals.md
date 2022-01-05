# Learning Goals: Machine Learning in Production / AI Engineering (17-445/17-645/17-745/11-695)



## Lecture: Introduction and Motivation

Content:

* Lecture illustrates traditional view of machine learning and contrasts it with the challenges of building systems
* Contrasting software engineering and data scientist roles, outline need for collaboration
* Syllabus and class structure; introductions, and survey

Learning goals:

* Illustrate the engineering challenges for building a production system with ML components, beyond creating the model
* Summarize the respective goals and challenges of software engineers vs data scientists

Assignment:

* Case study analysis of an ML product



## Lecture: From Models to AI-Enabled Systems (Systems Thinking) ![Requirements](https://img.shields.io/badge/-Requirements-green.svg) ![Architecture](https://img.shields.io/badge/-Architecture/Design-blue.svg) ![QA](https://img.shields.io/badge/-Quality%20Assurance-orange.svg) ![Process](https://img.shields.io/badge/-Process-grey.svg)

Overview:

* Machine learning is typically a component of a larger system in production: AI-enabled systems consist of ML and non-ML components, developed with different processes, need to be integrated; AI is more or less dominant in those systems
* The lack of specifications and its consequences for composition and abstraction: Contrasting ML with non-ML components; inductive vs deductive reasoning
* System-level strategies to engineering systems from imprecise specifications and unreliable components (e.g., guardrails and other safety mechanisms)
* Thinking in pipelines not models
* Components of intelligent experiences and corresponding challenges (experience, intelligence, orchestration) within a larger system architecture; overview of design options and automation degrees, e.g., forcefulness of the experience
* Qualities of interest (beyond model accuracy)

Learning goals:

* Explain the consequences of the shift from deductive to inductive reasoning for abstraction and composition
* Explain how machine learning fits into the larger picture of building and maintaining production systems
* Explain the modularity implications of having machine-learning components without specifications
* Describe the typical components relating to AI in an AI-enabled system and typical design decisions to be made

References:

* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 5 (Components of Intelligent Systems).
* 🗎 Wagstaff, Kiri. "[Machine learning that matters](https://arxiv.org/abs/1206.4656)." In Proceedings of the 29 th International Conference on Machine Learning, (2012).
* 🗎 Sculley, David, Gary Holt, Daniel Golovin, Eugene Davydov, Todd Phillips, Dietmar Ebner, Vinay Chaudhary, Michael Young, Jean-Francois Crespo, and Dan Dennison. "[Hidden technical debt in machine learning systems](http://papers.nips.cc/paper/5656-hidden-technical-debt-in-machine-learning-systems.pdf)." In Advances in neural information processing systems, pp. 2503-2511. 2015.
* 🗎 Nushi, Besmira, Ece Kamar, Eric Horvitz, and Donald Kossmann. "[On human intellect and machine failures: troubleshooting integrative machine learning systems](http://erichorvitz.com/human_repair_AI_pipeline.pdf)." In *Proceedings of the Thirty-First AAAI Conference on Artificial Intelligence*, pp. 1017-1025. 2017.
* 🗎 O'Leary, Katie, and Makoto Uchida. "[Common problems with Creating Machine Learning Pipelines from Existing Code](https://research.google/pubs/pub48984.pdf)." Proc. Third Conference on Machine Learning and Systems (MLSys) (2020).

Blog post/lecture notes:

* [On the process for building software with ML components](https://ckaestne.medium.com/on-the-process-for-building-software-with-ml-components-c54bdb86db24)

  

## Lecture: Model Quality and Unit Testing (2 lectures) ![Quality Assurance](https://img.shields.io/badge/-Quality%20Assurance-orange.svg)

Overview:

* Traditional model accuracy measures, confusion matrix, precision/recall, ROC, …
* Establishing baselines, comparison against heuristics approaches
* Measuring generalization, overfitting, train/validation/test split, …
* Setting expectations for correctness, bugs, 
* Notions of test suits and coverage for models (e.g., test by population segment), black box test case design, coverage
* The oracle problem, metamorphic testing, fuzzing, and simulation
* Pitfalls of data leakage
* Automated assessment, regression testing, dashboards, continuous integration, experiment tracking (e.g., MLFlow, ModelDB)

Learning goals:

* Select a suitable metric to evaluate prediction accuracy of a model and to compare multiple models
* Select a suitable baseline when evaluating model accuracy
* Explain how software testing differs from measuring prediction accuracy of a model
* Curate validation datasets for assessing model quality, covering subpopulations as needed
* Use invariants to check partial model properties with automated testing
* Avoid common pitfalls in evaluating model quality
* Select and deploy automated infrastructure to evaluate and monitor model quality

Assignment (part of project):

* Assess model quality offline with suitable accuracy measure; establish baseline, avoid common pitfalls; automate accuracy measurement and track results with continuous integration


References:

* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), 19-20 (Evaluating Intelligence, Machine Learning Intelligence).
* 🗎 Ribeiro, Marco Tulio, Tongshuang Wu, Carlos Guestrin, and Sameer Singh. "[Beyond Accuracy: Behavioral Testing of NLP Models with CheckList](https://homes.cs.washington.edu/~wtshuang/static/papers/2020-acl-checklist.pdf)." In Proceedings ACL, p. 4902–4912. (2020).
* 🗎 Barash, Guy, Eitan Farchi, Ilan Jayaraman, Orna Raz, Rachel Tzoref-Brill, and Marcel Zalmanovici. "[Bridging the gap between ML solutions and their business requirements using feature interactions](https://dl.acm.org/doi/abs/10.1145/3338906.3340442)." In Proceedings of the 2019 27th ACM Joint Meeting on European Software Engineering Conference and Symposium on the Foundations of Software Engineering, pp. 1048-1058. 2019.

Blog posts/lecture notes:

* [A Software Testing View on Machine Learning Model Quality](https://ckaestne.medium.com/a-software-testing-view-on-machine-learning-model-quality-d508cb9e20a6) 
* [Machine Learning is Requirements Engineering — On the Role of Bugs, Verification, and Validation in Machine Learning](https://medium.com/ckaestne/machine-learning-is-requirements-engineering-8957aee55ef4)



## Lecture: Goals and Success Measures for AI-Enabled Systems ![Requirements](https://img.shields.io/badge/-Requirements-green.svg)

Overview:

* Thinking about the system: System goals vs model goals
* Business consideration for using machine learning
  * When and how AI can support system goals
  * Overall cost of operating an ML-component (e.g., data, learning, updating, inference cost)
* Brief intro into measurement
* Defining and measuring a systems goals

Learning goals:

* Judge when to apply AI for a problem in a system
* Understand that system goals may not directly relate to model accuracy
* Define system goals and map them to goals for the AI component
* Design and implement suitable measures and corresponding telemetry

Assignments:

* For a case study (Smart Dashcam scenario), describe system and model goals and their relation; define concrete measures

References:

* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 2 (Knowing when to use IS) and 4 (Defining the IS’s Goals)
* 🕮 Ajay Agrawal, Joshua Gans, Avi Goldfarb. “[Prediction Machines: The Simple Economics of Artificial Intelligence](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/6lpsnm/alma991019698987304436)” 2018 
* 🗎 Bernardi, Lucas, Themistoklis Mavridis, and Pablo Estevez. "150 successful machine learning models: 6 lessons learned at Booking.com." In Proceedings of the 25th ACM SIGKDD International Conference on Knowledge Discovery & Data Mining, pp. 1743-1751. 2019.



## Lecture: Quality Assessment in Production ![Quality Assurance](https://img.shields.io/badge/-Quality%20Assurance-orange.svg) ![Implementation/Operations](https://img.shields.io/badge/-Implementation/Operations-yellow.svg)

Overview:

* Linking models to system goals: Model accuracy vs system quality
* Limitations of unit testing, especially for AI components
* History of testing software in production, from beta tests to A/B testing and chaos experiments; *feature flags* and corresponding infrastructure
* Design of telemetry to assess business goals, model quality, and other indicators; discussion of proxy metrics and engineering challenges
* Introduction to monitoring infrastructure
* Online experimentation
  * Testing in production, chaos engineering
  * *A/B testing*
  * Necessary statistics foundation
  * Mitigating risks of testing in production
* Infrastructure for experimentation, planning and tracking experiments; introduction to MLOps

Learning goals:

* Explain the limitations of unit testing and the rationale for testing in production
* Design telemetry to assess model and system quality in production
* Build monitoring infrastructure to collect and show telemetry data
* Understand the rationale for beta tests and chaos experiments
* Plan and execute experiments (chaos, A/B, shadow releases, ...) in production
* Examine experimental results with statistical rigor
* Support data scientists with platforms providing insights from production data

Assignment:

* Part of group project: Design an experimentation platform to conduct A/B tests and compare results with statistical rigor

References:

* 🕮 Hulten, Geoff. "[Building Intelligent Systems: A Guide to Machine Learning Engineering.](https://www.buildingintelligentsystems.com/)" Apress, 2018, Chapter 15 (Intelligent Telemetry).
* 🕮 Alec Warner and Štěpán Davidovič. “[Canary Releases](https://landing.google.com/sre/workbook/chapters/canarying-releases/).” in [The Site Reliability Workbook](https://landing.google.com/sre/books/), O'Reilly 2018
* 📰 Georgi Georgiev. “[Statistical Significance in A/B Testing – a Complete Guide](http://blog.analytics-toolkit.com/2017/statistical-significance-ab-testing-complete-guide/#noninf).” Blog 2018
* 🗎 Nushi, Besmira, Ece Kamar, Eric Horvitz, and Donald Kossmann. "[On human intellect and machine failures: troubleshooting integrative machine learning systems](http://erichorvitz.com/human_repair_AI_pipeline.pdf)." In *Proceedings of the Thirty-First AAAI Conference on Artificial Intelligence*, pp. 1017-1025. 2017.
* Kang, Daniel, Deepti Raghavan, Peter Bailis, and Matei Zaharia. "[Model Assertions for Monitoring and Improving ML Model](https://arxiv.org/abs/2003.01668)." In Proceedings of MLSys 2020.



## Lecture: Risk and Planning for Mistakes (2 lectures) ![Requirements](https://img.shields.io/badge/-Requirements-green.svg) 

Overview:

* Inevitability of wrong predictions: Lack of specifications, deductive reasoning, common sources of wrong predictions
* System-level strategies to deal with unreliable components:
  * User interface design, incl. forcefulness, undo, setting expectations, …
  * Humans in the loop, incl. avoiding complacency, deciding where and when to ask for human judgment, …
  * Safeguards outside the model: guardrails, redundancies, voting, fallback, graceful degradation, …
* Decomposing requirements to understand problems
  * The world and the machine, explicit environment assumptions from specifications
  * Considering drift, feedback loops, adversaries
* Introduction to risk analysis and fault trees: anticipate problems
  * Fault tree analysis, failure mode and effects analysis, hazard and interoperability study

Learning goals:

* Describe common reasons for why ML predictions can fail
* Analyze how mistake in an AI component can influence the behavior of a system
* Analyze system requirements at the boundary between the machine and world, consider drift, feedback loops, and adversaries
* Evaluate risk of a mistake from the AI component using fault trees
* Design and justify a mitigation strategy for a concrete system

Assignment:

* Write requirements and plan mechanisms for dealing with mistakes; set system goals and define success measures; perform risk analysis

References:

* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 6--8, and 24.
* 🗎 Kocielnik, Rafal, Saleema Amershi, and Paul N. Bennett. "Will you accept an imperfect AI? Exploring designs for adjusting end-user expectations of AI systems." In *Proceedings of the 2019 CHI Conference on Human Factors in Computing Systems*, pp. 1-14. 2019.

Blog post/lecture notes:

* [The World and the Machine and Responsible Machine Learning](https://medium.com/@ckaestne/the-world-and-the-machine-and-responsible-machine-learning-1ae72353c5ae)



## Lecture: Tradeoffs among Modeling Techniques ![Architecture](https://img.shields.io/badge/-Architecture/Design-blue.svg)![Requirements](https://img.shields.io/badge/-Requirements-green.svg)

Overview:

* Survey quality attributes of interest in production ML settings (e.g., accuracy, model size, inference time, learning time, incremental learning, robustness)
* Contrasting internals of two learning techniques: decision trees and deep learning and implications on various qualities
* Brief survey of other classes of machine learning and brief primer on symbolic AI
* Constraints and tradeoff analysis for selecting ML techniques in production ML settings

Learning goals:

* Organize and prioritize the relevant qualities of concern for a given project
* Explain they key ideas behind decision trees and random forests and analyze consequences for various qualities
* Explain the key ideas of deep learning and the reason for high resource needs during learning and inference and the ability for incremental learning
* Plan and execute an evaluation of the qualities of alternative AI components for a given purpose

Assignment:

* Present tradeoff analysis among two techniques (prepare memo for broad audience); for a given dataset evaluate which technique is more suitable after measuring various qualities

References:

* 🗎 Vogelsang, Andreas, and Markus Borg. "[Requirements Engineering for Machine Learning: Perspectives from Data Scientists](https://arxiv.org/pdf/1908.04674.pdf)." In Proc. of the 6th International Workshop on Artificial Intelligence for Requirements Engineering (AIRE), 2019.
* 🗎 Siebert, Julien, Lisa Joeckel, Jens Heidrich, Koji Nakamichi, Kyoko Ohashi, Isao Namba, Rieko Yamamoto, and Mikio Aoyama. "[Towards Guidelines for Assessing Qualities of Machine Learning Systems](https://arxiv.org/pdf/2008.11007)." In International Conference on the Quality of Information and Communications Technology, pp. 17-31. Springer, Cham, 2020.
* 🗎 Strubell, Emma, Ananya Ganesh, and Andrew McCallum. "[Energy and Policy Considerations for Deep Learning in NLP](https://arxiv.org/pdf/1906.02243.pdf)." In *Proceedings of the 57th Annual Meeting of the Association for Computational Linguistics*, pp. 3645-3650. 2019.



## Lecture: Architectural Design for AI-enabled Systems ![Architecture](https://img.shields.io/badge/-Architecture/Design-blue.svg)

Overview:

* Introduction to software architecture, data collection, and domain-specific modeling
* Discussion how quality goals for the system influence system architecture of production ML systems
  * Consider latency and data volume requirements and constraints when deciding on deployment architecture
  * Consider update frequency when deciding on system design and deployment
  * Consider information needs when designing telemetry and relevant parts of the system
  * Consider privacy requirements when deciding where and when to training and deployment the system and how to collect telemetry
  * Consider system requirements when selecting modeling techniques (revisit ML tradeoff lecture)
  * Consider the design and operating costs of different alternative designs
* Deploying inference services as microservices; model evolution
* Composing complex systems with ML and non-ML components: case study Apollo self-driving cars
* Architectural patterns and design patterns for ML

Learning goals:

* Understand important quality considerations when using ML components
* Follow a design process to explicitly reason about alternative designs and their quality tradeoffs
* Gather data to make informed decisions about what ML technique to use and where and how to deploy it
* Critique the decision of where an AI model lives (e.g., cloud vs edge vs hybrid), considering the relevant tradeoffs
* Deliberate how and when to update models and how to collect telemetry
* Create an architectural model describing the relevant characteristics to reason about update frequency and costs
* Critique the decision of where an AI model lives (e.g., cloud vs edge vs hybrid), considering the relevant tradeoffs 

Assignment:

* Design and justify a system architecture for a given scenario, considering computing and network resources

References:

* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapter 13 (Where Intelligence Lives)

* 🗎 Yokoyama, Haruki. "Machine learning system architectural pattern for improving operational stability." In *2019 IEEE International Conference on Software Architecture Companion (ICSA-C)*, pp. 267-274. IEEE, 2019.

* 📰 Daniel Smith. "[Exploring Development Patterns in Data Science](https://www.theorylane.com/2017/10/20/some-development-patterns-in-data-science/)." TheoryLane Blog Post. 2017.

* 🗎 Hazelwood, Kim, Sarah Bird, David Brooks, Soumith Chintala, Utku Diril, Dmytro Dzhulgakov, Mohamed Fawzy et al. "[Applied machine learning at facebook: A datacenter infrastructure perspective](https://research.fb.com/wp-content/uploads/2017/12/hpca-2018-facebook.pdf)." In *2018 IEEE International Symposium on High Performance Computer Architecture (HPCA)*, pp. 620-629. IEEE, 2018.

* 🗎 Peng, Zi, Jinqiu Yang, Tse-Hsun Chen, and Lei Ma. "A first look at the integration of machine learning models in complex autonomous driving systems: a case study on Apollo." In *Proceedings of the 28th ACM Joint Meeting on European Software Engineering Conference and Symposium on the Foundations of Software Engineering*, pp. 1240-1250. 2020.

  



## Lecture: Data Quality ![Quality Assurance](https://img.shields.io/badge/-Quality%20Assurance-orange.svg)

Overview:

* Overview of complexities in data acquisition, data cleaning, and feature extraction steps, both in training and in production
* The tradeoff between more data vs better data in machine learning and the role of random vs systematic data errors
* Overview of common data quality problems
* *Data schema* enforcement, consistency rules, and unit testing for data; tools for defining and checking schemas and constraints (e.g., databases, xml, Avro, Great Expectations, ...)
* Using ML to detect quality problems, inconsistencies, rules; discovery of rules and probabilistic repair (e.g., HoloClean)
* Separating different notions and sources of *drift*; comparing data distributions and detecting data drift; overview of solutions of handling drift in ML systems

Learning goals:

* Describe common data cleaning steps and their purpose and risks
* Design and implement automated quality assurance steps that check data schema conformance and distributions 
* Devise comparison strategies and thresholds for detecting drift
* Understanding the better data vs more data tradeoffs

Assignments:

* As part of group project: Perform basic data quality checks, at least schema enforcement

References:

* Sambasivan, Nithya, Shivani Kapania, Hannah Highfill, Diana Akrong, Praveen Paritosh, and Lora M. Aroyo. "[“Everyone wants to do the model
work, not the data work”: Data Cascades in High-Stakes AI](https://dl.acm.org/doi/abs/10.1145/3411764.3445518)". In Proceedings of the 2021 CHI Conference on Human Factors in Computing Systems, pp. 1-15. 2021.
* 🗎 Schelter, S., Lange, D., Schmidt, P., Celikel, M., Biessmann, F. and Grafberger, A., 2018. [Automating large-scale data quality verification](http://www.vldb.org/pvldb/vol11/p1781-schelter.pdf). Proceedings of the VLDB Endowment, 11(12), pp.1781-1794.
* 🗎 Polyzotis, Neoklis, Martin Zinkevich, Sudip Roy, Eric Breck, and Steven Whang. "[Data validation for machine learning](https://mlsys.org/Conferences/2019/doc/2019/167.pdf)." *Proceedings of Machine Learning and Systems* 1 (2019): 334-347.
* 🗎 Rahimi, Mona, Jin LC Guo, Sahar Kokaly, and Marsha Chechik. "[Toward Requirements Specification for Machine-Learned Components](https://ieeexplore.ieee.org/document/8933771)." In 2019 IEEE 27th International Requirements Engineering Conference Workshops (REW), pp. 241-244. IEEE, 2019.
* 🗎 Polyzotis, Neoklis, Sudip Roy, Steven Euijong Whang, and Martin Zinkevich. 2017. “[Data Management Challenges in Production Machine Learning](https://dl.acm.org/doi/pdf/10.1145/3035918.3054782).” In Proceedings of the 2017 ACM International Conference on Management of Data, 1723–26. ACM.

(possible excursion for data debugging possible here, e.g. techniques to find influential instances or the [Training Set Debugging Using Trusted Items](https://arxiv.org/pdf/1801.08019.pdf) paper)

## Lecture: Infrastructure Quality, Deployment, and Operations ![Implementation/Operations](https://img.shields.io/badge/-Implementation/Operations-yellow.svg) ![QA](https://img.shields.io/badge/-Quality%20Assurance-orange.svg)

Overview:

* Overview of common problems in ML pipelines, including “silent” problems
* Testing all parts of the ML-pipeline; code reviews
* Overview of robustness testing with stubs, fire drills, chaos engineering
* Test automation with *Continuous Integration* tools
* Introduction to DevOps and Continuous Deployment
  * Containers, configuration management, monitoring
  * *Canary releases* and rolling releases
* Overview of MLOps


Learning goals:

* Implement and automate tests for all parts of the ML pipeline
* Understand testing opportunities beyond functional correctness
* Test whether the infrastructure is robust to various kinds of problems
* Automate test execution with continuous integration
* Deploy a service for models using container infrastructure
* Automate common configuration management tasks
* Devise a monitoring strategy and suggest suitable components for implementing it
* Diagnose common operations problems
* Understand the typical concerns and concepts of MLOps

Assignment:

* Part of group project: Design a pipeline to build, evaluate, and serve models that (a) performs automated tests offline, (b) enables experimentation, (c) detects and reports data quality issues and data drift, and (d) provides a monitoring dashboard and sends alerts


Reading:

* 🗎 Eric Breck, Shanqing Cai, Eric Nielsen, Michael Salib, D. Sculley. The ML Test Score: A Rubric for ML Production Readiness and Technical Debt Reduction. Proceedings of IEEE Big Data (2017)
* 📰 Zinkevich, Martin. [Rules of Machine Learning: Best Practices for ML Engineering](https://developers.google.com/machine-learning/guides/rules-of-ml/). Google Blog Post, 2017
* 🗎 Serban, Alex, Koen van der Blom, Holger Hoos, and Joost Visser. "[Adoption and Effects of Software Engineering Best Practices in Machine Learning](https://arxiv.org/pdf/2007.14130)." In Proc. ACM/IEEE International Symposium on Empirical Software Engineering and Measurement (2020).
* 🗎 O'Leary, Katie, and Makoto Uchida. "[Common problems with Creating Machine Learning Pipelines from Existing Code](https://research.google/pubs/pub48984.pdf)." Proc. Third Conference on Machine Learning and Systems (MLSys) (2020).
* 📰 Larysa Visengeriyeva. [Machine Learning Operations - A Reading List](https://ml-ops.org/content/references.html), InnoQ 2020

(could be two lectures if going deeper into DevOps and MLOps)



## Lecture: Managing and Processing Large Datasets ![Architecture](https://img.shields.io/badge/-Architecture-blue.svg) ![Implementation/Operations](https://img.shields.io/badge/-Implementation/Operations-yellow.svg)

Overview:

* Illustrate the need for operating at massive scale in some systems, both for learning, inference, and telemetry; need for distributed data storage and computing
* Distributed data storage strategies and their tradeoffs
* Common patterns for distributed data processing: batch processing, stream processing, and the lambda architecture
* Event sourcing (immutable data) and related design tradeoffs 
* Brief introduction to challenges of distributed systems
* Brief overview of performance analysis and planning
* Excursion: Distributed deep learning 

Learning goals:

* Organize different data management solutions and their tradeoffs
* Understand the scalability challenges involved in large-scale machine learning and specifically deep learning
* Explain the tradeoffs between batch processing and stream processing and the lambda architecture
* Recommend and justify a design and corresponding technologies for a given system
* Outline how machine learning can be parallelized
* Explain the challenges of distributed systems

References:

* 🕮 Martin Kleppmann. [Designing Data-Intensive Applications](https://cmu.primo.exlibrisgroup.com/discovery/fulldisplay?docid=alma991019578119704436&context=L&vid=01CMU_INST:01CMU&search_scope=MyInst_and_CI&tab=Everything&lang=en). O’Reilly, 2017

* 🕮 Nathan Marz and James Warren. "Big Data: Principles and Best Practices of Scalable Realtime Data Systems." Manning, 2015.

* 🗎 Li, Mu, David G. Andersen, Jun Woo Park, Alexander J. Smola, Amr Ahmed, Vanja Josifovski, James Long, Eugene J. Shekita, and Bor-Yiing Su. "Scaling distributed machine learning with the parameter server." In *11th USENIX Symposium on Operating Systems Design and Implementation (OSDI)*, pp. 583-598. 2014.

  

## Lecture: Process and Technical Debt ![Process](https://img.shields.io/badge/-Process-grey.svg)

Overview:

* Overview of common data science workflows (e.g., CRISP-DM)
  * Importance of iteration and experimentation
  * Role of computational notebooks in supporting data science workflows
* Overview of software engineering processes and lifecycles: costs and benefits of process, common process models, role of iteration and experimentation
* Contrasting data science and software engineering processes, goals and conflicts
* Integrating data science and software engineering workflows in process model for engineering AI-enabled systems with ML and non-ML components; contrasting different kinds of AI-enabled systems with data science trajectories
* Overview of technical debt as metaphor for process management; common sources of technical debt in AI-enabled systems

Learning goals:

- Contrast development processes of software engineers and data scientists
- Outline process conflicts between different roles and suggest ways to mitigate them
- Recognize the importance of process
- Describe common agile practices and their goals
- Plan the process for developing AI-enabled systems following different data science trajectories
- Understand and correctly use the metaphor of technical debt
- Describe how ML can incur reckless and inadvertent technical debt, outline common sources of technical debt

References:

* 🗎 Sculley, David, Gary Holt, Daniel Golovin, Eugene Davydov, Todd Phillips, Dietmar Ebner, Vinay Chaudhary, Michael Young, Jean-Francois Crespo, and Dan Dennison. "[Hidden technical debt in machine learning systems](http://papers.nips.cc/paper/5656-hidden-technical-debt-in-machine-learning-systems.pdf)." In Advances in neural information processing systems, pp. 2503-2511. 2015.
* 🗎 Studer, Stefan, Thanh Binh Bui, Christian Drescher, Alexander Hanuschkin, Ludwig Winkler, Steven Peters, and Klaus-Robert Mueller. "[Towards CRISP-ML (Q): A Machine Learning Process Model with Quality Assurance Methodology](https://arxiv.org/abs/2003.05155)." arXiv preprint arXiv:2003.05155 (2020).
* 🗎 Martínez-Plumed, Fernando, Lidia Contreras-Ochando, Cesar Ferri, José Hernández Orallo, Meelis Kull, Nicolas Lachiche, Maréa José Ramírez Quintana, and Peter A. Flach. "[CRISP-DM Twenty Years Later: From Data Mining Processes to Data Science Trajectories](https://research-information.bris.ac.uk/files/220614618/TKDE_Data_Science_Trajectories_PF.pdf)." IEEE Transactions on Knowledge and Data Engineering (2019).
* 🗎 Patel, Kayur, James Fogarty, James A. Landay, and Beverly Harrison. "[Investigating statistical machine learning as a tool for software development](http://www.kayur.org/papers/chi2008.pdf)." In Proceedings of the SIGCHI Conference on Human Factors in Computing Systems, pp. 667-676. 2008.
* 🗎 Yang, Qian, Jina Suh, Nan-Chen Chen, and Gonzalo Ramos. "[Grounding interactive machine learning tool design in how non-experts actually build models](http://www.audentia-gestion.fr/MICROSOFT/Machine_Teaching_DIS_18.pdf)." In *Proceedings of the 2018 Designing Interactive Systems Conference*, pp. 573-584. 2018.
* 📰 Fowler and Highsmith. [The Agile Manifesto](http://agilemanifesto.org/)
* 🕮 Steve McConnell. Software project survival guide. Chapter 3
* 🕮 Pfleeger and Atlee. Software Engineering: Theory and Practice. Chapter 2
* 🗎 Kruchten, Philippe, Robert L. Nord, and Ipek Ozkaya. "[Technical debt: From metaphor to theory and practice](https://resources.sei.cmu.edu/asset_files/WhitePaper/2012_019_001_58818.pdf)." IEEE Software 29, no. 6 (2012): 18-21.

Blog post/lecture notes:

* [On the process for building software with ML components](https://ckaestne.medium.com/on-the-process-for-building-software-with-ml-components-c54bdb86db24)



## Lecture: Human AI Interaction ![Requirements](https://img.shields.io/badge/-Requirements-green.svg)![Implementation/Operations](https://img.shields.io/badge/-Implementation/Operations-yellow.svg)

Overview:

* High-level overview of design space: automation degree, forcefulness, transparency, …
* Overview of usability
* Aligning mental models
* Building trust in AI-enabled systems (transparency, setting expectations, mental models, explanations, …)
* AI-design guidelines

Learning goals:

​	tbd.

References:

* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 5 (Components of Intelligent Systems) and Chapter 7.
* 🗎 Yang, Qian. "[The role of design in creating machine-learning-enhanced user experience](https://www.aaai.org/ocs/index.php/SSS/SSS17/paper/viewPaper/15363)." In *2017 AAAI Spring Symposium Series*. 2017.
* 🗎 Amershi, Saleema, Dan Weld, Mihaela Vorvoreanu, Adam Fourney, Besmira Nushi, Penny Collisson, Jina Suh et al. "[Guidelines for Human-AI Interaction](https://www.microsoft.com/en-us/research/uploads/prod/2019/01/Guidelines-for-Human-AI-Interaction-camera-ready.pdf)." In *Proceedings of the 2019 CHI conference on human factors in computing systems*, pp. 1-13. 2019.
* 🗎 Kocielnik, Rafal, Saleema Amershi, and Paul N. Bennett. "[Will you accept an imperfect AI? Exploring designs for adjusting end-user expectations of AI systems](http://library.usc.edu.ph/ACM/CHI2019/1proc/paper411.pdf)." In *Proceedings of the 2019 CHI Conference on Human Factors in Computing Systems*, pp. 1-14. 2019.
* 🗎 Kulesza, Todd, Margaret Burnett, Weng-Keen Wong, and Simone Stumpf. "Principles of explanatory debugging to personalize interactive machine learning." In *Proceedings of the 20th international conference on intelligent user interfaces*, pp. 126-137. 2015.
* 🗎 Cai, Carrie J., Samantha Winter, David Steiner, Lauren Wilcox, and Michael Terry. "[’Hello AI’: Uncovering the Onboarding Needs of Medical Practitioners for Human-AI Collaborative Decision-Making](https://dl.acm.org/doi/abs/10.1145/3359206)." *Proceedings of the ACM on Human-Computer Interaction* 3, no. CSCW (2019): 1-24.

## Lecture: Ethics + Fairness (3 lectures) ![Requirements](https://img.shields.io/badge/-Requirements-green.svg) ![Quality Assurance](https://img.shields.io/badge/-Quality%20Assurance-orange.svg) 

Overview:

* Introductions to ethics and responsible AI
  * Moral vs ethical vs legal
  * Safety concerns, broadly
  * Discrimination (harms of allocation and representation)
  * Algorithmic transparency and explainability
  * Security and privacy
  * Reproducibility and accountability
  * Amplification through feedback loops
* Fairness concepts, legal and practical definitions 
* Common sources of bias in machine learning
* Fairness at the model level: fairness measures (anti-classification, separation, independence), fairness testing, interventions, and their tradeoffs
* Fairness beyond the model: requirements engineering, dataset construction, monitoring and auditing, checklists, process integration and enforcement 

Learning goals:

* Review the importance of ethical considerations in designing AI-enabled systems
* Recall basic strategies to reason about ethical challenges
* Diagnose potential ethical issues in a given system
* Understand the types of harm that can be caused by ML
* Understand the sources of bias in ML
* Design and execute tests to check for bias/fairness issues
* Evaluate and apply mitigation strategies
* Consider achieving fairness in AI-based systems as an activity throughout the entire development cycle
* Understand the role of requirements engineering in selecting ML fairness criteria
* Understand the process of constructing datasets for fairness
* Consider the potential impact of feedback loops on AI-based systems and need for continuous monitoring

Assignment:

* Analyze a given component for potential bias, design a mitigation, and deploy automated tests 

References:

* 🗎 Robyn Caplan, Joan Donovan, Lauren Hanson, Jeanna Matthews. [Algorithmic Accountability: A Primer.](https://datasociety.net/wp-content/uploads/2018/04/Data_Society_Algorithmic_Accountability_Primer_FINAL-4.pdf) Data & Society (2018)
* 📰 Max Tegmark. [Benefits and Risks of Artificial Intelligence](https://futureoflife.org/background/benefits-risks-of-artificial-intelligence/?cn-reloaded=1). Future of Life Institute
* 📰 Julia Angwin, Jeff Larson, Surya Mattu and Lauren Kirchner. [Machine Bias](https://www.propublica.org/article/machine-bias-risk-assessments-in-criminal-sentencing). Propublica 2016
* 🗎 Corbett-Davies, Sam, and Sharad Goel. "[The measure and mismeasure of fairness: A critical review of fair machine learning](https://arxiv.org/abs/1808.00023)." arXiv preprint arXiv:1808.00023 (2018).
* 🗎 Holstein, Kenneth, Jennifer Wortman Vaughan, Hal Daumé III, Miro Dudik, and Hanna Wallach. "[Improving fairness in machine learning systems: What do industry practitioners need?](http://users.umiacs.umd.edu/~hal/docs/daume19fairness.pdf)" In *Proceedings of the 2019 CHI Conference on Human Factors in Computing Systems*, pp. 1-16. 2019.
* 🗎 Madaio, Michael A., Luke Stark, Jennifer Wortman Vaughan, and Hanna Wallach. "[Co-Designing Checklists to Understand Organizational Challenges and Opportunities around Fairness in AI](http://www.jennwv.com/papers/checklists.pdf)." In Proceedings of the 2020 CHI Conference on Human Factors in Computing Systems, pp. 1-14. 2020.
* 🗎 Bietti, Elettra. "[From ethics washing to ethics bashing: a view on tech ethics from within moral philosophy](https://dl.acm.org/doi/pdf/10.1145/3351095.3372860)." In *Proceedings of the 2020 Conference on Fairness, Accountability, and Transparency*, pp. 210-219. 2020.
* 🗎 Binns, Reuben. "[Fairness in machine learning: Lessons from political philosophy](http://proceedings.mlr.press/v81/binns18a/binns18a.pdf)." In *Conference on Fairness, Accountability and Transparency*, pp. 149-159. PMLR, 2018.
* 🗎 Keyes, O., Hutson, J., & Durbin, M. (2019, May). [A mulching proposal: Analysing and improving an algorithmic system for turning the elderly into high-nutrient slurry](https://arxiv.org/pdf/1908.06166). In *Extended Abstracts of the 2019 CHI Conference on Human Factors in Computing Systems* (pp. 1-11).



## Lecture: Transparency, Interpretability, and Explainability (2 lectures) ![Requirements](https://img.shields.io/badge/-Requirements-green.svg) ![Machine Learning](https://img.shields.io/badge/-Debugging-Purple.svg)

Overview:

* Introduction to use cases, concepts, and measures for interpretability
* Inherent interpretability of different ML models vs retrofitting explanations
* Various approaches to provide explanations for black-box models, including local and global surrogates, feature importance, invariants, counterfactuals, prototypes, and influential instances
* Discussion of trustworthiness of post-hoc explanations and involved tradeoffs
* Algorithmic transparency: arguments, benefits, drawbacks, perceptions
* Interface design for explanations and influences on human-AI interactions (e.g., building mental models; trust and too much trust)
* Discussion on regulation and policy around responsible AI

Learning goals:

- Understand the importance of and use cases for interpretability
- Explain the tradeoffs between inherently interpretable models and post-hoc explanations
- Measure interpretability of a model
- Select and apply techniques to debug/provide explanations for data, models and model predictions
- Evaluate when to use interpretable models rather than ex-post explanations

References:

* 🗎 Rudin, Cynthia. "[Stop explaining black box machine learning models for high stakes decisions and use interpretable models instead](https://arxiv.org/abs/1811.10154)." Nature Machine Intelligence 1, no. 5 (2019): 206-215.
* 🎧 Data Skeptic Podcast Episode “[Black Boxes are not Required](https://dataskeptic.com/blog/episodes/2020/black-boxes-are-not-required)” with Cynthia Rudin (32min)
* 🕮 Christoph Molnar. "[Interpretable Machine Learning: A Guide for Making Black Box Models Explainable](https://christophm.github.io/interpretable-ml-book/)." 2019
* 🗎 Bhatt, Umang, Alice Xiang, Shubham Sharma, Adrian Weller, Ankur Taly, Yunhan Jia, Joydeep Ghosh, Ruchir Puri, José MF Moura, and Peter Eckersley. "Explainable machine learning in deployment." In Proceedings of the 2020 Conference on Fairness, Accountability, and Transparency, pp. 648-657. 2020.
* 🗎 Eslami, Motahhare, Aimee Rickman, Kristen Vaccaro, Amirhossein Aleyasen, Andy Vuong, Karrie Karahalios, Kevin Hamilton, and Christian Sandvig. [I always assumed that I wasn't really that close to her: Reasoning about Invisible Algorithms in News Feeds](http://eslamim2.web.engr.illinois.edu/publications/Eslami_Algorithms_CHI15.pdf). In Proceedings of the 33rd annual ACM conference on human factors in computing systems, pp. 153-162. ACM, 2015.
* 🗎 Stumpf, Simone, Adrian Bussone, and Dympna O’sullivan. "[Explanations considered harmful? user interactions with machine learning systems](http://www.doc.gold.ac.uk/~mas02mg/HCML2016/HCML2016_paper_2.pdf)." In *Proceedings of the ACM SIGCHI Conference on Human Factors in Computing Systems (CHI)*. 2016.
* 🗎 Kulesza, Todd, Margaret Burnett, Weng-Keen Wong, and Simone Stumpf. "Principles of explanatory debugging to personalize interactive machine learning." In *Proceedings of the 20th international conference on intelligent user interfaces*, pp. 126-137. 2015.

(possibly go further in debugging here or next lecture, independent of explainability)

## Lecture: Versioning, Provenance, and Reproducibility ![Requirements](https://img.shields.io/badge/-Requirements-green.svg) ![Implementation/Operations](https://img.shields.io/badge/-Implementation/Operations-yellow.svg) ![Quality Assurance](https://img.shields.io/badge/-Quality%20Assurance-orange.svg)

Overview:

* Challenge of reproducing data, models, and decisions, especially in complex systems
* Documenting and tracking data provenance (modeling), "visibility debt", techniques for automated tracking
* Versioning of code, data, and models
* Curbing nondeterminism in ML pipelines
* Logging and audit traces
* Overview of corresponding MLOps tools like DVC, ModelDB, and MLFlow

Learning goals:

* Judge the importance of data provenance, reproducibility and explainability for a given system
* Create documentation for data dependencies and provenance in a given system
* Propose versioning strategies for data and models
* Test systems for reproducibility

References:

* 🗎 Halevy, Alon, Flip Korn, Natalya F. Noy, Christopher Olston, Neoklis Polyzotis, Sudip Roy, and Steven Euijong Whang. "Goods: Organizing google's datasets." In Proceedings of the 2016 International Conference on Management of Data, pp. 795-806. ACM, 2016.
* 🗎 Gulzar, Muhammad Ali, Matteo Interlandi, Tyson Condie, and Miryung Kim. "Debugging big data analytics in spark with bigdebug." In Proceedings of the 2017 ACM International Conference on Management of Data, pp. 1627-1630. ACM, 2017.
* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapter 21 (Organizing Intelligence) – 23 (Orchestration)
* 🗎 Sugimura, Peter, and Florian Hartl. "Building a Reproducible Machine Learning Pipeline." *arXiv preprint arXiv:1810.04570* (2018).





## Lecture: Security and Privacy ![Requirements](https://img.shields.io/badge/-Requirements-green.svg) ![Quality Assurance](https://img.shields.io/badge/-Quality%20Assurance-orange.svg) ![Process](https://img.shields.io/badge/-Process-grey.svg)

Overview:

* Introduction to security: Confidentiality, integrity, and availability
* Security and privacy at the model level
  * Attack scenarios against AI components and possible defenses
  * Poisoning attacks
  * Evasion attacks
  * Adversarial examples and model hardening
  * Model inversion attacks
  * Generative adversarial networks
  * Federated learning
* Security and privacy at the system level
  * Requirements and risk analysis
  * Threat modeling
  * Defense strategies outside the model, including trust mechanisms
  * Designing for security, least privilege, isolation
  * Anomaly detection
* Basics of adversarial learning techniques
* Feedback loops and how to detect them
* Dangers of leaking sensitive data, deanonymization, and *differential privacy*
* *Threat modeling*
* Overview of common security patterns/tactics
* Anomaly detection, intrusion detection

Learning goals:

* Explain key concerns in security (in general and with regard to ML models)
* Analyze a system with regard to attacker goals, attack surface, attacker capabilities
* Describe common attacks against AI component 
* Conduct threat modeling for a given system and derive security requirements
* Suggest counter measures against attacks for specific systems, both at the model and at the system level
* Discuss challenges in anonymizing data 
* Apply key design principles for secure system design

Reading:

* 🕮 Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapter 25 (Adversaries and Abuse)

* 🗎 G. McGraw et al., *The Top 10 Risks of Machine Learning Security*, IEEE Computer (2020)

* 🗎 McGraw, Gary, Harold Figueroa, Victor Shepardson, and Richie Bonett. "[An architectural risk analysis of machine learning systems: Toward more secure machine learning](https://berryvilleiml.com/docs/ara.pdf)." Technical report, Berryville Institute of Machine Learning, v 1.0 (2020).

* 🗎 Shawn Hernan and Scott Lambert and Tomasz Ostwald and Adam Shostack. [Uncover Security Design Flaws Using The STRIDE Approach](https://github.com/ckaestne/seai/raw/F2019/other_material/readings/security/msnd_threatmodeling.pdf). MSDN 2007

* 🕮 Agrawal, A., Gans, J., & Goldfarb, A. (2018). [*Prediction machines: the simple economics of artificial intelligence*](https://cmu.primo.exlibrisgroup.com/permalink/01CMU_INST/6lpsnm/alma991019698987304436). Harvard Business Press. Chapter 19 (Managing AI Risk)

* 🗎 Goodfellow, I., McDaniel, P., & Papernot, N. (2018). [Making machine learning robust against adversarial inputs](https://par.nsf.gov/servlets/purl/10111674). *Communications of the ACM*, *61*(7), 56-66. 

* 🗎 Huang, L., Joseph, A. D., Nelson, B., Rubinstein, B. I., & Tygar, J. D. (2011, October). [Adversarial machine learning](http://www.blaine-nelson.com/research/pubs/Huang-Joseph-AISec-2011.pdf). In *Proceedings of the 4th ACM workshop on Security and artificial intelligence* (pp. 43-58). 

  

## Lecture: Safety and Robustness (2 lectures) ![Requirements](https://img.shields.io/badge/-Requirements-green.svg) ![Architecture/Design](https://img.shields.io/badge/-Architecture/Design-blue.svg) ![Quality Assurance](https://img.shields.io/badge/-Quality%20Assurance-orange.svg) 

Overview:

* Introduction to safety and ethics; safety vs reliability; safety beyond traditional safety-critical systems
* Revisiting risk and requirements analysis (fault trees, FMEA, HAZOP)
* Robustness analysis and limitations of robustness for assessing safety
* Architectural safety tactics -- how to build safe systems from unreliable components
* Layers of safety engineering: safe practices, safety culture, safety regulation
* Introduction to assurance cases and software certification; evidence collection for safety claims

Learning goals:

* Understand safety concerns in traditional and AI-enabled systems
* Summarize the state of the art robustness analysis strategies for machine-learned models
* Perform a hazard analysis for a system to derive safety requirements
* Diagnose potential safety issues in a given system
* Collect evidence and sketch an argument for a safety case
* Design architectural safeguards against safety-relevant mistakes from AI components
* Describe the typical processes for safety evaluations and their limitations

Assignment: (?)

* Perform a hazard analysis of a given system, identify suitable mitigations, and sketch an argument for a safety case

References:

* 🗎 Borg, Markus, Cristofer Englund, Krzysztof Wnuk, Boris Duran, Christoffer Levandowski, Shenjian Gao, Yanwen Tan, Henrik Kaijser, Henrik Lönn, and Jonas Törnqvist. "[Safely entering the deep: A review of verification and validation for machine learning and a challenge elicitation in the automotive industry](https://www.atlantis-press.com/journals/jase/125905766)." Journal of Automotive Software Engineering. Volume 1, Issue 1, Pages 1 - 19. 2019
* 🗎 Cohen, Jeremy M., Elan Rosenfeld, and J. Zico Kolter. "[Certified adversarial robustness via randomized smoothing](https://arxiv.org/abs/1902.02918)." In Proc. International Conference on Machine Learning, p. 1310--1320, 2019.
* 🗎 Salay, Rick, Rodrigo Queiroz, and Krzysztof Czarnecki. "[An analysis of ISO 26262: Using machine learning safely in automotive software (Links to an external site.)](https://arxiv.org/pdf/1709.02435)." *arXiv preprint arXiv:1709.02435* (2017).
* 🗎 Wiens, Jenna, Suchi Saria, Mark Sendak, Marzyeh Ghassemi, Vincent X. Liu, Finale Doshi-Velez, Kenneth Jung et al. "[Do no harm: a roadmap for responsible machine learning for health care](http://www.regenhealthsolutions.info/wp-content/uploads/2019/08/Do-no-harm-a-roadmap-for-responsible-machine.pdf)." *Nature medicine* 25, no. 9 (2019): 1337-1340.
* 🗎 Shneiderman, Ben. "Bridging the gap between ethics and practice: Guidelines for reliable, safe, and trustworthy Human-Centered AI systems." *ACM Transactions on Interactive Intelligent Systems (TiiS)* 10, no. 4 (2020): 1-31.



## Lecture: Fostering Interdisciplinary Teams ![Process](https://img.shields.io/badge/-Process-grey.svg)

Overview:

* Different roles in developing AI-enabled systems and their respective goals and concerns
* The importance of interdisciplinary teams; unicorns
* Collaboration points in building AI-enabled systems; revisiting process considerations and data science trajectories
* Communication costs in teams, team composition, and socio-technical congruence
* Managing conflicting goals: team organization, agile practices, DevOps, T-shaped people
* Overcoming groupthink: hype, diversity, culture, agile practices
* Mitigating social loafing: responsibilities, motivation, agile practices
* Discussion on the future of software engineering for AI-enabled systems
  * The role of ML to automate software engineering tasks
  * The role of AutoML to automate data science tasks
  * Empowering team members & responsible engineering

Learning goals:

* Understand different roles in projects for AI-enabled systems
* Plan development activities in an inclusive fashion for participants in different roles
* Diagnose and address common teamwork issues
* Describe agile techniques to address common process and communication issues

References:

* 🗎 Kim, M., Zimmermann, T., DeLine, R., & Begel, A. (2017). [Data scientists in software teams: State of the art and challenges (Links to an external site.)](https://andrewbegel.com/papers/data-scientists.pdf ). *IEEE Transactions on Software Engineering*, *44*(11), 1024-1038.
* 🗎 Yang, Qian, Jina Suh, Nan-Chen Chen, and Gonzalo Ramos. "[Grounding interactive machine learning tool design in how non-experts actually build models](http://www.audentia-gestion.fr/MICROSOFT/Machine_Teaching_DIS_18.pdf)." In *Proceedings of the 2018 Designing Interactive Systems Conference*, pp. 573-584. 2018.
* 🗎 Wang, Dakuo, Justin D. Weisz, Michael Muller, Parikshit Ram, Werner Geyer, Casey Dugan, Yla Tausczik, Horst Samulowitz, and Alexander Gray. "[Human-AI Collaboration in Data Science: Exploring Data Scientists' Perceptions of Automated AI](https://www.researchgate.net/profile/Michael_Muller/publication/335703274_Human-AI_Collaboration_in_Data_Science_Exploring_Data_Scientists'_Perceptions_of_Automated_AI/links/5d76a0294585151ee4ab0338/Human-AI-Collaboration-in-Data-Science-Exploring-Data-Scientists-Perceptions-of-Automated-AI.pdf)." Proceedings of the ACM on Human-Computer Interaction 3, no. CSCW (2019): 1-24.

