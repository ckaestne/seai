# Individual Assignment 1: Building an ML-enabled Product

(17-445/17-645/17-745 Machine Learning in Production)

## Overview

In this assignment, you will enhance an existing product with a new feature powered by machine learning. Building a system with an ML component requires more than training a model. While sometimes central to the system, the ML component is typically just one part among many in a larger system. 

Learning goals:
* Demonstrate familiarity with programming skills necessary for this course
* Understand the scope of software engineering challenges when building an production system with ML components
* Identify technical and nontechnical challenges 
* Discuss user interface design decisions and risks introduce with the ML component

**A word on scope and difficulty.** In this assignment you will work with an existing nontrivial code base of a web application. It involves several technologies, tools, and libraries like the *pip* dependency manager, *HTML*, *REST APIs*, databases, object relational mappers, and the *flask* library many of which will not be familiar to many students. We expect some basic programming skills as a prerequisite for this course but do not assume that you are already familiar with all these technologies and tools. Nonetheless, we will not teach those technologies but expect that you can learn enough by yourself by reading documentation or tutorials as needed to perform small changes. You will most likely not need to understand all technologies in detail, just enough to navigate the code base and make small changes. Documentation for many of these technologies is mature and has good examples. The final submission may only modify or introduce a few lines of code in the end, but identifying how to make those changes may take quite some exploration and learning. -- *This is intentional*. Professional developers and data scientists will constantly learn new technologies, including many that do not exist today, without having a lecture or recitation to cover exactly what is needed for the task. Incrementally modifying and maintaining existing systems is far more common than developing new things from scratch. Learning new technologies, libraries and tools and troubleshooting problems with documentation, debugging, and sites like Stackoverflow are important skills and a prerequisite to be successful in this class, especially in the team project.

Beyond that, this assignment is intentionally *open ended*. We provide some recommendations for technologies to use but you are free to use others. We make minimum requirements for an implementation that can be implemented with under 20 lines of code. You can receive full credit for such a minimal implementation with remaining obvious problems if you identify in the discussion what the problems are and how you would do things differently if you had more time. At the same time, we welcome you to explore better solutions that exceed the minimum requirements to build a better product. 

## Context: Accessibility with Alternative Image Text

Web standards like HTML and most markup languages have had accessibility features to provide *[alternative text](https://en.wikipedia.org/wiki/Alt_attribute)* for images since very early versions (e.g., HTML 1.2 in 1993). Alternative text may not be shown by default the in the browser, but they can convey information to visually impaired users using screen readers or users with very limited bandwidth that prefer not to transfer image files. There is lots of guidance how to provide good alternative text (e.g., [Wikipedia's style guide](https://en.wikipedia.org/wiki/Wikipedia:Manual_of_Style/Accessibility/Alternative_text_for_images)). In practice though, alternative text is often missing or of low quality. For example, Twitter recently introduced the option for authors to provide alternative text for images, but only few users use it.

As with many accessibility features, investment in accessibility is also beneficial to users without a disability. For example, alternative text is also accessible to traditional search engines, which may help to find pictures that were not explicitly labeled. 

## Task

In this assignment, you will use advances in machine learning for vision problems to improve accessibility in an open source project by providing alternative text on images. We suggest that you extend [albumy](https://github.com/greyli/albumy) (while we strongly recommend to extend *albumy*,  you are free to chose a different open source project in any language you prefer. However, we will likely not be able to answer questions well about other projects or languages.)

*Albumy* is a demo implementation of a minimal Instagram clone in Python (created as example for a book on the *flask* library for Python). Users can create accounts and upload and share images, describe and tag images, and comment on images. While *albumy* is not a polished end-user product, it is a reasonable stand-in for a software product that may be used by end users while still having a reasonably small codebase. *Albumy* does not currently use machine learning for any of its functionality.

**Introduce ML-powered features.** Change the open source project to introduce at a minimum the following accessibility feature:
*Alternative text generation:* Provide an automatically generated alternative text for images if users do not provide their own. In *albumy* you can use the existing description field or add a new mechanism to store the alternative text.
You can use any existing ML models as part of your implementation, research or free or paid, remote APIs or local pretrained models. We do *not* recommend to train your own model.

**Discuss the feature in the product.** Machine learning contributes a part to a larger application with many non-ML parts and system-level concerns. When designing the feature, think about how you introduce the feature into the existing open source application, whether they change the user interface, and when and how to call the ML models. Also consider whether the used ML models are really suitable for the task at hand and whether you foresee any risks of deploying this feature in its current form and how to make it better. Finally, anticipate engineering issues that might occur if you  wanted to scale the system to support millions of users and daily image uploads. Make sure you are discussing the overall application, not just the ML model. 

Your discussions may reveal limitations of your implementation and make suggestions for improvements. Even if you point out serious flaws in your own implementation, you are not required to implement the improvements if your implementation already meets our minimal requirements.



## Deliverables

See Canvas for instructions of how to create a private repository with GitHub classrom that contains the existing *albumy* implementation (you can change or replace all code in this repository however you like).

Commit all your code changes to your GitHub repository, but *do not commit private credentials*. Update instructions to install and run the system in the `README.md` file as necessary (e.g., explain how to get an API token if needed or add additional libraries to `requirements.txt`). 

Additionally upload a short report to Gradescope by [date see Canvas] with the following content: 

* **GitHub link:** Start the document with a link to your last commit on GitHub: On the GitHub webpage, click on the last commit message and copy the URL in the format `https://github.com/[user]/[repo]/commit/[commitid]`. Make sure that the link includes the long ID of the last commit.
* **Technical description (1 page max):** Briefly describe how you implemented the feature. Provide pointers to the relevant parts of the code, ideally as direct links files or even specific lines on GitHub.
* **User interface design approach (1 page max):** Recommend how the feature should interact with users (automate, prompt, organize, annotate, hybrid) and why. Justify your recommendation, considering forcefulness, frequency, value, and cost. If your implementation differs from the recommended approach, briefly explain how you would change your implementation if you had more time.
* **Risks (1 page max):** Discuss what risks you can anticipate from using machine learning for the feature in the applications. Identify at least one risk and discuss potential solutions to mitigate the risk. (You do not need to implement the solutions.)
* **Production challenges (1 page max):** Discuss any technical challenges you anticipate if you want to deploy this feature in production (e.g., scalability, operating costs) and how you would change your implementation if you expected millions of users. Identify at least one problem and discuss corresponding potential solutions. (You do not need to implement the solutions.)

Make sure your document is clearly structured, such that it is recognizable which answer belongs to which question. Ideally, you answer each question on a separate page, which makes our lives easier for grading. In Gradescope map each question to the corresponding page (see “Assign” in the [Gradescope documentation](https://gradescope-static-assets.s3.amazonaws.com/help/submitting_hw_guide.pdf)).

Page limits are recommendations and not strictly enforced. You can exceed the page limit if there is a good reason. We prefer precise and concise answers over long and rambling ones.


## Grading

**Important:** Please read the grading specifications carefully. Note from the syllabus that we grade each specification below pass/fail. That is, there is no partial credit when not fully meeting all parts of the specification and no extra credit for going beyond the specification. For example, if the document is clearly structured but you do not map questions to the relevant pages in Gradescope, you will lose the full 10 points for the first specification. You can make up for lost points by resubmitting the assignment later, using some of your tokens, as described in the syllabus. The grading specifications should be clear enough that you should be able to evaluate yourself with high confidence whether your solution meets the specification. 

In this, as in all future assignments, we are happy to answer clarification questions about the grading specifications. If you are not sure what is expected of you, please ask.

The assignment is worth 100 points. We will assign credit as follows:

* 10p: The document is clearly structured, such that it is clear which text belongs to which question. The document includes a link to a specific commit in your GitHub repository created with GitHub classroom. When uploading the solution to Gradescope, questions are mapped to the relevant pages.
* 10p: We can install and run your implementation based on the descriptions in the `README.md` file (including instructions for dependencies and API creditials if needed).
* 10p: No private credentials are committed to the GitHub repository, including its history.
* 30p: The document describes how alternative text generation is implemented and we can find the corresponding implementation. A machine-learned model was used in the implementation. The application is functional in that it produces HTML with `alt` tags containing alternative text for all  images uploaded by users (excluding profile pictures), The alternative text is automatically generated by an ML model unless manually specified by users.
* 20p: The document makes a plausible recommendations of how to design the user interaction for the new feature, using the concepts automate, prompt, organize, annotate and hybrid introduced in class. The recommendation is justified and the justification considers forcefulness, frequency, value, and cost. The answer makes clear whether the implementation corresponds to the recommendation and explains needed changes if it does not.
* 10p: The document makes a good faith attempt at discussing possible risks. The discussion focuses on application-level concerns and the user experience. At least one potential risk with the current implementation is identified. At least one potential solution is discussed for each risk. All discussed risks and solutions are plausible in the context of the application.
* 10p: The document makes a good faith attempt at discussing production challenges. The discussion focuses on production issues such as scalability or operation costs. At least one potential problem with the current implementation is identified. At least one potential solution is discussed for each identified problem. All discussed problems and solutions are plausible in the context of the application.

## Technical hints

Current browsers do not usually show the alternative text by default, not even as tool tip. There are several browser plugins and screen readers that can highlight them or you can simply inspect the produced HTML source.

There are many web APIs that provide image captioning features. You will typically have to sign up for an account. Most offer the API for free for a certain number of requests or offer trial periods -- this is sufficient to complete the assignment. Google and Microsoft also offer cloud credits for students that you may use (see Canvas). You can also consider using pretrained models locally. We do not recommend to train your own model, as this would by far exceed the scope of this assignment. When we tested the assignment, we had good experiences with the Azure Computer Vision APIs.

For *albumy*, it is worth to gain a basic understanding of package management in Python with [pip](https://pip.pypa.io/en/stable/getting-started/) and of creating and running web applications that produce HTML pages with [flask](https://flask.palletsprojects.com/en/2.1.x/). If you are unfamiliar with HTML, the most basic tutorials are likely sufficient. The file `blueprints/main.py` contains the entry points for rendering different pages, including those for showing the photo listing, an individual photo, and for uploading photos. Albumy uses an internal database to store objects in a format specified in `models.py` using [SQLAlchemy](https://www.sqlalchemy.org/); those objects are easily extensible without database knowledge. The uploaded files themselves are simply stored in a directory. The files in `templates/main` contain HTML templates used to generate the web pages by flask, where flask simply fills in the parts in double curly braces with the result of the code contained within. There are at least three `<img>` tags in these templates for showing user images without an `alt` tag in the original implementation. Forms in *albumy* are generated with the library [wtforms](https://github.com/wtforms/wtforms) that abstracts from low-level HTML code. 

Public APIs for ML models like Azure's [Vision API](https://docs.microsoft.com/en-us/azure/cognitive-services/computer-vision/quickstarts-sdk/image-analysis-client-library?pivots=programming-language-csharp&tabs=visual-studio) usually have fairly decent documentation and code snippets in multiple languages to illustrate how to use them.

Never commit private credentials (such as API keys) to a public Git repository. A common strategy is to write credentials into a file (e.g., `api.key`), read the key from the file at runtime, add that file to the `.gitignore` file to avoid committing it accidentally, and add instructions to the README of how to obtain a key and how write it into a file. Alternatively it is common to pass API keys as environment variables. If you accidentally commit a key and push this to a public repository, you will need to revoke the key and create a new one; if you have not yet pushed the changes you can go the nontrivial route of [rewriting the git history](https://stackoverflow.com/questions/872565/remove-sensitive-files-and-their-commits-from-git-history). 
