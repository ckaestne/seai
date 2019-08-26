---
author: Christian Kaestner
title: "17-445: Introduction and Motivation"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
---  

# Introduction and Motivation

Christian Kaestner and Eunsuk Kang

---

## Learning Goals

* Explain the typical machine-learning process
* Illustrate the challenges in engineering an AI-enabled system beyond accuracy
* Summarize the respective goals and challenges of software engineers vs data scientists

---

# Case Study: The Transcription Service Startup

----

![competitor](transcription.png)

----

## Transcription services

* Take audio or video files and produce text.
    - Used by academics to analyze interview text
    - Podcast show notes
    - Subtitles for videos

* State of the art: Manual transcription, often mechanical turk (1.5 $/min)

----

## The startup idea

PhD research on domain-specific speech recognition, that can detect technical jargon

DNN trained on public PBS interviews + transfer learning on smaller manually annotated domain-specific corpus

Research has shown amazing accuracy for talks in medicine, poverty and inequality research, and talks at Ruby programming conferences; published at top conferences

Idea: Let's commercialize the software and sell to academics and conference organizers

----

## Likely challenges?

<!-- discussion -->

Notes: Ask students to write at least 3 challenges each, collect answers on board

----
## Data scientist

* Often fixed dataset for training and evaluation (e.g., PBS interviews)
* Focused on accuracy
* Prototyping, often Jupyter notebooks or similar 
* Expert in modeling techniques and feature engineering
* Model size, updateability, implementation stability typically does not matter

<!-- split -->

## Software engineer

* Builds a product
* Concerned about cost, performance, stability, release time
* Identify quality through customer satisfaction
* Must scale solution, handle large amounts of data
* Detect and handle mistakes, preferably automatically
* Maintain, evolve, and extend the product over long periods
* Consider requirements for security, safety, fairness


----

## Likely challenges?

<!-- discussion -->

----

## Qualities of Interest ("ilities")

* Quality is about more than the absence of defects
* Quality in use (effectiveness, efficiency, satisfaction, freedom of risk, ...)
* Product quality (functional correctness and completeness, performance efficiency, compatibility, usability, dependability, scalability, security, maintainability, portability, ...)
* Process quality (manageability, evolvability, predictability, ...)
* 
* "Quality is never an accident; it is always the result of high intention, sincere effort, intelligent direction and skillful execution; it represents the wise choice of many alternatives." (many attributions)

----

## Garvin’s eight categories of product quality

* Performance
* Features
* Reliability
* Conformance
* Durability
* Serviceability
* Aesthetics
* Perceived Quality

<!-- references -->

Reference:
Garvin, David A., [What Does Product Quality Really Mean](http://oqrm.org/English/What_does_product_quality_really_means.pdf). Sloan management review 25 (1984).
----

## Relevant Qualities for Transcription Service?

<!-- discussion -->

----

## Examples for discussion

* What does correctness or accuracy really mean? What accuracy do customers care about?
* How can we see how well we are doing in practice? How much feedback are customers going to give us before they leave?
* Can we estimate how good our transcriptions are?
* How to present results to the customers (including confidence)?
* When customers complain about poor transcriptions, how to prioritize and what to do?
* 
* What are unacceptable mistakes and how can they be avoided?
* How quickly do we detect problems?
* How quickly can we fix mistakes? How?
* Will transcribing the same audio twice produce the same result? Does it matter?

----

## Examples for discussion 2
 
* With more customers, transcriptions are taking longer and longer -- what can we do?
* Transcriptions sometimes crash. What to do?
* How do we achieve high availability?
* How can we see that everything is going fine and page somebody if it is not?
* Tensorflow update; does our infrastructure still work?
* Once somewhat successful, how to handle large amounts of data per day?
* Buy more machines or move to the cloud?
*
* Models are continuously improved. When to deploy? Can we roll back?
* Can we offer live transcription as an app? As a web service?
* Can we get better the longer a person talks? Should we then go back and reanalyze the beginning? Will this benefit the next upload as well?

----

## Examples for discussion 3

* How many domains can be supported? Do we have the server capacity?
* How specific should domains be? Medical vs "International Conference on Allergy & Immunology"?
* How to make it easy to support new domains?
* 
* Can we handle accents? 
* Better recognition of male than female speakers?
* 
* Can and should we learn from customer data? 
* What could be possible privacy problems and how can we avoid them?
* Do we need to worry about security? Where?

----

![Screenshot of Temi transcription service](temi.png)

[Highlights challenging fragments. Can see what users fix inplace to correct. Star rating for feedback.]

---

# Correctness and Specifications

***

# Deductive vs. Inductive Reasoning

----

## Who is to blame?

```java
Algorithms.shortestDistance(g, "Tom", "Anne");

> ArrayOutOfBoundsException
```

```java
Algorithms.shortestDistance(g, "Tom", "Anne");

> -1
```

----

## Who is to blame?

```java
class Algorithms {
    /**
     * This method finds the shortest distance between to 
     * verticies. It returns -1 if the two nodes are not 
     * connected. 
    */
    int shortestDistance(…) {…}
}
```
```java
class Algorithms {
    /**
     * This method finds the shortest distance between to 
     * verticies. Method is only supported 
     * for connected verticies.
    */
    int shortestDistance(…) {…}
}
```

----

## System decomposition with interfaces

```java
/*@ requires amount >= 0;
    ensures balance == \old(balance)-amount &&
            \result == balance;
@*/
public int debit(int amount) {
    ...
}
```
(JML specification in Java, pre- and postconditions)

```java
/**
  * Calls the <code>read(byte[], int, int)</code> overloaded [...]
  * @param buf The buffer to read bytes into
  * @return The value retured from <code>in.read(byte[], int, int)</code>
  * @exception IOException If an error occurs
  */
public int read(byte[] buf) throws IOException
{
    return read(buf, 0, buf.length);
}
```
(textual specification with JavaDoc)


----

## Contracts/Specifications

* Contracts describe expected behavior for methods, while hiding the implementation behind
* States method's and caller's responsibilities
* Analogy: legal contract
    * If you pay me this amount on this schedule...
    * I will build the following...
    * Some contracts have remedies for nonperformance
* Invariants must hold before and after loop/method execution
* Defines what it means for implementation to be correct, including exceptional behavior

----

## Example: Protocol Specification

![protocol](protocol.png)
<!-- .element: class="stretch" -->


Source: Ryzhyk. On the Construction of Reliable Device Drivers. PhD Thesis 2009


----

## Who is to blame?

```java
Math.sqrt(-5);

> 0
```
----

## Benefits of Specifications

* Exact specification of what should be implemented
* Accurate blame assignments and identification of buggy behavior
* Useful for test generation and as test oracle

----

## Specifications in Machine Learning?

```java
/**
  ????
*/
String transcribe(File audioFile);
```

```java
/**
  ????
*/
List<Product> suggestedPurchases(List<Product> pastPurchases);
```


----

## Specifications in Machine Learning?

* Usually clear specifications do not exist
* Can define correctness for some data, but not general rules. Sometimes can only determine correctness after the fact.
* Learning for tasks for which we cannot write specifications
    - Too complex
    - Rules unknown
* AI will learn rules/specifications, but are those the right ones?
* 
* Often *goals* used instead --> maximize a specific objective

----

[![](inductive.png)](https://danielmiessler.com/blog/the-difference-between-deductive-and-inductive-reasoning/)
<!-- .element: class="stretch" -->


(Daniel Miessler, CC SA 2.0)


----

## Deductive Reasoning

* Combining logical statements following agreed upon rules to form new statements
* Proving theorems from axioms
* From general to the particular
* *mathy reasoning, eg. proof that π is irrational*
* 
* Formal methods, classic rule-based AI systems, expert systems

<!-- split -->

## Inductive Reasoning

* Constructing axioms from observations
* Strong evidence suggests a rule
* From particular to the general
* *sciency reasoning, eg. finding laws of nature*
* 
* Most modern machine learning systems, statistical learning


----

## Shift in Design Thinking

From deductive reasoning to inductive reasoning

From clear specifications to goals

From guarantees to best effort

**What does this mean for software engineering? For correctness of AI-enabled systems? For testing?**

----

## A Touch of Realism

While it is possible to formally specify programs and prove them correct, this is rarely ever done.

In practice, specifications are often textual, local, weak, vague, or ambiguous, if they exist at all. Some informal requirements and some tests might be the only specifications available.

Software engineers have long development methods to deal with uncertainty, missing specifications, and unreliable components.

**AI may raise the stakes, but the problem and solutions are not new.**

---

# Technical Debt

> "Machine learning: The high interest credit card of technical debt" -- [Sculley et al. 2014](https://storage.googleapis.com/pub-tools-public-publication-data/pdf/43146.pdf)

![](debt.jpg)
----

[![](debt.png)](https://www.monkeyuser.com/2018/tech-debt/) 
<!-- .element: class="stretch" -->


----

## The Notebook

> Jupyter Notebooks are a gift from God to those who work with data. They allow us to do quick experiments with Julia, Python, R, and more -- [John Paul Ada](https://towardsdatascience.com/no-hassle-machine-learning-experiments-with-azure-notebooks-e1a22e8782c3)

![](jupyter.png) 
<!-- .element: class="stretch" -->

Notes: Discuss benefits and drawbacks of Jupyter style notebooks

----

## Notebooks

* Allow quick and easy exploration and experimentation
* Literate programming intermixing text, code, and results
* Small code snippets, heavy use of libraries
* 
* Proof of concept on snapshot data only
* Poor abstraction and testing practices
* Low automation, often not scalable
* Difficult transition in production
----

## AI and Technical Debt 

* AI can seem like an easy addition, but it may cause long-term costs
* Needs to be maintained, evolved, and debugged
* Goals may change, environment may change, some changes are subtle
* 
* Example problems
    - Systems and models are tangled and changing one has cascading effects on the other
    - Untested, brittle infrastructure; manual deployment
    - Unstable data dependencies, replication crisis 
    - Data drift and feedback loops
    - Magic constants and dead experimental code paths


<!-- references -->
Further reading: Sculley, David, et al. [Hidden technical debt in machine learning systems](http://papers.nips.cc/paper/5656-hidden-technical-debt-in-machine-learning-systems.pdf). Advances in Neural Information Processing Systems. 2015.


---

# Syllabus and Class Structure

17-445/17-645, Fall 2019, 12 units

Monday/Wednesday 1:30-2:50

----

## Instructors

Christian Kaestner, Eunsuk Kang, Chu-Pan Wong

< brief introductions >


----

## Communication

Email to se-ai@lists.andrew.cmu.edu preferred, rather than individual instructors

Announcements through canvas

Office hours and open door policy (When our door is open and we are not currently meeting with somebody else, feel free to interrupt us for course-related issues.)

----

## Software engineering class

* Focused on engineering judgment
* Arguments, tradeoffs, and justification, rather than single correct answer
* "it depends..."
* Practical engagement, building systems, testing, automation
* Strong teamwork component
* Not focused on formal guarantees or machine learning fundamentals (modeling, statistics)

----

## Prerequisites

<!-- colstart -->
Some **software engineering experience**
* version control
* gathering requirements
* software design and modeling
* testing and test automation

<!-- col -->
**Machine learning basics**
* extracting features, building and evaluating models
* basic understanding of how different kinds of learning techniques work

<!-- colend -->

Use knowledge check on canvas to identify gaps. Talk to us about strategies to fill gaps.

----

## Active lecture

* Case study driven
* Discussion highly encouraged
* Contribute own experience
* Regular active in-class exercises
* In-class presentation
* Discussions over definitions


----
## Laptop policy

Empirical research is fairly clear: 
* "Multi-tasking on laptops during class poses a significant distraction to laptop users and **fellow students**"<sup>[1]</sup>
* "...students who took notes on laptops performed worse on conceptual questions than students who took notes longhand"<sup>[2]</sup> 

Smoking section policy: *Avoid laptops beyond note-taking. If you want to use laptops, sit in the back.*


<!-- references -->

[1]: Faria Sana, Tina Weston, and Nicholas J. Cepeda. 2013. [Laptop multitasking hinders classroom learning for both users and nearby peers](https://www.sciencedirect.com/science/article/pii/S0360131512002254). *Comput. Educ.* 62 (March 2013), 24-31. 

[2]: Mueller, Pam A., and Daniel M. Oppenheimer. [The pen is mightier than the keyboard: advantages of longhand over laptop note taking](https://journals.sagepub.com/doi/full/10.1177/0956797614524581) *Psychological science* 25.6 (2014): 1159-1168.


----
## Textbook

Building Intelligent Systems: A Guide to Machine Learning Engineering

by Geoff Hulten

https://www.buildingintelligentsystems.com/

Various chapters assigned throughout the semester

Supplemented with research articles, blog posts, videos, podcasts, ...

<!-- split -->

![Building intelligent systems book](book.webp)

----

## Readings and Quizzes

* Reading assignments for most lectures
  * Preparing in-class discussions
  * Background material, case descriptions, possibly also podcast, video, wikipedia
  * Complement with own research
* Short and easy online quizzes on readings, due by start of lecture

----

## Assignments

* Series of small to medium-sized assignments: 
    * engage with practical challenges
    * design, implement, and automate
    * reason about tradeoffs and justify your decisions

* Individual and team assignments

* No capstone project

----

## Grading

* 50% assignments
* 15% midterm
* 20% final
* 10% participation
* 5% reading quizzes

----

## Participation

* Participation is important
    - Participation in in-class discussions
    - Active participation in recitations
    - Both quality and quantity are important, quality more than quantity
* Participation != Attendance

----

## Late day policy

Late work in **group assignments** will receive feedback but no credit. 

Late work in **individual assignments** will be accepted with a 10% penalty per day, for up to 3 days. 

Talk to us (early) for concerns and exceptions.

----

## Academic honesty

See web page

In a nutshell: do not copy, do not lie, do not share or publicly release your solutions

In group work, be honest about contributions of team members, do not cover for others

If you feel overwhelmed or stressed, please come and talk to us (see syllabus for other support opportunities)

----

![Class Overview](overview.png)

----

## Aside: AI vs ML

* Artificial intelligence is an umbrella term covering symbolic AI (problem solving, reasoning) as well as machine learning (statistical learning from data)
* This course focuses mostly on *statistical machine learning* (extrapolating from data, inductive reasoning)
* We will cover *symbolic AI* (expert systems, probabilistic reasoning, ...) selectively, often for contrast



---

# Survey time

Survey helps us to tailor class and form teams.

![survey](survey.jpg)

---

# Summary

* *Data scientists* and *software engineers* have different goals and focuses
  * Building systems requires both
  * Various qualities are relevant, beyond just accuracy
  * Deliberate engineering for production, beyond experimentation notebooks
* Inductive reasoning and lack of specifications
