---
author: Christian Kaestner
title: "17-445: Process and Team Reflections"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
license: Creative Commons Attribution 4.0 International (CC BY 4.0)
---

# Process and Team Reflections

Christian Kaestner

<!-- references -->

Required reading: DeMarco and Lister. Peopleware: Productive Projects and Teams. Addison-Wesley, 3rd ed., 2013. Chapters 22, 23, and 28.

---

# Learning Goals

* Plan development activities in an inclusive fashion for participants in different roles
* Describe agile techniques to address common process and communication issues

---

# Case Studies

Disclaimer: All pictures represent abstract developer groups or products to give a sense of scale; they are not necessarily the developers of those products or developers at all.

----

## How to structure teams?

Microblogging platform; 3 friends

<!-- colstart -->
![Small team](team4.jpg)
<!-- col -->
![Twitter](twitter.png)
<!-- colend -->

----
## How to structure teams?

Banking app; 15 developers and data analysts

<!-- colstart -->
![Small team](team15.jpg)
<!-- col -->
![PNC app](pnc.jpg)
<!-- colend -->

----
## How to structure teams?

Mobile game; 
50ish developers;
distributed teams?

![Team 50](team50.jpg)
----
## How to structure teams?

Mobile game; 
50ish developers;
distributed teams?

![Team 200](team200.png)

----
## How to structure teams?

Self-driving cars; 1200 developers and data analysts

<!-- colstart -->
![Large team](team1200.jpg)
<!-- col -->
![Uber self driving car](uber.png)
<!-- colend -->

---
# Teams

----
## Necessity of Groups

* Division of labor
* Division of expertise (e.g., security expert, ML expert, data cleaning expert, database expert)

----
## Team Issues

* Interdisciplinary
* Process costs
* Groupthink
* Social loafing
* Multiple/conflicting goals

---
# Team issues: Process costs
----
## Mythical Man Month

> Brooks's law: Adding manpower to a late software project makes it later

![](mmmbook.jpg)

1975, describing experience at 
IBM developing OS/360
----
## Process Costs

![](connected.png)

*n(n − 1) / 2* communication links
----
## Process Costs

![](connectedteams.png)
----
## Brook's Surgical Teams

* Chief programmer – most programming and initial documentation
* Support staff
    * Copilot: supports chief programmer in development tasks, represents team at meetings
    * Administrator: manages people, hardware and other resources
    * Editor: editing documentation 
    * Two secretaries: one each for the administrator and editor
    * Program clerk: keeps records of source code and documentation
    * Toolsmith: builds specialized programming tools
    * Tester: develops and runs tests
    * Language lawyer: expert in programming languages, provides advice on producing optimal code.

<!-- references -->

Brooks. The Mythical Man-Month. 1971

----
## Microsoft's Small Team Practices

* Vision statement and milestones (2-4 month), no formal spec
* Feature selection, prioritized by market, assigned to milestones
* Modular architecture
* Allows small federated teams (Conway's law)
* Small teams of overlapping functional specialists

(Windows 95: 200 developers and testers, one of 250 products)

----
## Microsoft's Feature Teams

* 3-8 developers (design, develop)
* 3-8 testers (validation, verification, usability, market analysis)
* 1 program manager (vision, schedule communication; leader, facilitator) – working on several features
* 1 product manager (marketing research, plan, betas)
----
## Microsoft's Process

* "Synchronize and stabilize"
* For each milestone
    * 6-10 weeks feature development and continuous testing
frequent merges, daily builds
    * 2-5 weeks integration and testing (“zero-bug release”, external betas   )
    * 2-5 weeks buffer

----
## Agile Practices (e.g., Scrum)

* 7±2 team members, collocated
* self managing
* Scrum master (potentially shared among 2-3 teams)
* Product owner / customer representative

----
> Large teams (29 people) create around six times as many defects as small teams (3 people) and obviously burn through a lot more money. Yet, the large team appears to produce about the same mount of output in only an average of 12 days’ less time. This is a truly astonishing finding, through it fits with my personal experience on projects over 35 years. - Phillip Amour, 2006, CACM 49:9

----
## Establish communication patterns

* Avoid overhead
* Ensure reliability
* Constraint latency
* 
* e.g. Issue tracker vs email; online vs face to face

----
## Awareness

* Notifications
* Brook's documentation book
* Email to all
* Code reviews

----
## Conway’s Law

> “Any organization that designs a system (defined broadly) will produce a design whose structure is a copy of the organization's communication structure.” — Mel Conway, 1967

> “If you have four groups working on a compiler, you'll get a 4-pass compiler.”

---
## Congurence

![](congruence.png)

Structural congruence,
Geographical congruence,
Task congruence,
IRC communication congruence

---
# Team issues: Multiple/conflicting goals

(Organization of Interdisciplinary Teams)

----
## Matrix Organization

![](teammatrix.png)
----
## Project Organization

![](teamproject.png)

----
## Case Study: Brøderbund

> As the functional departments grew, staffing the heavily matrixed projects became more and more of a nightmare. To address this, the company reorganized itself into “Studios”, each with dedicated resources for each of the major functional areas reporting up to a Studio manager. Given direct responsibility for performance and compensation, Studio managers could allocate resources freely.

> The Studios were able to exert more direct control on the projects and team members, but not without a cost. The major problem that emerged from Brøderbund’s Studio reorganization was that members of the various functional disciplines began to lose touch with their functional counterparts. Experience wasn’t shared as easily. Over time, duplicate effort began to appear.

----
## Conflicting Goals

* Software engineers vs Data scientists
* Software engineers vs Security specialists
* Data scientists vs Privacy lawyers

<!-- discussion -->

CC 3.0 SA by Shishirdasika

----
![Computational Notebook](notebook.png)

<!-- references -->

Notes:

Different practices and goals. Transitional exploratory notebook code into production?

----
## Specialist Allocation (Organizational Architectures)

* Centralized: development teams consult with a core group of  specialists when they need help
* Distributed: development teams hire specialists to be a first-class member of the team
* Weak Hybrid: centralized group of specialists and teams with  critical applications hire specialists
* Strong Hybrid: centralized group of specialists and most teams also hire specialists

**Tradeoffs?**

----
## Example: Security Roles

* Everyone: “security awareness” – buy into the process
* Developers: know the security capabilities of development tools and use them, know how to spot and avoid relevant, common vulnerabilities
* Managers: enable the use of security practices
* Security specialists: everything security

----
## Data Scientists on Software Teams

<!-- discussion -->

----
## Commitment & Accountability

* Conflict is useful, expose all views
* Come to decision, commit to it
* Assign responsibilities
* Record decisions and commitments; make record available

----
## Bell & Hart – 8 Causes of Conflict

* Conflicting resources.
* Conflicting styles.
* Conflicting perceptions.
* Conflicting goals.
* Conflicting pressures.
* Conflicting roles.
* Different personal values.
* Unpredictable policies.

<!-- references -->
Bell, Art. (2002). Six ways to resolve workplace conflicts.
McLaren School of Business, University of San Francisco., https://www.mindtools.com/pages/article/eight-causes-conflict.htm
---
# Team issues: Groupthink

![](groupthink.png)

----
## Groupthink

* Group minimizing conflict
* Avoid exploring alternatives
* Suppressing dissenting views
* Isolating from outside influences
* -> Irrational/dysfunctional decision making

----
## Example: Time and Cost Estimation

<!-- discussion -->

----
## Example: Use of Hype Technology

(agile, block chain, machine learning, devops, AIOps, ...)

<!-- discussion -->

----
## Causes of Groupthink

* High group cohesiveness, homogeneity
* Structural faults (insulation,  biased leadership, lack of methodological exploration)
* Situational context (stressful external threats, recent failures, moral dilemmas)

----
## Symptoms

* Overestimation of ability: invulnerability, unquestioned believe in morality
* Closed-mindedness: ignore warnings, stereotyping; innovation averse
Pressure toward uniformity: self-censorship, illusion of unanimity, …
----
![](svposter.png)
----
## Diversity

> “Men and women have different viewpoints, ideas, and market insights, which enables better **problem solving**. A gender-diverse workforce provides easier **access to resources**, such as various sources of credit, multiple sources of information, and wider industry knowledge. A gender-diverse workforce allows the company to serve an **increasingly diverse customer base**. Gender diversity helps companies **attract and retain talented women**.”

> “Cultural diversity leads to **process losses** through task conflict and decreased social integration, but to process gains through increased creativity and satisfaction.”

<!-- references -->


Stahl, Günter K., et al. "Unraveling the effects of cultural diversity in teams: A meta-analysis of research on multicultural work groups." Journal of international business studies 41.4 (2010): 690-709.

http://www.gallup.com/businessjournal/166220/business-benefits-gender-diversity.aspx

----
## Groupthink and AI

* Fairness
* Safety requirements (e.g. Pitt delivery robot)
* Ethics

----
## Mitigation Strategies

<!-- discussion -->

---
# Team issues: Social loafing

![](tug.png)

----
![](loafinggraph.png)

<!-- references -->

Latane, Bibb, Kipling Williams, and Stephen Harkins. "Many hands make light the work: The causes and consequences of social loafing." Journal of personality and social psychology 37.6 (1979): 822.

----
## Social Loafing

* People exerting less effort within a group
* Reasons
    * Diffusion of responsibility
    * Motivation
    * Dispensability of effort / missing recognition
    * Avoid pulling everybody / "sucker effect"
    * Submaximal goal setting
* “Evaluation potential, expectations of co-worker performance, task meaningfulness, and culture had especially strong influence”


<!-- references -->

Karau, Steven J., and Kipling D. Williams. "Social loafing: A meta-analytic review and theoretical integration." Journal of personality and social psychology 65.4 (1993): 681.

----
## Mitigation Strategies

<!-- discussion -->

----
## Mitigation Strategies

* Involve all team members, colocation
* Assign specific tasks with individual responsibility
    * Increase identifiability
    * Team contracts, measurement
* Provide choices in selecting tasks
* Promote involvement, challenge developers
* Reviews and feedback
* Team cohesion, team forming exercises
* Small teams

----
## Responsibilities & Buy-In

* Involve team members in decision making
* Assign responsibilities (ideally goals not tasks)
* Record decisions and commitments; make record available

----
## Motivation

Autonomy * Mastery * Purpose

![](drivebook.gif)


---
# General Guidelines

----
## Hints for team functioning

* Trust them; strategic not tactical direction
* Reduce bureaucracy, protect team
* Physical colocation, time for interaction
* Avoid in-team competition (bonuses etc)
* Time for quality assurance, cult of quality
* Realistic deadlines
* Peer coaching
* Sense of elitism
* Allow and encourage heterogenity

<!-- references -->

DeMarco and Lister. Peopleware. Chapter 23

----
## Elitism Case Study: The Black Team

* Legendary team at IBM in the 1960s
* Group of talented ("slightly better") testers
    * Goal: Final testing of critical software before delivery
* Improvement over first year
* Formed team personality and energy
    * "adversary philosophy of testing"
    * Cultivated image of destroyers
    * Started to dress in black, crackled laughs, grew mustaches
* Team survived loss of original members


<!-- references -->

DeMarco and Lister. Peopleware. Chapter 22

----
## Troubleshooting Teams

* Cynicism as warning sign
* Training to improve practices
* Getting to know each other; celebrate success; bonding over meals
* “A meeting without notes is a meeting that never happened”


---

# Summary

* Team disfunctions well studied
* Know the signs, know the interventions
* Small teams, crossfunctional teams
* Create awareness and accountability
* Further Readings:
    * Mantle and Lichty. Managing the Unmanageable. Addison-Wesley, 2013
    * DeMarco and Lister. Peopleware. 3rd Edition. Addison Wesley, 2013
