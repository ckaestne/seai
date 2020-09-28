# Individual Assignment 3: Requirements and Risks

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will zoom out from the AI component and think about the requirements and risks associated with a larger AI-enabled system in a concrete scenario. You may again work with a partner (optional, see below).

In this assignment, you will get practice on how to systematically identify system requirements and risks associated with a larger AI-enabled system. In particular, you will learn to (a) make a clear distinction between the roles that environmental and machine entities play in system dependability, and (2) apply fault tree analysis (FTA) to identify potential risks in a case study scenario involving a vehicle dash cam.

Learning goals:
* Understand the role of the environment in establishing system requirements.
* Learn to systematically identify risks and design mitigation strategies.
* Understand the strengths and limitations of FTA.

## Scenario

[Dashcams](https://en.wikipedia.org/wiki/Dashcam) are getting more popular and are broadly installed in many vehicles already. As a manufacturer of dashcams, you want to develop features that distinguish your dashcams from those of your competitors. As one project, you work with a non-profit organization on *child safety*: The project's goal is to use dashcam footage to locate children reported missing. However, instead of broadcasts, such as [Amber alerts](https://en.wikipedia.org/wiki/Amber_alert) your products will allow to search for those children in video recordings made by the dashcam.

Assume that you are contracting out the AI component that recognizes persons in images and video to a company with extensive experience in face recognition based on deep neural networks. The contractors build on past tools and infrastructure (e.g., [Amazon Rekognition](https://aws.amazon.com/rekognition/)) but will customize one or multiple components to your needs, to the extent possible (e.g., deploying models offline would be an option). They will provide you with the infrastructure to train and serve person recognition models, which you can operate and update in-house.

In designing such system, there are many considerations, such as:
* Your dashcams do not have direct internet access, but they can communicate over USB, Bluetooth or Wifi with phones, cars, and wifi-hotspots.
* The dashcams may run on battery but are usually connected to the car's power supply. Their processing power differs from model to model.
* Searches are coordinated with the authorities and the non-profit organization. You suspect less strict requirements as for Amber alerts, but the legal details are not worked out yet. Searches are likely not very frequent in any given area. For Amber alerts, [official statistics](https://amberalert.gov/statistics.htm) report nearly 1 alert per day nationwide.
* Faster reports of sightings are more useful to the authorities.
* You suspect users may be worried about privacy and charges for data.
* You recently hear everywhere, including press and consultants, how exciting the future of [Edge computing](https://en.wikipedia.org/wiki/Edge_computing) rather than Cloud computing is going to be and wonder whether you should explore that. You wouldn't be opposed to thinking about partnering with other organizations to, say, install hardware in gas stations or drive throughs.

You are concerned at least about the following qualities:

1. Latency between reporting a child missing (with numerous pictures) to receiving potential matches from dashcam users
2. Number of false positives and false negatives
3. Ability to observe how well the system works in production
4. Scalability and cost of running the infrastructure with many users across many countries
5. Operating costs for users
6. Difficulty of changing and updating the system to meet new requirements or incorporate better technology
7. Privacy
8. Development cost, technical complexity of the solution, maintainability

## Tasks

Think about requirements for such a system and how would you decompose them into specifications on individual components (AI or not). What assumptions about the environment does this system need to rely on? What could go wrong and how could risks be mitigated? You will focus on two aspects: goals (requirements) and risks.

First, identify the goals for the new feature in the dashcam. Break down goals into *organizational objectives*, *leading indicators*, *user outcomes*, and *model properties* and provide corresponding measures you could use to assess how well you achieve the goals. Provide a brief description how goals relate to each other (e.g., “better model accuracy should help with higher user satisfaction”). Organizational objectives and leading indicators should be stated from the perspective of the company (not the partnering non-profits or authorities).  For user outcomes and model properties make clear to which users or models the goal refer; you may state different goals for different users. Your list of goals should be reasonably comprehensive and may include multiple goals at each level.

Second, think about what could go wrong by performing a fault tree analysis. Start with a top event being a violation of a system requirement (i.e., the system failing to achieve a desired organizational objective) and break it into intermediate and basic events (which may correspond to a violation of an environmental assumption or an AI component failing to satisfy its specification). List possible casues of the system-level failure by identifying minimal cut sets and suggest strategies for mitigating them. Mitigation strategies will typically be at the system level, outside of the AI component itself. Briefly explain how each suggested mitigation strategy can (partially for fully) address the risk.

## Deliverable

Submit a report as a single PDF file to Gradescope that covers the following topics in clearly labeled sections (ideally each section starts on a new page):

1. **Goals** (1 page max): Provide a list of organizational objectives, leading indicators, user outcomes, and model properties.
2. **Environment and Machine** (0.5 page max): Identify environmental entities and machine components (AI and non-AI) in this scenario. The machine components must include at least one AI component that performs image recognition.
3. **Requirement Decomposition** (1 page max): Select **one** of the organization objectives as a requirement to analyze. Specify a list of environment assumptions (ENV) and specifications (SPEC) that are needed to establish this requirement (REQ).
4. **Risk analysis** (1.5 page max) Perform a fault tree analysis to identify potential root causes for the violation of the requirement selected in Q2. Identify at least **three** minimal cut sets in your fault tree. (For this question, you may use any tool of your choice to construct the fault tree. A scan of a hand-drawn diagram is also acceptable, as long as it is clearly legible. There are also several free FTA tools you may wish to use; e.g., Fault Tree Analyzer (https://www.fault-tree-analysis-software.com) or Open Reliability Editor (https://github.com/troeger/fuzzed)).
5. **Mitigations** (1 page max): For each one of the three causes (minimal cut sets) identified in Q3, suggest a mitigation strategy to reduce the risk of the failure.

## Grading

The assignment is worth 100 points. For full credit, we expect:
* [ ] 20 points: Goals are listed and correctly grouped. The goals relate to the scenario and are reasonably complete.
* [ ] 10 points: Environment entities and machine components relevant to the scenario are listed. The machine components include at least one AI component that performs image recognition.
* [ ] 20 points: A selected requirement (REQ) is clearly stated. Environmental assumptions (ENV) and machine specifications (SPEC) needed to establish this requirement are included.
* [ ] 30 points: A fault tree that shows possible causes behind the violation of the requirement selected in Q3 is included. At least three minimal cut sets are identified. The included fault tree is syntactically valid.
* [ ] 20 points: Three mitigation strategies for the cut sets identified in Q4 are included.

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class, under the following condition: *You may not work with anybody who you know well or who was on your team in a previous course or previous assignment (including I2).* To facilitate the search for team members, we post a link to a shared Google spreadsheet on Canvas.

If you work together as a team, you can either submit a joint solution or separate solutions on Gradescope. If you submit a joint solution, both team members will receive the same grade. If you submit separate solutions, those solutions may share text or code, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.

