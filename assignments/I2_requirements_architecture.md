# Individual Assignment 2: Requirements and Architecture

(11-695/17-445/17-645/17-745 Machine Learning in Production / AI Engineering)

## Overview

In this assignment, you will zoom out from the AI component and think about the requirements and risks associated with a larger AI-enabled system in a concrete scenario and the architecture of how to deploy it. 

In this assignment, you will get practice on how to systematically identify system requirements and risks associated with a larger AI-enabled system. In particular, you will learn to (a) make a clear distinction between the roles that environmental and machine entities play in system dependability, and (2) apply fault tree analysis (FTA) to identify potential risks in a case study scenario involving a vehicle dash cam. You will furthermore discuss different deployment options.

This 2-week assignment combines assignments on two topics, each worth 100 points, each planned for about 1 week. Both parts can be solved independently, but it may make sense to think about a possible architecture already when discussing requirements and risks.

Learning goals:
* Understand the role of the environment in establishing system requirements.
* Learn to systematically identify risks and design mitigation strategies.
* Apply FTA to understand risks and plan mitigations in an AI-enabled system
* Understand the strengths and limitations of FTA.
* Reason about qualities relevant to the deployment of an AI component in a system architecture
* Design measures to quantify system goals, design qualities, and telemetry feedback

## Scenario

[Dashcams](https://en.wikipedia.org/wiki/Dashcam) are getting more popular and are broadly installed in many vehicles already. As a manufacturer of dashcams, you want to develop features that distinguish your dashcams from those of your competitors. As one project, you work with a non-profit organization on *child safety*: The project's goal is to use dashcam footage to locate children reported missing. However, instead of broadcasts, such as [Amber alerts](https://en.wikipedia.org/wiki/Amber_alert) your products will allow to search for those children in video recordings made by the dashcam.

Assume that you are contracting out the AI component that recognizes persons in images and video to a company with extensive experience in face recognition based on deep neural networks. The contractors build on past tools and infrastructure (e.g., [Amazon Rekognition](https://aws.amazon.com/rekognition/)) but will customize one or multiple components to your needs, to the extent possible (e.g., deploying models offline would be an option). They will provide you with the infrastructure to train and serve person recognition models, which you can operate and update in-house.

In designing such system, there are many considerations, such as:
* Your dashcams do not have direct internet access, but they can communicate over USB, Bluetooth or Wifi with phones, cars, and wifi-hotspots.
* The dashcams may run on battery but are usually connected to the car's power supply. Their processing power differs from model to model.
* Searches are coordinated with the authorities and the non-profit organization. You suspect less strict requirements as for Amber alerts, but the legal details are not worked out yet. Searches are likely not very frequent in any given area. For Amber alerts, [official statistics](https://amberalert.gov/statistics.htm) report about 1 alert per day *nationwide*.
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

## Tasks, Part A: Requirements and Risks

Think about requirements for such a system and how would you decompose them into specifications on individual components (AI or not). What assumptions about the environment does this system need to rely on? What could go wrong and how could risks be mitigated? You will focus on two aspects: goals (requirements) and risks.

First, identify the goals for the new feature in the dashcam. Break down goals into *organizational objectives*, *leading indicators*, *user outcomes*, and *model properties* and provide corresponding measures you could use to assess how well you achieve the goals. Provide a brief description how goals relate to each other (e.g., “better model accuracy should help with higher user satisfaction”). Organizational objectives and leading indicators should be stated from the perspective of the company (not the partnering non-profits or authorities).  For user outcomes and model properties make clear to which users or models the goal refer; you may state different goals for different users. Your list of goals should be reasonably comprehensive and may include multiple goals at each level.

Second, think back to the world vs machine discussion in class. Consider one of the critical requirements of the system (REQ), based on the system-level goals that you derived earlier. What assumptions about the environment (ENV) do you need to rely on to achieve this requirement? What are the responsibilities (SPEC) of the machine components (both AI and non-AI) that are needed to establish REQ in conjunction with ENV?

Third, think about what could go wrong and analyze one possible risk with fault tree analysis. First identify a requirement violation (risk) to analyze – this might come from brainstorming or more systematically analyzing the requirements and environment assumptions above. Start with the top event being a violation of a requirement and break it into intermediate and basic events (which may correspond to a violation of an environmental assumption or an AI component failing to satisfy its specification). List possible causes of the system-level failure by identifying minimal cut sets. Design at least two strategies for mitigating the risks of potential failures and incorporate them into the fault tree. Mitigation strategies will typically be at the system level, outside of the AI component itself, and will reduce the risk of the requirement violation. Briefly explain how each suggested mitigation strategy can (partially for fully) address the risk.

## Tasks, Part B: Architecture

**Deployment.** Compare four different design alternatives about how to deploy the system with regard to the eight qualities listed in the scenario. To that end, analyze whether the AI component(s) for recognizing a person in an image should be deployed (a) on the dashcam, (b) on a phone, (c) in the cloud, or (d) some other configuration you describe (e.g., hybrid or edge). Provide a short explanation and an architecture diagram for your fourth design.

Where possible estimate the impact of the different designs on the eight different qualities. You may want to do some Internet research about typical characteristics of various hardware and software components (e.g., storage capacity of dashcams, size of typical face recognition models, bandwidth of Bluetooth connections). You do not need to conduct precise measurements or estimate concrete values, but should inform your discussion with an understanding of the qualities in the context of the scenario (e.g., “solution A is better than solution B because of a bottleneck in Bluetooth bandwidth” or “privacy is better in solution C because customer data does not leave the device”). 

After understanding the four different designs, explicitly discuss the tradeoffs involved, which involves discussing the relative relevance of the qualities and the differences in qualities for the different solutions. Recommend one of the solutions.

**Telemetry.** Suggest a design for telemetry to identify how well the system and the AI component(s) are performing in production. Be explicit about what data you would collect, what quality measure you use, and how you would use the collected data to compute the quality measure. Briefly justify your design and why it is appropriate in the context of the scenario. That discussion should cover at least (1) the amount of data transmitted or stored, (2) how it copes with rare events, and (3) whether it can detect both false positives and false negatives.



## Deliverable

Submit a report as a single PDF file to Gradescope that covers the following topics across two parts in clearly labeled sections (ideally each section starts on a new page):

**Part A: Requirements and Risks**

1. **Goals** (1 page max): Provide a list of organizational objectives, leading indicators, user outcomes, and model properties.
2. **Environment and Machine** (0.5 page max): Identify environmental entities and machine components (AI and non-AI) in this scenario. The machine components must include at least one AI component that performs image recognition.
3. **Requirement Decomposition** (1 page max): Select **one** of requirement to analyze based on the goals identified above. Specify a list of environment assumptions (ENV) and specifications (SPEC) that are needed to establish this requirement (REQ).
4. **Risk analysis** (1.5 page max) Perform a fault tree analysis to identify potential root causes for the violation of the requirement selected in the previous step. Identify all minimal cut sets in your fault tree. 
5. **Mitigations** (1 page max): Suggest at least two mitigation strategy to reduce the risk of the failure studied in the fault tree. Both mitigations should be at the system level, outside of the ML component (i.e., not just "collect more training data"). Briefly explain how the mitigations reduce the risk. Provide a second updated fault tree that includes those mitigations.

**Part B: Architecture**

1. **Analysis of deployment alternatives** (no page limit): Briefly describe the fourth deployment architecture considered and provide an architecture diagram. Then for each of the 4 deployment options discuss the 8 qualities listed above. A tabular representation (one column per deployment option, one row per quality) may be suitable, but other clearly structured formats are possible. Rough estimates or relative ratings with a brief explanation are sufficient as long as they are grounded and realistic in the scenario.
2. **Recommendation and justification of deployment architecture** (1 page max): Recommend a deployment architecture and justify this recommendation in terms of the relative relevance of the qualities and the tradeoffs among quality attributes.
3. **Telemetry** (1 page max): Suggest how telemetry should be selected, describe how quality would be measured from telemetry data, and briefly justify those decisions.

For drawing fault trees, you may use any tool of your choice. A scan of a hand-drawn diagram is acceptable, as long as it is clearly legible. There are also several free FTA tools you may wish to use; e.g., [Fault Tree Analyzer](https://www.fault-tree-analysis-software.com) or [Open Reliability Editor](https://github.com/troeger/fuzzed).

## Grading

The assignment is worth 200 points. For full credit, we expect:

**Part A: Requirements and Risk**

* [ ] 20 points: Goals are listed and appropriately grouped. The goals relate to the scenario and are reasonably complete.
* [ ] 10 points: Environment entities and machine components relevant to the scenario are listed. The machine components include at least one AI component that performs image recognition.
* [ ] 10 points: A selected requirement (REQ) is clearly stated. The requirement mention only phenomena in the world.
* [ ] 10 points: Environmental assumptions (ENV) are clearly stated. These assumptions relate to phenomena in the world or map those to shared phenomena accessibly by the machine.
* [ ] 10 points: Machine specifications (SPEC) are clearly stated. These specifications mention only those phenomena in the interface between the world and the machine.
* [ ] 5 points: The requirement, environmental assumption, and machine specifications fit reasonably together and correspond to the scenario.
* [ ] 15 points: A fault tree that shows possible causes behind the violation of the requirement selected in Q3 is included. The included fault tree is syntactically valid.
* [ ] 10 points: Minimal cut sets are identified from the fault tree.
* [ ] 10 points: At least two mitigation strategies, corresponding to the requirement and the cut sets identified, are described. The description explains how the risk is reduced. The mitigations are at the system level outside the component. The mitigations are shown in an updated fault tree.

**Part B: Architecture**

* [ ] 10 points: Description of a fourth deployment architecture is included. 
* [ ] 10 points: An architecture diagram for the fourth deployment architecture is included and matches the description.
* [ ] 20 points: For each of the 4 design alternatives at least 4 quality attributes are analyzed. The analysis is plausible for the scenario.
* [ ] 10 points: For each of the 4 design alternatives all 8 quality attributes are analyzed plausibly. The analysis is plausible for the scenario.
* [ ] 10 points: Recommendation for a deployment decision provided and a justification for the decision is provided. 
* [ ] 10 points: The justification clearly makes tradeoffs among the discussed qualities and weighs the relative importance of the qualities to come to a conclusion supported by the analysis.
* [ ] 10 points: Telemetry design is suggested and described, describing the goal of the telemetry and what data is collected. 
* [ ] 10 points: The telemetry section contains a description of quality measures and how they can be derived from the telemetry data. 
* [ ] 10 points: The telemetry section contains a justification for the chosen approach. The justification considers (1) the amount of data transmitted or stored, (2) how telemetry copes with rare events, and (3) whether this form of telemetry can detect both false positives and false negatives.
