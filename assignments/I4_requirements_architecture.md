# Individual Assignment 4: Requirements and Architecture

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will zoom out from the AI component and think about the requirements and the architecture of a larger AI-enabled system in a concrete scenario. You may again work with a partner (optional, see below).

Learning goals:
* Analyze a system’s goals and define corresponding measures
* Analyze risks of mistakes by AI components and design mitigation strategies
* Reason about qualities relevant to the deployment of an AI component in a system architecture
* Design measures to quantify system goals, design qualities, and telemetry feedback

## Scenario

[Dashcams](https://en.wikipedia.org/wiki/Dashcam) are getting more popular and are broadly installed in many vehicles already. As a manufacturer of dashcams, you want to develop features that distinguish your dashcams from those of your competitors. As one project, you work with a non-profit organization on *child safety*: The project's goal is to use dashcam footage to locate children reported missing. However, instead of broadcasts, such as [Amber alerts](https://en.wikipedia.org/wiki/Amber_alert) your products will allow to search for those children in video recordings made by the dashcam.

Assume that you are contracting out the AI component that recognizes persons in images and video to a company with extensive experience in face recognition based on deep neural networks. The contractors build on past tools and infrastructure (e.g., [Amazon Rekognition](https://aws.amazon.com/rekognition/)) but will customize one or multiple components to your needs, to the extend possible (e.g., deploying models offline would be an option). They will provide you with the infrastructure to train and serve person recognition models, which you can operate and update in-house.

In designing such system, there are many considertions, such as:
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

Think about requirements for such a system and how you would design it (no implementation needed for this assignment). What could go wrong and how could risks be mitigated? What would be the main components (AI or not), where might they be located? Consider alternative designs. You will focus on four aspects: goals, risks, deployment architecture, and telemetry.

First, identify the goals for the new feature in the dashcam. Break down goals into *organizational objectives*, *leading indicators*, *user outcomes*, and *model properties* and provide corresponding measures you could use to assess how well you achieve the goals. Provide a brief description how goals relate to each other (e.g., “better model accuracy should help with higher user satisfaction”). Organizational objectives and leading indicators should be stated from the perspective of the company (not the partnering non-profits or authorities).  For user outcomes and model properties make clear to which users or models the goal refer; you may state different goals for different users. Your list of goals should be reasonably comprehensive and may include multiple goals at each level.

Second, think about risks based on wrong predictions by the image recognition component and possible mitigation strategies. Specifically think about possible safeguards, experience design, and keeping humans in the loop. Identify and explain at least 3 relevant risks caused by wrong predictions and suggest mitigation strategies. Mitigation strategies will typically be at the system level, outside of the AI component itself. Briefly explain how each suggested mitigation strategy can (partially for fully) address the risk. Optional: You can receive bonus points if you systematically use and document a risk analysis technique (e.g., FTA, FMEA, HAZOP) in your analysis.

Third, suggest a deployment architecture and discuss tradeoffs with an alternative design. To that end, suggest whether the AI component(s) for recognizing a person in an image should be deployed (a) on the dashcam, (b) on a phone, (c) in the cloud, or (d) some other configuration you describe (e.g., hybrid or edge). Briefly describe your fourth considered design, then explicitly discuss the tradeoffs involved in this discussion by comparing the suggested design with an alternative design according to the qualities listed above, which involves discussing the relative relevance of the qualities and the differences in qualities for the different solutions. Where possible estimate the impact of the different designs on the different qualities. You may want to do some Internet research about typical characteristics of various hardware and software components (e.g., storage capacity of dashcams, size of typical face recognition models, bandwidth of Bluetooth connections). You do not need to conduct precise measurements or estimate concrete values, but should inform your discussion with an understanding of the qualities in the context of the scenario (e.g., “solution A is better than solution B because of a bottleneck in Bluetooth bandwidth” or “privacy is better in solution C because customer data does not leave the device”). We recommend but do not require to add diagrams to explain your fourth design and generally to support your discussion.

Fourth, suggest a design for telemetry to identify how well the system and the AI component(s) are performing in production. Be explicit about what data you would collect, what quality measure you use, and how you would use the collected data to compute the quality measure. Briefly justify your design and why it is appropriate in the context of the scenario. That discussion should cover at least (1) the amount of data transmitted or stored, (2) how it copes with rare events, and (3) whether it can detect both false positives and false negatives.


## Deliverable

Submit a report as a single PDF file to Gradescope that covers the following topics in clearly labeled sections (ideally each section starts on a new page):

1. **Goals** (1 page max): Provide a list of organizational objectives, leading indicators, user outcomes, and model properties and corresponding measures. Briefly discuss how goals relate to each other.
2. **Risks** (1.5 page max) Describe three relevant risks from wrong predictions and corresponding mitigation strategy. Explain how each mitigation strategy reduces the risk.
3. **Analysis of deployment alternatives:** Briefly describe the fourth deployment architecture considered. Then for each of the 4 deployment options discuss the 8 qualities listed above. A tabular representation (one column per deployment option, one row per quality) may be suitable, but other clearly structured formats are possible. Rough estimates or relative ratings with a brief explanation are sufficient as long as they are grounded and realistic in the scenario.
4. **Recommendation and justification of deployment architecture** (1 page max): Recommend a deployment architecture and justify this recommendation in terms of the relative relevance of the qualities and the tradeoffs among quality attributes.
5. **Telemetry** (1 page max): Suggest how telemetry should be selected, describe how quality would be measured from telemetry data, and briefly justify those decisions.
6. **Optional: Formal risk analysis:** Provide a brief description of the risk analysis process selected and how it was systematically applied. Provide supporting evidence (e.g., diagrams, tables, screenshots) of the risk analysis performed and briefly discussed insights gained from applying a method systematically, if any.

Graphics and tables do not count against the page limit.


## Grading

The assignment is worth 100 points. For full credit, we expect:
* [ ] 25 points: Goals listed and correctly grouped (10p). List of goals relates to scenario and reasonable complete (5p). For each goal a metric is clearly defined that could realistically be measured in the scenario (5p). The relationship of goals is described and plausible (5p).
* [ ] 25 points: Three risks from wrong predictions are described that are relevant in the scenario (10p). For each risk a plausible mitigation strategy is suggested and explained (15p).
* [ ] 15 points: Description of a fourth deployment architecture is included. For each of the 4 design alternatives all 8 quality attributes are analyzed plausibly.
* [ ] 15 points: Recommendation for a deployment decision provided and justified (10p). The justification clearly makes tradeoffs among the qualities and weighs the relative importance of the qualities (5p).
* [ ] 20 points: Telemetry design suggested and justified (10p). Clear description of quality measures and how they can be derived from the telemetry data (5p). The justification considers the amount of data transmitted or stored, how telemetry copes with rare events, and whether telemetry can detect both false positives and false negatives (5p).
* [ ] (optional) 10 bonus points: One risk analysis technique systematically applied to understand risks. Supporting evidence provided. Insights from applying the method discussed.

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class, under the following condition: *You may not work with anybody who you know well or who was on your team in a previous course or previous assignment (including I3).* To facilitate the search for team members, we post a link to a shared Google spreadsheet on Canvas.

If you work together as a team, you can either submit a joint solution or separate solutions on Gradescope. If you submit a joint solution, both team members will receive the same grade. If you submit separate solutions, those solutions may share text or code, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.