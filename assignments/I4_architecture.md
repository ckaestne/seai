# Individual Assignment 4: Requirements and Architecture

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, we revisit the Dashcam scenario from I3 and discuss different deployment options.

Learning goals:
* Reason about qualities relevant to the deployment of an AI component in a system architecture
* Design measures to quantify system goals, design qualities, and telemetry feedback

## Scenario

The scenario is exactly the same as I3:

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

**Part 1: Deployment.** Compare four different design alternatives about how to deploy the system with regard to the eight qualities listed in the scenario. To that end, analyze whether the AI component(s) for recognizing a person in an image should be deployed (a) on the dashcam, (b) on a phone, (c) in the cloud, or (d) some other configuration you describe (e.g., hybrid or edge). Provide a short explanation and an architecture diagram for your fourth design.

Where possible estimate the impact of the different designs on the eight different qualities. You may want to do some Internet research about typical characteristics of various hardware and software components (e.g., storage capacity of dashcams, size of typical face recognition models, bandwidth of Bluetooth connections). You do not need to conduct precise measurements or estimate concrete values, but should inform your discussion with an understanding of the qualities in the context of the scenario (e.g., “solution A is better than solution B because of a bottleneck in Bluetooth bandwidth” or “privacy is better in solution C because customer data does not leave the device”). 

After understanding the four different designs, explicitly discuss the tradeoffs involved, which involves discussing the relative relevance of the qualities and the differences in qualities for the different solutions. Recommend one of the solutions.

**Part 2: Telemetry.** Suggest a design for telemetry to identify how well the system and the AI component(s) are performing in production. Be explicit about what data you would collect, what quality measure you use, and how you would use the collected data to compute the quality measure. Briefly justify your design and why it is appropriate in the context of the scenario. That discussion should cover at least (1) the amount of data transmitted or stored, (2) how it copes with rare events, and (3) whether it can detect both false positives and false negatives.


## Deliverable

Submit a report as a single PDF file to Gradescope that covers the following topics in clearly labeled sections (ideally each section starts on a new page):

1. **Analysis of deployment alternatives** (no page limit): Briefly describe the fourth deployment architecture considered and provide an architecture diagram. Then for each of the 4 deployment options discuss the 8 qualities listed above. A tabular representation (one column per deployment option, one row per quality) may be suitable, but other clearly structured formats are possible. Rough estimates or relative ratings with a brief explanation are sufficient as long as they are grounded and realistic in the scenario.
4. **Recommendation and justification of deployment architecture** (1 page max): Recommend a deployment architecture and justify this recommendation in terms of the relative relevance of the qualities and the tradeoffs among quality attributes.
5. **Telemetry** (1 page max): Suggest how telemetry should be selected, describe how quality would be measured from telemetry data, and briefly justify those decisions.


## Grading

The assignment is worth 100 points. For full credit, we expect:
* [ ] 10 points: Description of a fourth deployment architecture is included. 
* [ ] 10 points: An architecture diagram for the fourth deployment architecture is included and matches the description.
* [ ] 20 points: For each of the 4 design alternatives at least 4 quality attributes are analyzed. The analysis is plausible for the scenario.
* [ ] 10 points: For each of the 4 design alternatives all 8 quality attributes are analyzed plausibly. The analysis is plausible for the scenario.
* [ ] 10 points: Recommendation for a deployment decision provided and a justification for the decision is provided. 
* [ ] 10 points: The justification clearly makes tradeoffs among the discussed qualities and weighs the relative importance of the qualities to come to a conclusion supported by the analysis.
* [ ] 10 points: Telemetry design is suggested and described, describing the goal of the telemetry and what data is collected. 
* [ ] 10 points: The telemetry section contains a description of quality measures and how they can be derived from the telemetry data. 
* [ ] 10 points: The telemetry section contains a justification for the chosen approach. The justification considers (1) the amount of data transmitted or stored, (2) how telemetry copes with rare events, and (3) whether this form of telemetry can detect both false positives and false negatives.

## Groupwork option

In the current remote learning setting, we want to encourage collaboration and interaction among students. We therefore allow the options for this assignment to work together with *one* other student in the class. We recommend to work with the same suggested partner as in assignment I3. If you deviate from the recommended pairing, you may *not* work together with a student with whom you have worked together on a previous individual assignment.

If you work together as a team, you can either submit a joint solution or separate solutions on Gradescope. If you submit a joint solution, both team members will receive the same grade. If you submit separate solutions, those solutions may share text or code, but we will grade them separately. Always make sure that you indicate with whom you worked together, even if just for part of the assignment. 

Groupwork is optional. You may decide to work alone.

