# Individual Assignment 3: Architecture

(17-445/17-645 Machine Learning in Production / AI Engineering)

## Overview

In this assignment, we return to the Dashcam scenario and explore architecture and alternatives of different deployment options.

Learning goals:
* Reason about qualities relevant to the deployment of an ML component in a system architecture
* Design measures to quantify system goals, design qualities, and telemetry feedback

## Tasks

Return to the scenario description of I3. Carefully read the list of qualities discussed in the scenario description and make sure you understand the concepts of interest here.

**Task 1: Deployment.** Compare four different design alternatives about how to deploy the system with regard to the eight qualities listed in the scenario. To that end, analyze whether the ML component(s) for recognizing a person in an image should be deployed (a) on the dashcam, (b) on a phone, (c) in the cloud, or (d) some other configuration you describe (e.g., hybrid or edge). Provide a short explanation and an architecture diagram for your fourth design.

Where possible estimate the impact of the different designs on the eight different qualities listed in the scenario description. You may want to do some Internet research about typical characteristics of various hardware and software components (e.g., storage capacity of dashcams, size of typical face recognition models, bandwidth of Bluetooth connections). You do not need to conduct precise measurements or estimate concrete values, but should inform your discussion with an understanding of the qualities in the context of the scenario (e.g., “solution A is better than solution B because of a bottleneck in Bluetooth bandwidth” or “privacy is better in solution C because customer data does not leave the device”). 

After understanding the four different designs, explicitly discuss the tradeoffs involved, which involves discussing the relative relevance of the qualities and the differences in qualities for the different solutions. Recommend one of the solutions.

**Task 2: Telemetry.** Suggest a design for telemetry to identify how well (a) the system and (b) the ML component(s) are performing in production. Be explicit about what data you would collect, what quality measure you use, and how you would use the collected data to compute the quality measure. Briefly justify your design and why it is appropriate in the context of the scenario. That discussion should cover at least (1) the amount of data transmitted or stored, (2) how it copes with rare events, and (3) whether it can detect both false positives and false negatives.

## Deliverable

Submit a report as a single PDF file to Gradescope that covers the following topics in clearly labeled sections (ideally each section starts on a new page):

1. **Fourth deployment design** (1 page max): Briefly describe the fourth deployment architecture considered and provide an architecture diagram. 
1. **Analysis of deployment alternatives** (4 pages max): For each of the 4 deployment options discuss the 8 qualities listed above. We recommend that you start a bullet list with 4 elements (one for each deployment option) for each of the 8 qualities, but tabular or other representations are also possible. Rough estimates or relative ratings with a brief explanation are sufficient as long as they are grounded and realistic in the scenario.
2. **Recommendation and justification of deployment architecture** (1 page max): Recommend a deployment architecture and justify this recommendation in terms of the relative relevance of the qualities and the tradeoffs among quality attributes.
3. **Telemetry** (1 page max): Suggest how telemetry should be selected for a system quality and a model quality and describe how quality would be measured from telemetry data, and briefly justify those decisions.

Page limits are recommendations and not strictly enforced. You can exceed the page limit if there is a good reason. We prefer precise and concise answers over long and rambling ones.

## Grading

The assignment is worth 100 points. For full credit, we expect:

* [ ] 10 points: Description of a fourth deployment architecture is included. 
* [ ] 10 points: An architecture diagram for the fourth deployment architecture is included and matches the description.
* [ ] 20 points: For each of the 4 design alternatives at least 4 quality attributes are analyzed. The analysis is plausible for the scenario.
* [ ] 10 points: For each of the 4 design alternatives all 8 quality attributes are analyzed plausibly. The analysis is plausible for the scenario.
* [ ] 10 points: Recommendation for a deployment decision provided and a justification for the decision is provided. 
* [ ] 10 points: The justification clearly makes tradeoffs among the discussed qualities and weighs the relative importance of the qualities to come to a conclusion supported by the analysis.
* [ ] 10 points: The telemetry section describes what telemetry data is collected and how. It is plausible in the scenario that this data can be collected.
* [ ] 10 points: The telemetry section contains a description of two quality measures, one for the system and one for the model. The section describes how the metrics are operationalized with the telemetry data in a way that is clear enough for a third party to independently implement.
* [ ] 10 points: The telemetry section contains a justification for the chosen approach. The justification considers (1) the amount of data transmitted or stored, (2) how telemetry copes with rare events, and (3) whether this form of telemetry can detect both false positives and false negatives.
