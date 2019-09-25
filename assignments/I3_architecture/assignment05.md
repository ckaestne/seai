# Individual Assignment 3: Architecture

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will reason about the architecture of a system beyond "just" choosing the right AI component. 

Learning goals:
* Model a system's architecture 
* Reason about tradeoffs in system design
* Identify relevant qualities and how to measure them.

## Scenario

[Dashcams](https://en.wikipedia.org/wiki/Dashcam) are getting more popular and are broadly installed in many vehicles already. As a manufacturer of dashcams, you want to develop features that distinguish your dashcams from those of your competitors. As one project, you work with a non-profit organization on *child safety*: The project's goal is to use dashcam footage to locate children reported missing. However, instead of broadcasts, such as [Amber alerts](https://en.wikipedia.org/wiki/Amber_alert) your products will allow to search for those children in video recordings made by the dashcam.

In designing such system, there are many concerns, such as:
* Your dashcams do not have direct internet access, but they can communicate over USB, Bluetooth or Wifi with phones, cars, and wifi-hotspots.
* The dashcams may run on battery but are usually connected to the car's power supply. Their processing power differs from model to model.
* Searches are coordinated with the authorities and the non-profit organization, though you could imagine less strict requirements as for Amber alerts. They are likely not very frequent in any given area. For Amber alerts, [official statistics](https://amberalert.gov/statistics.htm) report nearly 1 alert per day nationwide.
* Faster reports of sightings are more useful to the authorities.
* You suspect users may be worried about privacy and charge for data.
* You recently hear everywhere, including press and consultants, how exciting the future of [Edge computing](https://en.wikipedia.org/wiki/Edge_computing) rather than Cloud computing is going to be and wonder whether you should explore that. You wouldn't be opposed to thinking about partnering with other organizations to, say, install hardware in gas stations or drive throughs.

## Tasks

Think about how you would design such as system. What would be the main components (AI or not), where might they be located? Consider alternative designs.


You are concerned at least about the following qualities:
* Latency between reporting a child missing (with numerous pictures) to receiving potential matches from dashcam users
* Number of false positives and false negatives
* Ability to observe how well the system works in production
* Scalability and cost of running the infrastructure with many users across many countries
* Running costs for users
* Difficulty of changing and updating the system to meet new requirements or incorporate better technology
* Privacy
* Development cost, technical complexity of the solution, maintainability


We suggest you follow these steps:

1. Identifying and ranking all relevant qualities that are important for your design
2. Sketch an initial architecture diagram with which you can reason about the qualities of interest. It is often better to have multiple specialized diagrams for different qualities, rather than a single complicated diagram.
3. Estimate important properties and constraints relevant for the design of the system, such as bandwidth needed or available between two components. You may want to do some Internet research about typical characteristics of various hardware and software components (e.g., storage capacity of dashcams, size of typical face recognition models, bandwidth of Bluetooth connections).
4. Refine your architecture plans as needed and justify your final design


## On Notation

You have a lot of flexibility in how you document architectures. Box and connector diagrams are common. For different qualities you likely want to show different views of the system, in which boxes and connectors may have different meanings. Always include a legend for each diagram.

There are numerous free and commercial online and offline tools to draw diagrams, such as [Dia](http://dia-installer.de/) and [draw.io](https://www.draw.io/). Also photographs of whiteboard drawings are acceptable if they are clearly readable.


## Deliverable

Submit a report as a single PDF file to Canvas that describes and justifies your architecture.

The report should have the following clearly labeled sections:

1. **Qualities** (.5 pages max): Ranking of the qualities of interest and a brief justification of why the top 3 qualities are the most important qualities
2. **Architecture diagrams**: One or more diagrams of the suggested system architecture, that allow you to reason about your top 3 qualities. All diagrams need to include a legend. Explicitly indicate which diagram(s) are suitable for reasoning about your top 3 qualities.
3. **Architecture justification** (2 pages max): Justify your architectural design, explain your key choices (such as, where to locate AI components, how to distribute the system, where to store data, how to collect telemetry) and why they are better than alternatives. Refer to specific estimates for quality measures (e.g., operating costs, bandwidth, file sizes, latency) to justify your decision. Where possible, provide sources for your estimates.
4. **Uncertainty analysis** (.5 pages max): Given that you suggested this architecture on estimates rather than specific measurements, discuss your confidence in the estimates and whether your architecture decision would change if actual numbers were different from the estimates. Outline which properties you would try to measure (e.g., with a prototype) before committing on an architecture decision and how.


## Grading

The assignment is worth 100 points. For full credit, we expect:
* [ ] Reasonable ranking of qualities and plausible justification (10 pt)
* [ ] Clean and understandable architecture diagrams, that relate to at least 3 quality attributes (30 points)
* [ ] Plausible architecture justification that discusses alternatives and explicitly refers to estimated qualities (35 points)
* [ ] Discussion of how uncertainty in estimates might affect architectural choices and how more accurate data can be collected (15 pt)
* [ ] A clearly structured, well written document (10 pt)

## Hints

Some architectural diagram of the solution will likely refer to different hardware locations. Some architectural diagram will likely include storage locations for images, and processes (ML and non-ML for processing). It might be useful to think about multiple stages of image recognition with different tradeoffs. It may be useful to think about storage, buffering, or queuing videos at multiple stages rather than trying to process a single stream. False positives and false negatives may not be equally bad. There might be more than one path a video could take from a dashcam to a central server.