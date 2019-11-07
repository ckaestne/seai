# Individual Assignment 5: Security

(17-445/645 Software Engineering for AI-Enabled Systems)

## Overview

In this assignment, you will get practice with building a threat model for an AI-enabled system and devising defenses against potential attacks.

Learning goals:
* Understand emerging threats to AI-enabled systems.
* Apply a threat modeling process to identify potential security threats in a system and devise corresponding mitigations. 

## Tasks and Questions

Suppose that you are part of a startup that is building a new, revolutionary home assistant robot called _Fay_. Fay is a small, humanoid robot (similar in appearance to [Pepper from SoftBank](https://en.wikipedia.org/wiki/Pepper_(robot))) that is capable of moving around obstacles in a home on its own. Fay interacts with the members of a household through an AI-enabled intelligent speech dialogue system. In addition to answering questions (e.g., "what's the weather like today?") and assisting with tasks ("add eggs to my shopping list"), Fay is capable of engaging in different types of interactions depending on the characteristics of the person that it is currently interacting with. For instance, if Fay comes in contact with a child in the household, it will switch to a level of voice dialogue that is suitable for young children (using simple, short phrases with a safe-for-children, sanitized vocabulary). Similarly, if Kay identifies that a stranger that has entered the house, it may alert the head of the household or, if the former is unavailable, contact the local law enforcement to notify of a potential break-in.

Fay relies on AI for at least two different types of tasks: one for perception (i.e., using face recognition to identify the human user that it interacts with) and another one for speech dialogues (parsing human speech and generating appropriate responses). Another standout feature of Fay is that it continuously learns to improve on its interaction with humans by learning from all other Fay's that are deployed around the world. From time to time, each Fay will wirelessly upload a log of its interactions with humans to a cloud-based learning system, which then re-trains the models and pushes the update back onto the Fay's. Through this distributed, collaborative learning process, Fay will become capable of performing a wider range of interactions over time.

Unfortunately, the investors of your company have become wary of recent incidents where malicious users have sabotaged AI-enabled systems (one of the most notable ones being the [Tay chatbot from Microsoft](https://en.wikipedia.org/wiki/Tay_(bot))). Before they can finalize their investment, they would like to see strong evidence that Fay is designed to be secure against potential attacks and provide safe interactions with household members. As the lead software engineer at the company, you've been tasked with building a threat model and devise a list of mitigations against potential threats.

Answer the questions below. Concise and precise answers with a clear argument and structure are preferred over long, meandering collections of sentences.

Questions:

**Question 1:** List at least two security requirements for this system. For each of them, indicate whether it is a confidentiality, integrity, or availability requirement.

**Question 2:** Construct an architecture diagram with which you can reason about potential security threats on the system. Show key system components, connections between them (e.g., data flow, invocation of an API function), and a trust boundary that indicates which of the components may be malicious. Be sure to include a legend.

Your diagram must include, at minimum, the following components and connections between them: (1) an ML-based component for perception, (2) an ML component for speech dialogue, (3) a cloud-based learning component that periodically re-trains a model, (4) a component that stores the log of a Fay's interaction with humans and uploads it to the cloud, and (5) a human user that interacts with Fay.

**Question 3:** For each of the potentially malicious actors that you identified in Question 2, state its goal(s): What is it trying to achieve by carrying out an attack? Describe how the attacker's goals are related to the requirements that you identified in Question 1. 

**Question 4:** Identify a list of actions (i.e., threats) that an attacker may perform in order to achieve its goals. In particular, for each connection that you identified in Question 2, consider the six categories of threats from the STRIDE approach (i.e., spoofing, tampering, repudiation, information disclosure, denial of service, and elevation of privilege) as well as ML-specific attacks discussed in class (poisoning and evasion attacks). Note that not all of these threats may be relevant to the security requirements of this system; include only those that are relevant.

**Question 5:** For at least three of the threats that you identified in Question 4, describe a potential mitigation strategy.

* Hint: See [this article](https://blogs.msdn.microsoft.com/larryosterman/2007/09/05/threat-modeling-again-stride-mitigations/) for common mitigations to threats in STRIDE.

**Question 6:** If the system is implemented with mitigations against the threats you've identified, does this guarantee that the system will be completely secure? Based on your experience with Questions 1 to 5, discuss at least two fundamental limitations of threat modeling.

Submit your answers as a single PDF document to Canvas by [see Canvas]. Make sure your document is clearly structured, such that it is recognizable which answer belongs to which question.

## Grading

The assignment is worth 100 points. For full credit, we expect:
* Q1. Identification of security requirements (10 pt)
* Q2. Construction of an architecture diagram that sufficiently enables reasoning about potential threats (25 pt)
* Q3. Description of attacker goals (10 pt)
* Q4. Identification of potential threats on the system (25 pt)
* Q5. Discussion of mitigation strategies (10 pt)
* Q6. Discussion of limitations of threat modeling (10 pt)
* A clearly structured, well written document (10 pt)
