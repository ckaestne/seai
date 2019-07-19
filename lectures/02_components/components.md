---
author: Christian Kaestner
title: "17-445: Components of an AI-Enabled System"
semester: Fall 2019
footer: "17-445 Software Engineering for AI-Enabled Systems, Christian Kaestner"
---  

# Components of an AI-Enabled System

Christian Kaestner

<!-- references -->

Required reading: Hulten, Geoff. "Building Intelligent Systems: A Guide to Machine Learning Engineering." (2018), Chapters 2 and 5.

---

# Learning Goals

* Describe the components of a typical machine learning pipeline and their responsibilities and challenges
* Describe the typical components relating to AI in an AI-enabled system and typical design decisions to be made
* Illustrate the design space for AI-enabled systems for a given sample system

---
# When to use AI?
----
## When to use AI?

* Big problems, requiring lots of work
* Open-ended problems, continuing to grow over time
* Time-changing problems, where the right answer changes over time
* Intrinsically hard problems, pushing boundaries of what's considered possible

----

## Use of AI?

![stock exchange](stockexchange.jpg)
<!-- .element: class="stretch" -->

(CC BY-NC 2.0 [Travel Aficionado](https://www.flickr.com/photos/travel_aficionado/2396814840)

Notes: 
* Should it be used for the display panel of a stock exchange?
* For the bookkeeping and trading algorithms that determine prices and sign trades?
* For price prediction and automated trading?


----

## Use of AI?

![stock exchange](plane.jpg)
<!-- .element: class="stretch" -->

Picture by [David Mark](https://pixabay.com/users/12019-12019/?utm_source=link-attribution&amp;utm_medium=referral&amp;utm_campaign=image&amp;utm_content=100624)

---

## Display panel for stock exchange?

![stock exchange](stockexchange.jpg)
<!-- .element: class="stretch" -->

(CC BY-NC 2.0 [Travel Aficionado](https://www.flickr.com/photos/travel_aficionado/2396814840)