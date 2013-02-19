Introduction
============

Background
----------

|SPARK| is a programming language and a set of verification tools
designed to meet the needs of high-assurance software development.
|SPARK| is based on Ada 2012, both subsetting the language to remove
features that defy verification, but also extending the system of
contracts and "aspects" to support modular, formal verification.

|SPARK| is a much larger and more flexible language than its
predecessor SPARK 2005. The language can be configured to suit
a number of application domains and standards, from server-class
high-assurance systems (such as air-traffic management applications),
to embedded, hard real-time, critical systems (such as avionic
systems complying with DO-178C Level A).


Purpose
-------

The features of |SPARK| will evolve as the project develops, some are very mature but others will be discovered as the project progresses. This document will capture features in use cases and then derive from these high-level requirements, satisfaction arguments and specification statements. During the development of |SPARK| the use cases will help direct development and be tested informally during milestone integration.  When the |SPARK tools| require certification and the scope of certification is clear, the specification statements will be verified.

For this reason, during the development of |SPARK| the :ref:`use-cases` section should be read first. During certification the document sections should be read in order.


Scope
-----

These requirements cover all expected uses of |SPARK| and as such affect the language definition, tools and their use to meet certification goals.

Structure
---------

#. Introduction: this section

#. :ref:`context` presents an extended context diagram showing all direct and indirect stakeholders of |SPARK|.

#. :ref:`reqs` presents the high-level requirements of |SPARK| and presents for each a satisfaction argument.

#. :ref:`specification` presents the specification statements that, together with domain knowledge, cause the requirements to be met.

#. :ref:`use-cases` presents the use cases that support the requirements and specification statements.

Glossary
--------

Within this document the following definitions are used:

* *Machine*: The machine is the collection of artefacts that are being developed under |SPARK| to bring about a desired change in the *world*.
* *World*: The world is the operational context in which the *machine* operates.
* *Requirement*: A requirement is a desired property of the *world*. 
* *Specification*: A specification is a statement of how the *machine* or some part of it behaves. 
* *Domain Knowledge*: Domain knowledge is an artefact of the *world* that is always true e.g. the sun sets every day.

Within this document, the *machine* is always referred to as |SPARK|.


