.. _use-cases-label:

Use Cases
*********

.. todo:: use cases need to be reviewed by advisory panel.

|SPARK| and the |SPARK tools| will continue the design goal of SPARK Pro (and previous iterations of the SPARK language and toolset) of making it easier to develop software with extremely low defect densities through a suite of analysis techniques that can be used selectively according to the development team's needs.

The following use cases develop this goal based on current usage, the results of the Hi-Lite project and ideas on how the current technology can potentially enhance the user experience.

Process and Plan
================

Step 1 - Define high-level use cases based on current segmentation matrix

Step 2 - Brainstorm additional high-level use cases
   * Raise TN for "ideas" (not discussion) (include template and example Use Case)
   * Categorise as "in" or "out" 

Step 3 - Revise segmentation matrix

Step 4 - Refine high-level use cases

Step 5 - Review segmentation matrix against refined use cases

Step 6 - Convert use cases into operational requirements



SPARK - Basic
=============

Milestone 1:

* :ref:`uc-check-subset`

Milestone 3:

* state abstraction

* interfaces (volatiles)

Milestone 4:

* Prove of absence of RTE

* :ref:`uc-analyse-data-flow`

* profile "restrictions"

* programs with incomplete bodies

* |SPARK| and Ada 2012 source (aka "hide")

* Accept" errors in code

Milestone |rel2+|:

* Analyse multi-tasking programs




SPARK - Information Flow
========================

Milestone 4:

* :ref:`uc-analyse-information-flow`

* Check security and safety policy 

  * includes lowering security level following encryption, 
  * needs to consider use of "ghost" variables and functions)

Milestone |rel2+|:

* Visualise information flow (slicing)



SPARK - Advanced Proof
======================

Milestone 1:

* Prove simple properties

* Prove complex properties

* Prove program contracts

* Automate proof of simple VCs

* Automate proof of complex VCs
    
* Manual proof of VCs

Milestone 4:

* Proof contract refinement

* Prove type invariants


Milestone |rel2+|:

* Prove generic packages (not instantiations)

* Proof of object oriented language constructs (e.g. Liskov Substitution Principle)


Integrating Proof and Test 
==========================

Milestone 1:

* Internally generate aspects

Milestone 5 or earlier:

* Execute/don't execute assertions

* Combine test and formal program verification



Support local development processes
===================================

Milestone 1:

* Proof summary file to summarise outstanding VCs

Milestone 3:

* Use a different compiler

Milestone 5 or earlier:

* Interface to alternative provers


Milestone |rel2+|:

* Qualify tools for use as a verification tool 

* Existing Ada 2005 code, want to add |SPARK| aspects in comments and analyse them (not build)

* Cache VCs to speed up re-analysis


Miscellaneous
=============

Milestone 1:

* :ref:`uc-internally-generate-aspects`


Milestone 3:

* Use Ada Containers


Milestone 4:

* Use Ada Libraries

* Experiment with advanced |SPARK tools|

Milestone |rel2+|:

* Write abstract derives, invisibly "generate" concrete derives

* Support debugging unproved VCs

* Report quantitative view of high-cohesion/low-coupling (size of derives)

* Access types to subprograms

* Replacement for redefining --# to support multiple models

* Ability to specify complex properties not expressible in SPARK

* Fix aspects automatically ("bless the annotations")

* :ref:`uc-internally-generate-aspects-and-bless`

* Interprocedural flow analysis (covers 178C "data and control coupling" coverage as identifies ineffective code)



The Use Cases
=============

.. _uc-check-subset:
.. include:: ../use-cases/check-subset.rst    

.. _uc-analyse-data-flow:
.. include:: ../use-cases/analyse-data-flow.rst    

.. _uc-internally-generate-aspects:
.. include:: ../use-cases/internally-generate-aspects.rst

.. _uc-internally-generate-aspects-and-bless:
.. include:: ../use-cases/internally-generate-aspects-and-bless.rst

.. _uc-analyse-information-flow:
.. include:: ../use-cases/analyse-information-flow.rst    
