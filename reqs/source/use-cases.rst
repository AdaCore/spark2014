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
   * Ideas and categorise as "in" or "out" 

Step 3 - Revise segmentation matrix

Step 4 - Refine high-level use cases

Step 5 - Review segmentation matrix against refined use cases

Step 6 - Convert use cases into operational requirements



SPARK Classic - Basic
=====================

    Check SPARK Classic "restrictions"

    Analyse programs with incomplete bodies

    Automate proof of absence of RTE

    Support state abstraction

    Analyse multi-tasking programs

    Combine |SPARK| and Ada 2012 source

.. _uc-check-subset:
.. include:: ../use-cases/check-subset.rst    

.. _uc-analyse-data-flow:
.. include:: ../use-cases/analyse-data-flow.rst    


SPARK Classic - Information Flow
================================

    Check security and safety policy

.. _uc-analyse-information-flow:
.. include:: ../use-cases/analyse-information-flow.rst    


SPARK Classic - Advanced Proof
==============================

    Manual proof of properties

    Automate proof of properties
    
    Refined-pre and refined-post

    Proof of object oriented language constructs (e.g. Liskov Substituion Principle)


Integrating Proof and Test 
==========================

    Execute/don't execute pre/post

    Combine test and formal program verification

Miscellaneous
=============

    Existing Ada 2005 code, want to add |SPARK| aspects in comments and analyse them (not build)

    Ability to specify complex properties not expressible in SPARK

    Replacement for redefining --# to support multiple models

    Fix aspects automatically ("bless the annotations")

    Report quantitative view of high-cohesion/low-coupling (size of derives)

    Write abstract derives, invisibly "generate" concrete derives

    Internally generate aspects

    Internally generate aspects and bless them

    Use Ada Containers

    Interprocedural flow analysis (covers 178C "data and control coupling" coverage)

    Support debugging unproved VCs

.. _uc-internally-generate-aspects:
.. include:: ../use-cases/internally-generate-aspects.rst

.. _uc-internally-generate-aspects-and-bless:
.. include:: ../use-cases/internally-generate-aspects-and-bless.rst


