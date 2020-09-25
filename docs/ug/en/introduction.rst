************
Introduction
************

.. Text of intro is copied from the Introduction of SPARK RM.

SPARK is a programming language and a set of verification tools designed
to meet the needs of high-assurance software development.  SPARK is based
on Ada, both subsetting the language to remove features that defy
verification, but also extending the system of contracts and aspects to support
modular, formal verification.

The new aspects support abstraction and refinement and facilitate deep static
analysis to be performed including flow analysis and formal verification of an
implementation against a specification.

The current version of SPARK, sometimes referred to as SPARK 2014, is a much
larger and more flexible language than its predecessor SPARK 2005. The language
can be configured to suit a number of application domains and standards, from
server-class high-assurance systems (such as air-traffic management
applications), to embedded, hard real-time, critical systems (such as avionic
systems complying with DO-178C Level A).

A major feature of SPARK is the support for a mixture of proof and other
verification methods such as testing, which facilitates in particular the use
of unit proof in place of unit testing; an approach now formalized in DO-178C
and the DO-333 formal methods supplement.  Certain units may be formally proven
and other units validated through testing.

SPARK is supported by various tools in the |GNAT Pro| toolsuite:

* the GNAT compiler
* the GNAT Studio integrated development environment
* the GNATtest tool for unit testing harness generation
* the |GNATprove| tool for formal program verification

The remainder of this document is structured as follows:

* :ref:`Installation of GNATprove` goes through the installation steps on
  different platforms.
* :ref:`Identifying SPARK Code` describes the various means to identify the
  part of the program in |SPARK| that should be analyzed.
* :ref:`Overview of SPARK Language` provides an overview of the |SPARK|
  language.
* :ref:`SPARK Tutorial` gives an introduction
  to writing, testing and proving |SPARK| programs.
* :ref:`Formal Verification with GNATprove` describes the use of the
  |GNATprove| formal verification tool.
* :ref:`Applying SPARK in Practice` lists the main objectives and project
  scenarios for using |SPARK|.
