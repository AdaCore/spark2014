************
Introduction
************

.. Text of intro is copied from the Introduction of SPARK 2014 RM.

|SPARK| is a programming language and a set of verification tools designed to
meet the needs of high-assurance software development.  |SPARK| is based on Ada
2012, both subsetting the language to remove features that defy verification,
but also extending the system of contracts and "aspects" to support modular,
formal verification.

The new aspects support abstraction and refinement and facilitate deep static
analysis to be performed including information-flow analysis and formal
verification of an implementation against a specification.

|SPARK| is a much larger and more flexible language than its predecessor
SPARK 2005. The language can be configured to suit a number of application
domains and standards, from server-class high-assurance systems (such as
air-traffic management applications), to embedded, hard real-time, critical
systems (such as avionic systems complying with DO-178C Level A).

A major feature of |SPARK| is the support for a mixture of proof and
other verification methods such as testing, which
facilitates the use of unit proof in place of unit testing; an approach now
formalized in DO-178C and the DO-333 formal methods supplement.
Certain units may be formally proven and other units validated through
testing.

|SPARK| is supported by various tools in the |GNAT Pro| toolsuite:

* the GNAT compiler
* the GPS integrated development environment
* the GNATtest tool for unit testing harness generation
* the |GNATprove| tool for formal program verification

The remainder of this document is structured as follows:

* Chapter :ref:`introduction to spark` provides an overview of the |SPARK|
  language.
* Chapter :ref:`getting started` shows how to get started with the language and
  toolset by means of a simple example program.
* Chapter :ref:`formal verification with gnatprove` describes the use of the
  |GNATprove| formal verification tool.
* Chapter :ref:`usage scenarios for formal verification` lists the main usage
  scenarios for formal verification.
* Chapter :ref:`proof and test` explains how to combine the results of formal
  verification and classical verification by testing.

