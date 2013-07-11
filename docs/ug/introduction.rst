************
Introduction
************

.. Text of intro is copied from the Introduction of SPARK 2014 RM.

|SPARK| is a programming language and a set of verification tools designed to
meet the needs of high-assurance software development.  |SPARK| is based on Ada
2012, both subsetting the language to remove features that defy verification,
but also extending the system of contracts and "aspects" to support modular,
formal verification.

|SPARK| is a much larger and more flexible language than its predecessor
SPARK 2005. The language can be configured to suit a number of application
domains and standards, from server-class high-assurance systems (such as
air-traffic management applications), to embedded, hard real-time, critical
systems (such as avionic systems complying with DO-178C Level A).

|SPARK| is supported by various tools in the |GNAT Pro| toolsuite:

* the GNAT compiler
* the GPS graphical development environment
* the GNATtest tool for unit testing harness generation
* the |GNATprove| tool for formal program verification

.. Annotations are mentioned in the next sentence but haven't been introduced yet.

A crucial feature of |GNATprove| is that it interprets annotations exactly like
they are interpreted at run time during tests. In particular, their executable
semantics includes the verification of run-time checks, which can be verified
statically with |GNATprove|. |GNATprove| also performs additional verifications
on the specification of the expected behavior itself, and its correspondence to
the code.

.. Rewrite this to match the new structure.

* Chapter :ref:`introduction to spark` provides a detailed introduction to the
  |SPARK| language.
* Chapter :ref:`formal verification with gnatprove` describes the use of the
  |GNATprove| formal verification tool.
* Chapter :ref:`usage scenarios for formal verification` lists the main usage
  scenarios for formal verification.
* Chapter :ref:`proof and test` explains how to combine the results of formal
  verification and classical verification by testing.

