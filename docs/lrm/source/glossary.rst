Glossary
========

The |SPARK| Reference Manual uses a number of technical terms to
describe its features and rules.  Some of these terms are well known
others are less well known or have been defined within this document.
In the glossary given here the less well known terms and those defined
by |SPARK| are listed with a brief explanation to their meaning.

.. index:: data-flow analysis

- Data-flow analysis is the process of collecting information about
  the way the variables are used and defined in the program. In
  particular, in |SPARK| it is used to detect the use of uninitialized
  variables and state abstractions.

.. index:: executable contracts; executable semantics

- Executable semantics is the definition of what it means for a construct to be
  executed at run-time. In |SPARK|, most contracts have executable semantics,
  which means in particular that they can halt execution by raising an
  exception if some error condition occurs.

.. index:: flow analysis

- Flow analysis is a term used to cover both data-flow and
  information-flow analysis.

.. index:: formal verification

- Formal Verification, in the context of hardware and software
  systems, is the act of proving or disproving the correctness of
  intended algorithms underlying a system with respect to a certain
  formal specification or property, using formal methods of
  mathematics.  In |SPARK| this entails proving the implementation of
  a subprogram against its specification given its precondition using
  an automatic theorem prover (which may be part of the |SPARK|
  toolset.  The specification may be given by a postcondition or
  assertions or may be implicit from the definition of the program when
  proving absence of run-time exceptions (robustness property).

.. index:: information-flow analysis

- Information-flow analysis in an information theoretical context is the
  transfer of information from a variable x to a variable y in a given process,
  that is y depends on x. Not all flows may be desirable. For example, perhaps
  the behavior of one part of a system is intended to be completely independent
  of the state of another part so that information flow from the latter part to
  the former would indicate a design error. Or a system shouldn't leak any
  secret information to public observers.  In |SPARK| information-flow analysis
  is used to detect useless statements and check that the implementation of a
  subprogram satisfies its Global aspect and Depends aspect (if they are
  present).  It may also be used for security analysis in |SPARK|.
