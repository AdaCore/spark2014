.. _glossary:

Glossary
========

The |SPARK| Reference Manual uses a number of technical terms to
describe its features and rules.  Some of these terms are well known
others are less well known or have been defined within this document.
In the glossary given here the less well known terms and those defined
by |SPARK| are listed with a brief explanation to their meaning.


- Data-Flow analysis is the process of collecting information about
  the way the variables are used and defined in the program. In
  particular, in |SPARK| it is used to detect the use of uninitialized
  variables and state abstractions.

- Executable semantics

- Flow analysis is a term used to cover both data-flow and
  information-flow analysis.

- Formal Analysis is a term used to cover flow analysis and formal
  verification.

- Formal Verification, in the context of hardware and software
  systems, is the act of proving or disproving the correctness of
  intended algorithms underlying a system with respect to a certain
  formal specification or property, using formal methods of
  mathematics.  In |SPARK| this entails proving the implementation of
  a subprogram against its specification given its precondition using
  an automatic theorem prover (which may be part of the |SPARK|
  toolset.  The specification may be given by a postcondition or
  assertions or may be implicit from the definition of Ada when
  proving absence of run-time exceptions (robustness property).

- Formal verification of functional properties is the proof that an
  implementation meets its specification given as an assertion
  expression such as a postcondition.

- Formal verification of robustness properties, in Ada terminology, is
  the proof that certain predefined checks such as the ones that raise
  Constraint_Error will never fail at run-time.

- Information-Flow analysis in an information theoretical context is
  the transfer of information from a variable x to a variable y in a
  given process, that is x depends on y. Not all flows may be
  desirable. For example, a system shouldn't leak any secret
  (partially or not) to public observers.  In |SPARK| information-flow
  analysi is used to detect ineffective statements and check that the
  implementation of a subprogram satisfies its Global aspect and
  Depends aspect (if it is present).  It may also be used for security
  analysis in |SPARK|.
  

- Refinement 


- State abstraction


.. todo:: Extend this section.
