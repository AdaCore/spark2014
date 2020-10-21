.. _External Axiomatizations:

External Axiomatizations
========================

What is it?
-----------
It is a feature of the |SPARK| toolset that allows to manually supply a WhyMl
translation for the public specification of a library level package that is in
|SPARK|. This feature is still experimental.

Why is it useful?
-----------------
- For features that cannot easily be described using contracts, like
  transitivity, counting, or summation
- To link functions to the logic world, like trigonometry functions

How does it work?
-----------------
- To say that a library package has an external axiomatization, we annotate it
  using::

    pragma Annotate (GNATprove, External_Axiomatization);

- These packages should have SPARK_Mode On on their public specification and
  SPARK_Mode Off on their private part.
- The WhyMl translation for the package should be stored in a subdirectory
  named _theories of the proof directory specified for the project.

What should the translation look like?
--------------------------------------
- For each publicly visible entity E in the package P, it should provide the
  same elements (types as well as logic and program functions) as the automatic
  translation, all grouped in one single module named P__e. For example, the
  module for a function F should provide both a logic function declaration named
  f__logic and a program function declaration named f.
- For most types, a model module in defined in ada__model.mlw that can be cloned
  to get most of the required declarations.
- The manual translation may use any type, constant and function that is visible
  from the Ada package declaration.
- A good way to start an axiomatization file on a package is to launch the
  toolset on it and copy paste the modules created for each entity of the
  package. A WhyMl file created by the tool on a package P contains a module for
  every declaration visible from it, only declarations from P itself should be
  copied. The generated file usually contains two modules for each entity, one
  named P__e and one named P__e__axiom. Both should be put together in P__e for
  the manual translation. The toolset will replace statically known expressions
  with their value. Beware that they might be architecture dependent.

Example
-------
For example, let us consider the following package, stored in a file sum.ads,
providing a summation function for slices of arrays of integers:

.. literalinclude:: /examples/tests/sums/sums.ads
   :language: ada
   :linenos:

We can provide the following Why3 translation for it, that we should store in a
file named sum.mlw:

.. literalinclude:: /examples/tests/sums/proof/_theories/sums.mlw
   :language: none
