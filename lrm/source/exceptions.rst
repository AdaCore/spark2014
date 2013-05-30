Exceptions
==========

Language Definition
^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

There is no additional syntax associated with exceptions in |SPARK|.

.. centered:: **Legality Rules**

#. Exception handlers are not in |SPARK|. [Exception declarations (including
   exception renamings) are in |SPARK|. Raise statements are in |SPARK|,
   but must (as described below) be provably never executed.]

#. Raise expressions are not in |SPARK|; for a raise statement to be in
   |SPARK|, it must be immediately enclosed by an if statement
   which encloses no other statement. [It is intended that these two
   rules will be relaxed at some point in the future (this is why
   raise expressions are mentioned in the Verification Rules section below).]

.. centered:: **Static Semantics**

There are no additional static semantics associated with exceptions in |SPARK|.

.. centered:: **Dynamic Semantics**

There are no additional dynamic semantics associated with exceptions in |SPARK|.

.. centered:: **Verification Rules**

#. A ``raise_statement`` introduces an obligation to prove that the statement
   will not be executed, much like the proof obligation associated with

       ``pragma Assert (False);``

   [In other words, the proof obligations introduced for a raise statement
   are the same as those introduced for a runtime check which fails
   unconditionally. A raise expression (see Ada AI12-0022 for details) introduces
   a similar obligation to prove that the expression will not be evaluated.]

#. The pragmas ``Assertion_Policy``, ``Suppress``, and ``Unsuppress`` are
   allowed in |SPARK|, but have no effect on the generation of proof
   obligations. [For example, an array index value must be shown to be in
   bounds regardless of whether Index_Check is suppressed at the point
   of the array indexing.]
