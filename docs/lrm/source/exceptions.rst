Exceptions
==========

Exception Declarations
----------------------

No additions or restrictions

Exception Handlers
------------------

.. centered:: **Legality Rules**


1. Exception handlers are not permitted in |SPARK|.


Raise Statements
----------------

Raise statements are in |SPARK|, but must (as described below) be
provably never executed.

.. centered:: **Verification Rules**


1. A ``raise_statement`` introduces an obligation to prove that the statement
   will not be executed, much like the verification condition associated with

       ``pragma Assert (False);``

   [In other words, the verification conditions introduced for a raise
   statement are the same as those introduced for a run-time check
   which fails unconditionally.]

.. commented out since raise expression are not part of the language yet
   A raise expression (see Ada AI12-0022
   for details) introduces a similar obligation to prove that the
   expression will not be evaluated.]


Exception Handling
------------------

No additions or restrictions but exception handlers are not permitted in |SPARK|.

The Package Exceptions
~~~~~~~~~~~~~~~~~~~~~~

Pragmas Assert and Assertion_Policy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**


1. The pragmas ``Assertion_Policy``, ``Suppress``, and ``Unsuppress`` are
   allowed in |SPARK|, but have no effect on the generation of verification
   conditions. [For example, an array index value must be shown to be in
   bounds regardless of whether Index_Check is suppressed at the point
   of the array indexing.]


2. The following |SPARK| defined aspects and pragmas are assertions and
   their *Boolean_*\ ``expressions`` are assertion expressions:

   * Assert_And_Cut;
   * Assume;
   * Contract_Cases;
   * Default_Initial_Condition;
   * Initial_Condition;
   * Loop_Invariant;
   * Loop_Variant; and
   * Refined_Post.

   There is an *assertion_*\ ``aspect_mark`` for each of these aspects
   and pragmas with the same identifier as the corresponding aspect or
   pragma. In addition, Ghost is a |SPARK| defined
   *assertion_*\ ``aspect_mark``.

   An implementation may introduce further implementation defined
   *assertion_*\ ``aspect_marks`` some of which may apply to groups of
   these assertions.
