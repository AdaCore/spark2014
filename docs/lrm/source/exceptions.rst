Exceptions
==========

Exception Declarations
----------------------

No additions or restrictions

Exception Handlers
------------------

Exception handlers are supported in SPARK, but the verification rules associated
to language mandated checks and contracts make it so that only exceptions raised
in actual raise statements can be handled.

.. container:: heading

   Legality Rules


1. Exception handlers shall not have a choice parameter.


Raise Statements and Raise Expressions
--------------------------------------

Raise statements and raise expressions are in |SPARK|. An exception is said to
be *expected* if it is covered by a choice of an exception handler in an
enclosing handled sequence of statements, or if its enclosing entity is a
procedure body and the exception is covered by a choice in its Exceptional_Cases
aspect whose associated consequence is not statically False.

As described below, all raise expressions must be provably never executed.
The same holds true for raise statements if they raise unexpected exceptions.

.. container:: heading

   Verification Rules

1. A ``raise_expression`` introduces an obligation to prove that the expression
   will not be evaluated, much like the verification condition associated with

       ``pragma Assert (False);``

   [In other words, the verification conditions introduced for a raise
   expression are the same as those introduced for a run-time check
   which fails unconditionally.]

2. A ``raise_statement`` introduces an obligation to prove that the exception
   raised is expected. [For raise statements with an exception name which is
   unexpected, this amounts to proving that the statement will not be executed.]

Exception Handling
------------------

No additions or restrictions.

The Package Exceptions
~~~~~~~~~~~~~~~~~~~~~~

Pragmas Assert and Assertion_Policy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. container:: heading

   Legality Rules


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
