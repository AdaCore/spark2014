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

   Syntax

A pragma Assert might contain one or several associations of a check expression
and an optional message string:

::

   simple_assert_params ::= [Check =>] boolean_expression[, [Message =>] string_expression]

   level_assert_params ::= assertion_level => (simple_assert_params)[, level_assert_params]

   assert_params ::= simple_assert_params | level_assert_params

   pragma Assert (assert_params);

An assertion level might be used instead of an assertion aspect mark inside a
pragma Assertion_Policy:

::

   assertion_aspect_mark_or_level ::= assertion_aspect_mark | assertion_level

   pragma Assertion_Policy (assertion_aspect_mark_or_level => policy_identifier
   {, assertion_aspect_mark_or_level => policy_identifier});

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

.. container:: heading

   Static Semantics

3. A pragma Assertion_Policy that associates the policy_identifier Check with an
   assertion level also applies to all assertion levels it depends on.
   [Ghost code of a given level can reference ghost
   entities of levels it depends on. To be able to execute ghost code of
   a given level, all the levels it depends on need to also be enabled.]

4. A pragma Assertion_Policy that associates the policy_identifier Ignore with
   an assertion level also applies to all assertion levels that depend on it.
   [Ghost code of a given level can be referenced from ghost entities of levels
   that depend on it. If a given assertion level is disabled, then the levels
   that depend on it should also be disabled as they might reference disabled
   entities.]

5. To determine the assertion policy applicable to a ghost entity, an assertion
   expression, or a specification aspect associated with the Runtime assertion
   level or with an assertion level depending on the Static assertion level,
   pragmas Assertion_Policy that apply to named assertion aspects are ignored.
   [The assertion policy applicable to ghost entities, assertion expressions,
   and specification aspects associated with the Runtime assertion policy is
   always Check and the assertion policy applicable to ghost entities, assertion
   expressions, and specification aspects associated with assertion levels
   depending on the Static assertion level is always Ignore.]

6. To determine the assertion policy applicable to a ghost entity, an assertion
   expression, or a specification aspect associated with an assertion level
   other than the Runtime assertion level or an assertion level depending on the
   Static assertion level, the last pragma Assertion_Policy that
   applies to either the corresponding named assertion aspects or the assertion
   level associated with the ghost entity, assertion expression, or
   specification aspect in the specific region should be considered.

7. If they occur in a pragma Assertion_Policy, the Runtime assertion level shall
   always be associated with the Check policy identifier and the Static
   assertion level or levels that depend on it shall always be associated with
   the Ignore policy identifier.

Pragma Assertion_Level
~~~~~~~~~~~~~~~~~~~~~~

An assertion level allows for the grouping of ghost entities, assertion
expressions and specification aspects so they can be enabled or disabled
together using a pragma Assertion_Policy. An assertion level can depend on other
assertion levels.

.. container:: heading

   Syntax

::

   assertion_level_list ::= assertion_level[, assertion_level_list]

   assertion_levels ::= assertion_level | assertion_level_list

   pragma Assertion_Level (assertion_level[, Depends => assertion_levels]);

The assertion levels Runtime and Static are implicitly declared at the
configuration level.

.. container:: heading

   Name Resolution Rules

Assertion levels defined at the configuration level are always visible.

.. container:: heading

   Legality Rules

1. A pragma Assertion_Level shall occur as a configuration pragma.

2. The assertion level name of a pragma Assertion_Level shall not be an
   assertion aspect mark.

3. No two pragmas Assertion_Level with the same assertion level name shall occur
   in the same project, unless they have exactly the same dependencies.

.. container:: heading

   Static Semantics

4. Dependencies between assertion levels are transitive and shall not be cyclic.

.. container:: heading

   Dynamic Semantics

5. All assertion expressions associated with the Runtime assertion level shall
   always be checked.

6. All assertion expressions associated with the Static assertion level or with
   any assertion level depending on Static shall never be checked.
