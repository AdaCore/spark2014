Statements
==========

|SPARK| restricts the use of some statements, and adds a number of pragmas which
are used for verification, particularly involving loop statements.

Simple and Compound Statements - Sequences of Statements
--------------------------------------------------------

|SPARK| restricts statements that complicate verification, and excludes statements
related to tasking and synchronization.

.. centered:: **Extended Legality Rules**

#. A ``simple_statement`` shall not be a ``goto_statement``, an ``entry_call_statement``,
   a ``requeue_statement``, a ``delay_statement``, an ``abort_statement``,
   or a ``code_statement``.

#. A ``compound_statement`` shall not be an ``accept_statement`` or a ``select_statement``.

A statement is only in |SPARK| if all the constructs used in the statement are
in |SPARK|.

[A future release of |SPARK| is planned to support the Ravenscar multi-tasking
profile and then some of the tasking statements such as
``entry_call_statement``, and ``delay_statement`` will be permitted.]

Assignment Statements
---------------------

No extensions or restrictions.

If Statements
-------------

No extensions or restrictions.

Case Statements
---------------

No extensions or restrictions.

Loop Statements
---------------

User-Defined Iterator Types
~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| currently does not support the implementation of user-defined iterator
types.

.. todo:: Need to consider further the support for iterators and whether
          the application of constant iterators could be supported.

Generalized Loop Iteration
~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| currently does not support generalized loop iteration.

.. _loop_invariants:

Loop Invariants, Variants and Entry Values
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Two loop-related pragmas, Loop_Invariant and Loop_Variant, and a loop-related
attribute, Loop_Entry are defined. The pragma Loop_Invariant is used to specify
the essential non-varying properties of a loop Pragma Loop_Variant is intended
for use in ensuring termination. The Loop_Entry attribute is used to refer to
the value that an expression had upon entry to a given loop in much the same way
that the ``Old`` attribute in a subprogram postcondition can be used to refer to
the value an expression had upon entry to the subprogram.

.. centered:: **Syntax**

::

  loop_variant_parameters ::= loop_variant_item {, loop_variant_item}
  loop_variant_item       ::= change_direction => discrete_expression
  change_direction        ::= Increases | Decreases


.. centered:: **Static Semantics**

#. Pragma Loop_Invariant is like a pragma Assert except it also acts
   as a *cut point* in formal verification. A cut point means that a prover is
   free to forget all information about modified variables that has been
   established within the loop. Only the given Boolean expression is carried
   forward..

#. Pragma Loop_Variant is used to demonstrate that a loop will terminate by
   specifying expressions that will increase or decrease as the loop is
   executed.

.. centered:: **Legality Rules**

#. Loop_Invariant is just like pragma Assert with respect to syntax of its
   Boolean actual parameter, name resolution, legality rules and dynamic
   semantics, except for extra legality rules given below.

#. Loop_Variant has an expected actual parameter which is a specialization of an
   Ada expression. Otherwise, it has the same name resolution and legality
   rules as pragma Assert, except for extra legality rules given below.


#. The following constructs are said to be *restricted to loops*:

   * A Loop_Invariant pragma;

   * A Loop_Variant pragma;

   * A ``block_statement`` whose ``sequence_of_statements`` or
     ``declarative_part`` immediately includes a construct which is restricted
     to loops.

#. A construct which is restricted to loops shall occur immediately within
   either:

   * the ``sequence_of_statements`` of a ``loop_statement``; or

   * the ``sequence_of_statements`` or ``declarative_part`` of a
     ``block_statement``.

   [Roughly speaking, a Loop_Invariant or Loop_Variant pragma
   shall only occur immediately within a loop statement except that intervening
   block statements are ignored for purposes of this rule.]

#. The expression of a ``loop_variant_item`` shall be of any
   discrete type.

.. centered:: **Dynamic Semantics**

#. Other than the above legality rules, pragma Loop_Invariant is equivalent to
   pragma ``Assert``. Pragma Loop_Invariant is an assertion (as defined in Ada
   RM 11.4.2(1.1/3)) and is governed by the Loop_Invariant  assertion aspect
   [and may be used in an  Assertion_Policy pragma].

#. The elaboration of an Checked Loop_Variant pragma begins by evaluating the
   ``discrete_expressions`` in textual order. For the first elaboration of the
   pragma within a given execution of the enclosing loop statement, no further
   action is taken. For subsequent elaborations of the pragma, one or more of
   these expression results are each compared to their corresponding result from
   the previous iteration as follows: comparisons are performed in textual order
   either until unequal values are found or until values for all expressions
   have been compared. In either case, the last pair of values to be compared is
   then checked as follows: if the ``change_direction`` for the associated
   ``loop_variant_item`` is Increases (respectively, Decreases) then a check is
   performed that the expression value obtained during the current iteration is
   greater (respectively, less) than the value obtained during the preceding
   iteration. The exception Assertions.Assertion_Error is raised if this check
   fails. All comparisons and checks are performed using predefined operations.
   Pragma Loop_Variant is an assertion (as defined in Ada RM 11.4.2(1.1/3)) and
   is governed by the Loop_Variant assertion aspect [and may be used in an
   Assertion_Policy pragma].

.. centered:: **Examples**

The following example illustrates some pragmas of this section

.. code-block:: ada

   procedure P is
      type Total is range 1 .. 100;
      subtype T is Total range 1 .. 10;
      I : T := 1;
      R : Total := 100;
   begin
      while I < 10 loop
         pragma Loop_Invariant (R >= 100 - 10 * I);
         pragma Loop_Variant (Increases => I,
                              Decreases => R);
         R := R - I;
         I := I + 1;
      end loop;
   end P;

Note that in this example, the loop variant is unnecessarily complex, stating
that ``I`` increases is enough to prove termination of this simple loop.

Attribute Loop_Entry
^^^^^^^^^^^^^^^^^^^^

.. centered:: **Static Semantics**

#. For a prefix *X* that denotes an object of a nonlimited type, the
   following attribute is defined:

::
      X'Loop_Entry [(loop_name)]

#. The value of X'Loop_Entry [(loop_name] is the value of X on entry to the loop
   that is denoted by ``loop_name``.  If the optional ``loop_name`` parameter is
   not provided, the closest enclosing loop is the default.

.. centered:: **Legality Rules**

#. A Loop_Entry ``attribute_reference`` *applies to* a ``loop_statement`` in the
   same way that an ``exit_statement`` does (see Ada RM 5.7). For every rule
   about ``exit_statements`` in the Name Resolution Rules and Legality Rules
   sections of Ada RM 5.7, a corresponding rule applies to Loop_Entry
   ``attribute_references``.

#. In many cases, the language rules pertaining to the Loop_Entry
   attribute match those pertaining to the Old attribute (see Ada LRM 6.1.1),
   except with "Loop_Entry" substituted for "Old". These include:

   * prefix name resolution rules (including expected type definition)

   * nominal subtype definition

   * accessibility level definition

   * run-time tag-value determination (in the case where *X* is tagged)

   * interactions with abstract types

   * interactions with anonymous access types

   * forbidden attribute uses in the prefix of the ``attribute_reference``.

   The following rules are not included in the above list;
   corresponding rules are instead stated explicitly below:

   * the requirement that an Old ``attribute_reference`` shall only occur in a
     postcondition expression;

   * the rule disallowing a use of an entity declared within the
     postcondition expression;

   * the rule that a potentially unevaluated Old ``attribute_reference``
     shall statically denote an entity;

   * the prefix of the ``attribute_reference`` shall not contain a Loop_Entry
     ``attribute_reference.``

#. A ``Loop_Entry`` ``attribute_reference`` shall occur within a ``Loop_Variant``
   or ``Loop_Invariant`` pragma, or an ``Assert``, ``Assume`` or
   ``Assert_And_Cut`` pragma appearing in a position where a ``Loop_Invariant``
   pragma would be allowed.

  [Roughly speaking, a ``Loop_Entry`` ``attribute_reference`` can occur in an
  ``Assert``, ``Assume`` or ``Assert_And_Cut`` pragma immediately within a loop
  statement except that intervening block statements are ignored for purposes of
  this rule.]

#. The prefix of a Loop_Entry ``attribute_reference`` shall not contain a use
   of an entity declared within the ``loop_statement`` but not within the prefix
   itself.

   [This rule is to allow the use of I in the following example:

   .. code-block:: ada

     loop
        pragma Assert
          ((Var > Some_Function (Param => (for all I in T => F (I))))'Loop_Entry);

   In this example the value of the inequality ">" that would have been
   evaluated on entry to the loop is obtained even if the value of Var has since
   changed].


#. The prefix of a Loop_Entry ``attribute_reference`` shall statically denote
   an entity, or shall denote an ``object_renaming_declaration``, if

   * the ``attribute_reference`` is potentially unevaluated; or

   * the ``attribute_reference`` does not apply to the innermost
     enclosing ``loop_statement``.

   [This rule follows the corresponding Ada RM rule for 'Old
    The prefix of an Old attribute_reference that is potentially unevaluated
    shall statically denote an entity and have the same rationale. If the
    following was allowed:

   .. code-block:: ada


      procedure P (X : in out String; Idx : Positive) is
      begin
         Outer :
            loop
                if Idx in X'Range then
                   loop
                      pragma Loop_Invariant (X(Idx) > X(Idx)'Loop_Entry(Outer));

   this would introduce an exception in the case where Idx is not in X'Range.]

.. centered:: **Dynamic Semantics**

#. For each X'Loop_Entry other than one occurring within an Ignored
   assertion expression, a constant is implicitly declared at the beginning of
   the associated loop statement. The constant is of the type of X and is
   initialized to the result of evaluating X (as an expression) at the point
   of the constant declaration. The value of X'Loop_Entry is the value of this
   constant; the type of X'Loop_Entry is the type of X. These implicit
   constant declarations occur in an arbitrary order.

#. The previous paragraph notwithstanding, the implicit constant declaration
   is not elaborated if the ``loop_statement`` has an ``iteration_scheme`` whose
   evaluation yields the result that the ``sequence_of_statements`` of the
   ``loop_statement`` will not be executed (loosely speaking, if the loop
   completes after zero iterations).

   [Note: This means that the constant is not elaborated unless the
   loop body will execute (or at least begin execution) at least once.
   For example, a while loop

   .. code-block:: ada

      while <condition> do
         sequence_of_statements; -- contains Loop_Entry uses
      end loop;

   may be thought of as being transformed into

   .. code-block:: ada

      if <condition> then
         declare
         ... implicitly declared Loop_Entry constants
         begin
            loop
               sequence_of_statements;
               exit when not <condition>;
            end loop;
         end;
      end if;

   The rule also prevents the following example from raising Constraint_Error:

   .. code-block:: ada

      declare
         procedure P (X : in out String) is
         begin
            for I in X'Range loop
               pragma Loop_Invariant (X(X'First)'Loop_Entry >= X(I));
               ...; -- modify X
            end loop;
         end P;
         Length_Is_Zero : String := "";
      begin
         P (Length_Is_Zero);
      end;]


Block Statements
----------------

No extensions or restrictions.

Exit Statements
---------------

No extensions or restrictions.

Goto Statements
---------------

The goto statement is not permitted in |SPARK|.

.. _pragma_assume:

Proof Pragmas
-------------

This section discusses the pragmas Assert_And_Cut and Assume.

Two |SPARK| pragmas are defined, Assert_And_Cut and Assume.  Each has a
single Boolean parameter and may be used wherever pragma Assert is allowed.

A Boolean expression which is an actual parameter of pragma Assume
can be assumed to be True for the remainder of the subprogram. If the
Assertion_Policy is Check for pragma Assume and the Boolean expression does not
evaluate to True, the exception Assertions.Assertion_Error will be raised.
However, in proof, no verification of the expression is performed and in general
it cannot.  It has to be used with caution and is used to state axioms.


.. centered:: **Static Semantics**

#. Pragma Assert_And_Cut is the same as a pragma Assert except it also acts
   as a cut point in formal verification. The cut point means that a prover is
   free to forget all information about modified variables that has been
   established from the statement list before the cut point. Only the given
   Boolean expression is carried forward.

#. Pragma Assume is the same as a pragma Assert except that there is no
   proof obligation to prove the truth of the Boolean expression that is its
   actual parameter.  [Pragma Assume indicates to proof tools that the
   expression can be assumed to be True].

.. centered:: **Legality Rules**

#. Pragmas Assert_And_Cut and Assume have the same syntax for their Boolean
   actual parameter, name resolution rules and dynamic semantics as pragma
   Assert.

.. _assertcutinv_proof_semantics:

.. centered:: **Verification Rules**

#. The verification rules for pragma Assume are significantly different to that
   pragma Assert. [It would be difficult to overstate the importance of the
   difference.] Even though the dynamic semantics of pragma Assume and pragma
   Assert are identical, pragma Assume does not introduce a corresponding proof
   obligation. Instead the prover is given permission to assume the truth of the
   assertion, even though this has not been proven. [A single incorrect Assume
   pragma can invalidate an arbitrarily large number of proofs - the
   responsibility for ensuring correctness rests entirely upon the user.]


