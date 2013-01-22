Statements
==========

|SPARK| restricts the use of some statements, and adds a number of pragmas which are used for
verification, particularly involving loop statements.

Simple and Compound Statements - Sequences of Statements
--------------------------------------------------------

|SPARK| restricts statements that complicate verification, and excludes statements
related to tasking and synchronization.

.. centered:: **Extended Legality Rules**

#. A ``simple_statement`` shall not be a ``goto_statement``, an ``entry_call_statement``,
   a ``requeue_statement``, an ``abort_statement``, a ``raise_statement``, a ``delay_statement``,
   or a ``code_statement``.

#. A ``compound_statement`` shall not be an ``accept_statement`` or a ``select_statement``.


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

|SPARK| does not permit the use of user-defined iterator types.

.. centered:: **Extended Legality Rules**

#. ``Ada.Iterator_Interfaces`` shall not be named in a ``with_clause``.

Generalized Loop Iteration
~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| does not permit the use of generalized loop iteration.

.. centered:: **Extended Legality Rules**

#. An ``iteration_scheme`` shall not be an ``iterator_specification``.

Loop Invariants, Variants and Entry Values
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


Two loop-related pragmas, ``Loop_Invariant`` and ``Loop_Variant``, and a
loop-related attribute, ``Loop_Entry`` are defined. The pragma
``Loop_Invariant`` is similar to pragma ``Assert`` except for its proof
semantics. Pragma ``Loop_Variant`` is intended for use in ensuring
termination. The ``Loop_Entry`` attribute is used to refer to the value that an
expression had upon entry to a given loop in much the same way that the ``Old``
attribute in a subprogram postcondition can be used to refer to the value an
expression had upon entry to the subprogram.

Pragmas ``Loop_Invariant`` and ``Loop_Variant``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

::

      invariant_statement    ::= pragma Loop_Invariant (boolean_expression);

      loop_variant_statement ::= pragma Loop_Variant (loop_variant_item {, loop_variant_item} );

      loop_variant_item ::= change_direction => discrete_expression
      change_direction  ::= Increases | Decreases

.. centered:: **Legality Rules**


The following constructs are said to be "restricted to loops":

* A ``Loop_Invariant`` pragma;
* A ``Loop_Variant`` pragma;
* A ``block_statement`` whose ``sequence_of_statements`` or ``declarative_part``
  immediately includes a construct which is restricted to loops.

A construct which is restricted to loops shall occur
immediately within either:

* the ``sequence_of_statements`` of a ``loop_statement``; or
* the ``sequence_of_statements`` or ``declarative_part`` of a
  ``block_statement``.

[Roughly speaking, a ``Loop_Invariant`` or ``Loop_Variant`` pragma
must occur immediately within a loop statement except that intervening
block statements are ignored for purposes of this rule.]

The expression of a ``loop_variant_item`` is expected to be of any
discrete type.

.. centered:: **Static Semantics**

.. todo:: Anything to say here? RCC does not know. Any comment from SB or YM? Target: D2.

.. centered:: **Dynamic Semantics**

Other than the above legality rules, pragma ``Loop_Invariant`` is equivalent to
pragma ``Assert``.

Pragma ``Loop_Variant`` is an assertion (as defined in RM
11.4.2(1.1/3)) and is governed in the same way as pragma ``Assert``
by the ``Assert`` assertion aspect. In particular, the elaboration of
a disabled ``Loop_Variant`` pragma has no effect.

The elaboration of an enabled ``Loop_Variant`` pragma begins by
evaluating the ``discrete_expressions`` in textual order.
For the first elaboration of the pragma within a given execution
of the enclosing loop statement, no further action is taken.
For subsequent elaborations of the pragma, one or more of these
expression results are each compared to their corresponding
result from the previous iteration as follows: comparisons are
performed in textual order either until unequal values are found
or until values for all expressions have been compared. In either
case, the last pair of values to be compared is then checked as
follows: if the ``change_direction`` for the associated
``loop_variant_item`` is ``Increases`` (respectively, ``Decreases``) then a
check is performed that the expression value obtained during the
current iteration is greater (respectively, less) than the value
obtained during the preceding iteration. The exception
``Assertions.Assertion_Error`` is raised if this check fails. All
comparisons and checks are performed using predefined operations.

.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

.. todo:: describe Proof Semantics of pragma Loop_Invariant. Target D2.

The pragma ``Loop_Variant`` describes a lexicographic order, which must be
proved to decrease after each iteration of the loop. This means that it is
checked, in the order of appearance in the variant list, that each component
behaves as described. If the component does indeed decrease (or increase,
depending on the chosen keyword), we stop and the variant is proved. If the
component does the opposite (decrease while it was specified to increase, and
vice versa), the variant is invalid. If the component stays the same, we move
on to the next component. If all components stay the same, the variant is not
proved.

Proving this property implies the termination of the loop.

Attribute ``Loop_Entry``
^^^^^^^^^^^^^^^^^^^^^^^^

For a prefix ``X`` that denotes an object of a nonlimited type, the
following attribute is defined

::

   X'Loop_Entry [(loop_name)]

A ``Loop_Entry`` ``attribute_reference`` "applies to a loop statement" in the
same way that an ``exit_statement`` does (see RM 5.7). For every rule
about ``exit_statements`` in the Name Resolution Rules and Legality Rules
sections of RM 5.7, a corresponding rule applies to ``Loop_Entry``
``attribute_references``.

For each ``X'Loop_Entry`` other than one occurring within a disabled
assertion expression, a constant is implicitly declared at the
beginning of the associated loop statement. The constant is of the
type of ``X`` and is initialized to the result of evaluating ``X`` (as an
expression) at the point of the constant declaration. The value of
``X'Loop_Entry`` is the value of this constant; the type of ``X'Loop_Entry``
is the type of ``X``. These implicit constant declarations occur in an
arbitrary order.

The previous paragraph notwithstanding, the implicit constant declaration
is not elaborated if the ``loop_statement`` has an ``iteration_scheme`` whose
evaluation yields the result that the ``sequence_of_statements`` of the
``loop_statement`` will not be executed (loosely speaking, if the loop completes
after zero iterations).

Note: This means that the constant is not elaborated unless the
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

This rule prevents the following example from raising ``Constraint_Error``:

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
   end;

In many cases, the language rules pertaining to the ``Loop_Entry``
attribute match those pertaining to the ``Old`` attribute (see Ada LRM 6.1.1), except
with "Loop_Entry" substituted for "Old". These include:

* prefix name resolution rules (including expected type definition)
* nominal subtype definition
* accessibility level definition
* run-time tag-value determination (in the case where ``X`` is tagged)
* interactions with abstract types
* interactions with anonymous access types
* forbidden attribute uses in the prefix of the ``attribute_reference``.

Note: The following rules are not included in the
above list; corresponding rules are instead stated explicitly below:

* the requirement that an ``Old`` ``attribute_reference`` must occur in a
  postcondition expression;
* the rule disallowing a use of an entity declared within the
  postcondition expression;
* the rule that a potentially unevaluated ``Old`` ``attribute_reference``
  shall statically denote an entity.

A ``Loop_Entry`` ``attribute_reference`` shall occur within a
``Loop_Variant`` or ``Loop_Invariant`` pragma.

The prefix of a ``Loop_Entry`` ``attribute_reference`` shall not contain a use
of an entity declared within the ``loop_statement`` but not within the prefix
itself.

The prefix of a ``Loop_Entry`` ``attribute_reference`` shall statically denote
an entity, or shall denote an ``object_renaming_declaration``, if

* the ``attribute_reference`` is potentially unevaluated; or
* the ``attribute_reference`` does not apply to the innermost
  enclosing ``loop_statement``.


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

Proof Statements
----------------

This section discusses the pragmas ``Assert_And_Cut`` and ``Assume``.

.. centered:: **Syntax**

::

      assume_statement ::= pragma Assume (boolean_expression);

      cut_statement    ::= pragma Assert_And_Cut (boolean_expression);

.. centered:: **Legality Rules**

In addition to the assertion statements ``pragma Check`` and ``pragma
Assert``, a |SPARK| subprogram can contain the statement ``pragma
Assert_And_Cut`` and ``pragma Assume``, both carrying a Boolean
expression. These pragmas can occur anywhere a ``pragma Assert`` can occur.

.. _assertcutinv_proof_semantics:

.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

For each of the pragmas ``Check``, ``Assert``, ``Assert_And_Cut``, and
``Loop_Invariant``, it must be proved that the Boolean expression is true.
This is not required for pragma ``Assume``. In addition, the pragmas
``Assert_And_Cut`` and ``Loop_Invariant`` act as a cut point: the prover is
free to forget all information about modified variables that has been
established from the statement list before the cut point. A Boolean expression
given by pragma ``Assume`` can be assumed to be true for the remainder of
subprogram.

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

