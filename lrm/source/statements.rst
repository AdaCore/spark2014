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
   a ``requeue_statement``, a ``delay_statement``, an ``abort_statement``,
   or a ``code_statement``.

#. A ``compound_statement`` shall not be an ``accept_statement`` or a ``select_statement``.

A statement is only in |SPARK| if all the constructs used in the statement are
in |SPARK|.

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

|SPARK| does not support the implementation of user-defined iterator types.

Generalized Loop Iteration
~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| does not permit the use of variable iterators.

.. todo:: Need to consider further the support for iterators and whether
          the application of constant iterators could be supported.
          To be completed in Milestone.4 version of this document.

Loop Invariants, Variants and Entry Values
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

High-Level Requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language features:

    * **Requirement:** |SPARK| shall include feature/s to support proof of loop termination.

      **Rationale:** To aid detection of a serious programming error.

    * **Requirement:** |SPARK| shall include feature/s to support proof of partial correctness
      of code containing loops.

      **Rationale:** To support proof.

   * **Requirement:** Within a loop, it shall be possible to refer to the value of a given
     variable on entry to that loop.

     **Rationale:** To support proof.

#. Constraints, Consistency, Semantics, General requirements:

    * Not applicable

Language Definition
^^^^^^^^^^^^^^^^^^^

Two loop-related pragmas, ``Loop_Invariant`` and ``Loop_Variant``, and a
loop-related attribute, ``Loop_Entry`` are defined. The pragma
``Loop_Invariant`` is similar to pragma ``Assert`` except for its proof
semantics. Pragma ``Loop_Variant`` is intended for use in ensuring
termination. The ``Loop_Entry`` attribute is used to refer to the value that an
expression had upon entry to a given loop in much the same way that the ``Old``
attribute in a subprogram postcondition can be used to refer to the value an
expression had upon entry to the subprogram.

.. centered:: **Syntax**

::

      invariant_statement    ::= pragma Loop_Invariant (boolean_expression);

      loop_variant_statement ::= pragma Loop_Variant (loop_variant_item {, loop_variant_item} );

      loop_variant_item      ::= change_direction => discrete_expression

      change_direction       ::= Increases | Decreases

*To be completed in the Milestone 3 version of this document.*

.. todo::
   Provide detail on pragmas Loop_Invariant and Loop_Variant, and attribute Loop_Entry.
   To be completed in the Milestone 3 version of this document.

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

High-Level Requirements
~~~~~~~~~~~~~~~~~~~~~~~

#. Goals to be met by language feature:

    * **Requirement:** It shall be possible for users to explicitly state assumptions
      within the text of a subprogram to support the formal verification of that subprogram.

      **Rationale:** This allows facts about the domain to be used in a proof in a clean
      and explicit way.

   * **Requirement:** It shall be possible for users to assert at a given point within
     a subprogram the minimum set of facts required to complete formal verification
     of that subprogram.

     **Rationale:** This allows an explicit statement of what is necessary to complete
     formal verification and also assists the efficiency of that verification.

#. Constraints, Consistency, Semantics, General requirements:

    * Not applicable


Language Definition
~~~~~~~~~~~~~~~~~~~

.. centered:: **Syntax**

::

      assume_statement ::= pragma Assume (boolean_expression);

      cut_statement    ::= pragma Assert_And_Cut (boolean_expression);

.. centered:: **Legality Rules**

In addition to the assertion statements ``pragma Check`` and ``pragma
Assert``, a |SPARK| subprogram can contain the statement ``pragma
Assert_And_Cut`` and ``pragma Assume``, both carrying a Boolean
expression. These pragmas can occur anywhere a ``pragma Assert`` can occur.


.. centered:: **Static Semantics**

Not applicable.

.. centered:: **Dynamic Semantics**

Not applicable.

.. _assertcutinv_proof_semantics:

.. centered:: **Verification Rules**


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

