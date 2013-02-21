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


.. _loop_invariants:

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

Loop_Invariant is just like pragma Assert with respect to syntax, 
name resolution, legality rules, dynamic semantics, and
assertion policy, except for an legality rule given below.

Loop_Variant has an expected actual parameter which is a specialization of an
Ada expression. In all other respects it has the same syntax, name resolution,
legality rules, and assertion policy as pragma Assert except for extra legality
rules given below.

Loop_Variant has different dynamic semantics as detailed below.

.. centered:: **Syntax**
  
#. Pragma Loop_Variant expects a list of parameters which are a specialization
   of an Ada expression as follows:
  
   ::
  
     loop_variant_parameters ::= loop_variant_item {, loop_variant_item}
     loop_variant_item       ::= change_direction => discrete_expression
     change_direction        ::= Increases | Decreases
  

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

This section discusses the pragmas Assert_And_Cut and Assume.

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

Two |SPARK| pragmas are defined, Assert_And_Cut and Assume.  Each has a 
single Boolean parameter and may be used wherever pragma Assert is allowed.

A Boolean expression which is an actual parameter ofpragma ``Assume`` 
can be assumed to be True for the remainder of the subprogram. No verification 
of the expression is performed and in general it cannot.  It has to be used with
caution and is used to state axioms.

Pragma Assert_And_Cut and Loop_Invariant are similar to an Assert statement 
except they also act as a *cut point* in formal verification.  
A cut point means that a prover is free to forget all information about 
modified variables that has been established from the statement list before 
the cut point. Only the given Boolean expression is carried forward.

Assert_And_Cut, Assume and Loop_Invariant are the same as pragma Assert with
respect to Syntax, Name Resolution, Legality Rules, Dynamic Semantics, and
assertion policy. Apart from the legality rule that restricts the use of 
Loop_Invariant to a loop (see :ref:`loop_invariants`).

.. note:: (TJJ 21-Feb-2013) Loop_Invariant is partially covered in two separate 
   sections when we re-instate and complete the loop invariant, variant, loop 
   entry value text we should rationalize the placement of the description
   of loop invariant to one section.
   
.. _assertcutinv_proof_semantics:

.. centered:: **Verification Rules**

#. Pragma Assert_And_Cut and Loop_Invariant have similar rules to pragma Assert
   and follow from the usual rule that any runtime check [in this case, the
   check is that the evaluation of the assertion expression yields True]
   introduces a corresponding proof obligation. The difference is that these two
   pragmas introduce cut points: which indicate to a prover that it may, after
   proving the truth of the assertion, dispose of certain other conclusions that
   may have been inferred at that point.
   
#. The verification rules for pragma Assume are significantly different.
   [It would be difficult to overstate the importance of the difference.]
   Even though the dynamic semantics of pragma Assume and pragma Assert are 
   identical, pragma Assume does not introduce a corresponding proof obligation.
   Instead the prover is given permission to assume the truth of the assertion,
   even though this has not been proven. [A single incorrect Assume pragma can
   invalidate an arbitrarily large number of proofs - the responsibility for
   ensuring correctness rests entirely upon the user.]

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

