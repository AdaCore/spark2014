Statements
==========


There are no added features in this section, only restrictions.

.. todo:: I think these new pragmas are regarded as statements and
    should appear here.  The text has been copied directly from the
    initial langauge design document as prepared by Johannes. It needs
    to be tided up into LRM format

Restrictions
------------

User-defined iterator types are not in |SPARK|. An ``iterator_specification``
is not in |SPARK|.

Goto statements are not in |SPARK|.

Annotations in subprograms
--------------------------

This section discusses the pragmas ``Assert_And_Cut``, ``Loop_Invariant`` and
``Loop_Variant``.

Syntax
------

.. todo::
  We need to document the Assume pragma.

::

      cut_statement          ::= pragma Assert_And_Cut (boolean_expression);

      invariant_statement    ::= pragma Loop_Invariant(boolean_expression);

      loop_variant_statement ::= pragma Loop_Variant(variant_list);

      variant_list           ::= variant {, variant_list}
      variant_direction      ::= Increases | Decreases
      variant                ::= variant_direction => discrete_expression

Legality rules
--------------

In addition to the assertion statements ``pragma Check`` and ``pragma
Assert``, a SPARK 2014 subprogram can contain the statement ``pragma
Assert_And_Cut`` and ``pragma Assume``, both carrying a boolean
expression. This boolean property must be true at the point of the
``pragma Assert_And_Cut`` or ``pragma Assume``, as it is the case for
the other forms of assertions. These pragmas can occur anywhere a
``pragma Assert`` can occur.

Any loop may contain, at any position in the top-level statement list, a
``pragma Loop_Invariant``.

``pragma Loop_Variant`` must be the first statement of a loop and may not
appear in ``for`` loops.

.. _assertcutinv_proof_semantics:

Proof semantics
---------------

For all the pragmas ``Check``, ``Assert``, ``Assert_And_Cut`` and
``Loop_Invariant``, it must be proved that the boolean expression is true.
This is not required for pragma ``Assume``. In addition, the pragmas
``Assert_And_Cut`` and ``Loop_Invariant`` act as a cut point: the prover is
free to forget all information about modified variables that has been
established from the statement list before the cut point. A boolean expression
given by pragma ``Assume`` can be assumed to be true for the remainder of
subprogram.

The pragma ``Loop_Variant`` describes a lexicographic order, which must be
proved to decrease after each iteration of the loop. This means that it is
checked, in the order of appearance in the variant list, that each component
behaves as described. If the component does indeed decrease (or increase,
depending on the chosen keyword), we stop and the variant is proved. If the
component does the opposite (decrease while it was specified to increase, and
vice-versa), the variant is invalid. If the component stays the same, we move
on to the next component. If all components stay the same, the variant is not
proved.

Proving this property implies the termination of the loop.

Dynamic semantics
-----------------

The pragmas ``Check``, ``Assert``, ``Assume``, ``Assert_And_Cut`` and
``Loop_Invariant`` all have the same dynamic semantics, namely a
dynamic check that the boolean expression evaluates to ``True``.

Pragma ``Loop_Variant`` corresponds to a dynamic check with the following
semantics: The check is always true at the first iteration; at subsequent
iterations, the values of the discrete expressions are compared with the
values of the discrete expressions at the last iteration, and it is checked
that this indeed corresponds to a lexicographic order, as it has been
described in the :ref:`assertcutinv_proof_semantics`.

Examples
--------

.. highlight:: ada

The following example describes some pragmas of this section::

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

Discussion
----------

In GNAT, all pragmas described here are implemented using a ``pragma Check``
internally, so that the user-chosen assertion policy applies.
