Extended Legality Rules
=======================

A list of extended legality rules which determine whether the source
code is within |SPARK| by section and the reason for their exclusion:


6 Subprograms

#. A function is in |SPARK| only if it is side-effect free.

   Expressions in |SPARK| are required to be side-effect free, they
   just return a value.  A function call is an expression or a
   function may be called within an expression, so a function must be
   side-effect free.

6.1 Subprogram Declarations

#. A function declaration is only in |SPARK| if a
   ``parameter_specification`` of it's ``function_specification`` does
   not have a mode of **out** or **in out**.

   A function is not allowed to have side-effects.

#
By section

.. csv-table::
   :header:  "Section", "Legality Rules"

   "6.1", A ``parameter_specification`` of a ``function_specification`` shall not have a mode of **out** or **in out** as a function is not allowed to have side-effects.
