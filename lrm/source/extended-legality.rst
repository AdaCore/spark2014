Extended Legality Rules
=======================

A list of extended legality rules which determine whether the source
code is within |SPARK| by section and the reason for their exclusion:


6 Subprograms

#. A function is in |SPARK| only if it is side-effect free.

   Expressions in |SPARK| are required to be side-effect free, they
   just return a value.  A function call is an expression and a
   function may be called as part of a larger expression, so a
   function must be side-effect free.

6.1 Subprogram Declarations

#. A function declaration is only in |SPARK| if a
   ``parameter_specification`` of it's ``function_specification`` does
   not have a mode of **out** or **in out**.

   A function is not allowed to have side-effects.

END OF FILE
