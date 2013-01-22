Extended Legality Rules
=======================

A list of extended legality rules which determine whether the source
code is within |SPARK| by section and the reason for their exclusion:


6 Subprograms

#. A function in |SPARK| may not modify variables declared global
   to the function, but this rule is enforced during data flow analysis
   and not as an extended legality rule. As a consequence of this rule,
   the evaluation of any [SPARK] expression is side-effect free.

6.1 Subprogram Declarations

#. A function declaration in |SPARK| shall not have a
   ``parameter_specification`` of its ``function_specification``
   with a mode of **out** or **in out**. This rule also applies to
   a subprogram_body for which no explicit specification is given.

END OF FILE
