with Loop_Related_Illegal_2; use Loop_Related_Illegal_2;

procedure Main is
--  TU: 10. The elaboration of a Checked Loop_Variant pragma begins by
--  evaluating the ``discrete_expressions`` in textual order. For the first
--  elaboration of the pragma within a given execution of the enclosing loop
--  statement, no further action is taken. For subsequent elaborations of the
--  pragma, one or more of these expression results are each compared to their
--  corresponding result from the previous iteration as follows: comparisons
--  are performed in textual order either until unequal values are found or
--  until values for all expressions have been compared. In either case, the
--  last pair of values to be compared is then checked as follows: if the
--  ``change_direction`` for the associated ``loop_variant_item`` is Increases
--  (respectively, Decreases) then a check is performed that the expression
--  value obtained during the current iteration is greater (respectively, less)
--  than the value obtained during the preceding iteration. The exception
--  Assertions.Assertion_Error is raised if this check fails. All comparisons
--  and checks are performed using predefined operations. Pragma Loop_Variant
--  is an assertion (as defined in Ada RM 11.4.2(1.1/3)) and is governed by the
--  Loop_Variant assertion aspect [and may be used in an Assertion_Policy
--  pragma].
begin
    Expression_Remains_The_Same (0);
end Main;
