package Contract_Cases_Illegal_2
  with SPARK_Mode
is
   --  TU: 4. Upon a call of a subprogram which is subject to an enabled
   --  Contract_Cases aspect, Contract_Cases checks are
   --  performed as follows:
   --  * Immediately after the specific precondition expression is
   --    evaluated and checked (or, if that check is disabled, at the
   --    point where the check would have been performed if it were
   --    enabled), all of the ``conditions`` of the ``contract_case_list``
   --    are evaluated in textual order. A check is performed that exactly
   --    one (if no **others** ``contract_case`` is provided) or at most
   --    one (if an **others** ``contract_case`` is provided) of these
   --    ``conditions`` evaluates to True; Assertions.Assertion_Error is
   --    raised if this check fails.
   --  * Immediately after the specific postcondition expression is
   --    evaluated and checked (or, if that check is disabled, at the
   --    point where the check would have been performed if it were
   --    enabled), exactly one of the ``consequences`` is evaluated. The
   --    ``consequence`` to be evaluated is the one corresponding to the
   --    one ``condition`` whose evaluation yielded True (if such a
   --    ``condition`` exists), or to the **others** ``contract_case`` (if
   --    every ``condition``\ 's evaluation yielded False). A check
   --    is performed that the evaluation of the selected ``consequence``
   --    evaluates to True; Assertions.Assertion_Error is raised if this
   --    check fails.

   procedure Overlapping_Conditions (A, B : Integer ; C : out Integer)
     with Contract_Cases => (A > B => C = A,
                             B < A => C = B);

   procedure Incorrect_Contract (A, B : Integer ; C : out Integer)
     with Contract_Cases => (A < B => C = B,
                             B < A => C = A);
end Contract_Cases_Illegal_2;
