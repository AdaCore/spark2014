package Initial_Condition_Illegal_4
  --  TU: 7. Each variable or indirectly referenced state abstraction in an
  --  Initial_Condition aspect of a package Q which is declared immediately
  --  within the visible part of Q shall be initialized during the
  --  elaboration of Q and be denoted by a ``name`` of an
  --  ``initialization_item`` of the Initializes aspect of Q.
  with Initial_Condition => Var = 0
is
   Var : Integer;
   procedure P1;
end Initial_Condition_Illegal_4;
