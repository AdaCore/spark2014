package Initial_Condition_Illegal_3
  --  TU: 4. An Initial_Condition aspect is a sort of postcondition for the
  --  elaboration of both the specification and body of a package. If
  --  present on a package, then its *Boolean_*\ ``expression`` defines
  --  properties (a predicate) of the state of the package which can be
  --  assumed to be true immediately following the elaboration of the
  --  package. [The expression of the Initial_Condition cannot denote a
  --  state abstraction. This means that to express properties of hidden
  --  state, functions declared in the visible part acting on the state
  --  abstractions of the package must be used.]
  with SPARK_Mode,
       Initializes       => Var,
       Initial_Condition => Var = 0  --  Acts as a post condition
is
   Var : Integer := 0;

   procedure Init
     with Global => (Output => Var);
end Initial_Condition_Illegal_3;
