package Initial_Condition_Illegal_2
  with SPARK_Mode
is
   package State_Not_Denoted_By_Initializes
     --  TU: 3. Each variable or indirectly referenced state abstraction in an
     --  Initial_Condition aspect of a package Q which is declared immediately
     --  within the visible part of Q shall be initialized during the
     --  elaboration of Q and be denoted by a ``name`` of an
     --  ``initialization_item`` of the Initializes aspect of Q.
     with Abstract_State    => State,
          Initializes       => Var,
          Initial_Condition => F1 and Var = 0
   is
      Var : Integer := 0;

      function F1 return Boolean
        with Global => State;
   end State_Not_Denoted_By_Initializes;


   package Initial_Condition_Acts_As_Post
     --  TU: 4. An Initial_Condition aspect is a sort of postcondition for the
     --  elaboration of both the specification and body of a package. If
     --  present on a package, then its *Boolean_*\ ``expression`` defines
     --  properties (a predicate) of the state of the package which can be
     --  assumed to be true immediately following the elaboration of the
     --  package. [The expression of the Initial_Condition cannot denote a
     --  state abstraction. This means that to express properties of hidden
     --  state, functions declared in the visible part acting on the state
     --  abstractions of the package must be used.]
     with Initializes       => Var,
          Initial_Condition => Var = 0
   is
      Var : Integer := 0;

      procedure Init
        with Global => (Output => Var);
   end Initial_Condition_Acts_As_Post;
end Initial_Condition_Illegal_2;
