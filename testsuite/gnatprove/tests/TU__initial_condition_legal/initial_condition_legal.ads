package Initial_Condition_Legal
  --  TU: 5. With respect to dynamic semantics, specifying a given expression
  --  as the Initial_Condition aspect of a package is equivalent to
  --  specifying that expression as the argument of an Assert pragma
  --  occurring at the end of the (possibly implicit) statement list of
  --  the (possibly implicit) body of the package. [This equivalence
  --  includes all interactions with pragma Assertion_Policy but does not
  --  extend to matters of static semantics, such as name resolution.] An
  --  Initial_Condition expression does not cause freezing until the
  --  point where it is evaluated [, at which point everything that it
  --  might freeze has already been frozen].

  --  TU: 6. [The Initial_Condition aspect gives a proof obligation to show
  --  that the implementation of the ``package_specification`` and its body
  --  satisfy the predicate given in the Initial_Condition aspect.]
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => (State, Var),
       Initial_Condition => Var = 0 and F1
is
   Var : Integer := 0;

   function F1 return Boolean
     with Global => State;
end Initial_Condition_Legal;
