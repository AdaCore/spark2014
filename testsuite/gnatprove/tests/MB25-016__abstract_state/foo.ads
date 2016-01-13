package Foo with
   Abstract_State    => State,
   Initializes       => State,
   Initial_Condition => F2
is
   pragma Elaborate_Body;

   function F2 return Boolean with Global => State;

private

   C : Integer with Part_Of => State;

   function F2 return Boolean is (C > 0) with Refined_Global => C;

end Foo;
