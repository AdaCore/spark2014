package Foo with
   Abstract_State    => State,
   Initializes       => State,
   Initial_Condition => F1
is


private

   C : Integer with Part_Of => State;

   function F1 return Boolean is (C > 0) with Global => C;

end Foo;
