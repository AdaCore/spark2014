package Foo with Elaborate_Body,
   Abstract_State    => State,
   Initializes       => State,
   Initial_Condition => F1 and F3 and F4 and Get_A = Get_C
is

   function F1 return Boolean with Global => State;

   --  function F2 return Boolean with Global => State;

   function F3 return Boolean with Global => State;

   function F3_Totally_Unused return Boolean with Global => State;

   function F4 return Boolean with Global => State;

   function Get_A return Integer with Global => State;

   function Get_C return Integer with Global => State;

private

   C : Integer with Part_Of => State;

   function F1 return Boolean is (C > 0);

   --  function F2 return Boolean is (C > 0) with Refined_Global => C;

   function F3 return Boolean is (C > 0);

   function F3_Totally_Unused return Boolean is (True);

   function F4 return Boolean is (C = Get_A);

   function Get_C return Integer is (C);

end Foo;
