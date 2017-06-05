package State with
   Elaborate_Body,
   Abstract_State => State
is

   function State return Integer
     with Global => State;

   function Test (Old : Integer) return Boolean
   is (Old = State)
   with Global => State;

private

   S : Integer := 0 with Part_Of => State;

   function State return Integer is (S) with Refined_Global => S;

end State;
