package body P with Refined_State => (State => Y) is

   procedure Dummy is null;

   Z : constant Integer := X;
   --  Constant with variable input; should be listed in Refined_State
end;
