procedure P2 (Arg : out Integer) is                     --  local  of P2
   package Nested
     with Abstract_State => (Private_State, Body_State) --  locals of P2
   is
      Visible_Var : Integer;                            --  local  of P2

      function F return Integer;
   private
      Private_Var : Integer := 5 with Part_Of => Private_State;
   end Nested;

   package body Nested
     with Refined_State => (Private_State => (Private_Var), Body_State => (Body_Var))
   is
      Body_Var : Integer := 10;

      function F return Integer is (Visible_Var + Private_Var + Body_Var);
   begin
      Visible_Var := 0;
   end Nested;

begin
   Arg := Nested.F;
end P2;
