procedure P2 (Arg : out Integer) is    --  local
   package Nested
     with Abstract_State => (Private_State, Body_State)
   is
      Visible_Var : Integer;           --  local

      function F return Integer;
   private
      Private_Var : Integer := 5 with Part_Of => Private_State;      --  SHOULD BE local
   end Nested;

   package body Nested
     with Refined_State => (Private_State => (Private_Var), Body_State => (Body_Var))
   is
      Body_Var : Integer := 10;        --  local (SHOULD BE kept as local)

      function F return Integer is (Visible_Var + Private_Var + Body_Var);
   begin
      Visible_Var := 0;
   end Nested;

begin
   Arg := Nested.F;
end P2;
