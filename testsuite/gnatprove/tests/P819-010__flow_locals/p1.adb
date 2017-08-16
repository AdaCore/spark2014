procedure P1 (Arg : out Integer) is    --  local
   package Nested
     with Initializes => Visible_Var
   is
      Visible_Var : Integer;           --  local

      function F return Integer;
   private
      Private_Var : Integer := 5;      --  local (implicit abstract state)
   end Nested;

   package body Nested is
      Body_Var : Integer := 10;        --  local (implicit abstract state)

      function F return Integer is (Visible_Var + Private_Var + Body_Var);
   begin
      Visible_Var := 0;
   end Nested;

begin
   Arg := Nested.F;
end P1;
