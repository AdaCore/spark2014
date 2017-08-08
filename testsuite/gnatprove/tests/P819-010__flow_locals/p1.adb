procedure P1 (Arg : out Integer) is    --  local
   package Nested
     with Initializes => Visible_Var
   is
      Visible_Var : Integer;           --  local

      function F return Integer;
   private
      Private_Var : Integer := 5;      --  SHOULD BE local
   end Nested;

   package body Nested is
      Body_Var : Integer := 10;        --  local (SHOULD BE kept as local)

      function F return Integer is (Visible_Var + Private_Var + Body_Var);
   begin
      Visible_Var := 0;
   end Nested;

begin
   Arg := Nested.F;
end P1;
