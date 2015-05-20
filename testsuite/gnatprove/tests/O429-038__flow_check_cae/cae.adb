package body CAE
  with Refined_State => (State => (Priv_Var, Body_Var))
is
   Body_Var : Integer := 3
     with Constant_After_Elaboration => False;

   package Nested is
      procedure OK;  --  OK
   end Nested;

   package body Nested is
      procedure OK is
      begin
         Var := 10;
      end OK;
   end Nested;

   procedure P is
   begin
      Var := 10;
   end P;

   procedure P2 is
   begin
      Priv_Var := 10;
   end P2;

   procedure P3 is
   begin
      Body_Var := 10;
   end P3;

   procedure P4 is
   begin
      Var := 20;
   end P4;
end CAE;
