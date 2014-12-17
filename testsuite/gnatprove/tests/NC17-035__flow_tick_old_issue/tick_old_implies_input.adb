package body Tick_Old_Implies_Input is
   procedure P1
   is
   begin
      G := 1;
   end P1;

   procedure P2 (X : out Integer)
   is
   begin
      X := 1;
   end P2;

   procedure P3
   is
   begin
      G := 1;
   end P3;
end Tick_Old_Implies_Input;
