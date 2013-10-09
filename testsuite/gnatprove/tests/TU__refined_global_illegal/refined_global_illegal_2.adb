package body Refined_Global_Illegal_2
  with SPARK_Mode,
       Refined_State => (State => (X, Y))
is
   X, Y : Integer := 10;


   procedure P1 (Par : out Integer)
     with Refined_Global => (Input => X)
   is
   begin
      Par := X + Y;
   end P1;


   procedure P2 (Par : out Integer)
     with Refined_Global => (In_Out => X)
   is
   begin
      Par := X + Y;
      X   := X + 1;
   end P2;
end Refined_Global_Illegal_2;
