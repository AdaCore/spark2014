with Ada.Unchecked_Deallocation;

procedure Test_Loop_Acc with SPARK_Mode is
   type My_Rec is record
      X, F : Natural;
   end record;
   type Rec_Acc is access My_Rec;
   procedure Free is new Ada.Unchecked_Deallocation (My_Rec, Rec_Acc);

   T : Rec_Acc := new My_Rec'(0,0);
begin
   for I in 1 .. 50 loop
      T.X := T.all.X + 1;
      T.all := (X => T.F, F => T.X);
      pragma Loop_Invariant (T.F = T.X + (I mod 2));
      pragma Loop_Invariant (T.X = I - T.F);
   end loop;
   Free (T);
end Test_Loop_Acc;
